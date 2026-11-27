/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Basic
public import Zalcman.Reduction
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Phase alignment

The real-part deficit is controlled under a change of unit phase. The relevant
phase-aligned coefficient is invariant under rotations of the normalized univalent function.
-/

public section

open scoped ComplexConjugate

namespace Zalcman

private theorem conj_mul_self {u : ℂ} (hu : ‖u‖ = 1) : conj u * u = 1 := by
  rw [Complex.conj_mul', hu]
  norm_num

private theorem norm_sq_sub_le {v w : ℂ} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖v ^ 2 - w ^ 2‖ ≤ 2 * ‖v - w‖ := by
  rw [show v ^ 2 - w ^ 2 = (v + w) * (v - w) by ring, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa [hv, hw, one_add_one_eq_two] using norm_add_le v w

/-- The phase adjustment is bounded by the reference phase and the observed phase error. -/
theorem norm_one_sub_phaseAdjustment_le {α ω : ℂ} (hα : ‖α‖ = 1) (hω : ‖ω‖ = 1) :
    ‖1 - α ^ 2 * conj ω ^ 2‖ ≤ 2 * ‖1 - α‖ + 2 * ‖ω - α ^ 2‖ := by
  let γ : ℂ := α ^ 2
  have hγ : ‖γ‖ = 1 := by simp [γ, norm_pow, hα]
  have hconj : γ * (conj γ ^ 2) = conj γ := calc
    _ = (conj γ * γ) * conj γ := by ring
    _ = _ := by rw [conj_mul_self hγ, one_mul]
  have hdiff : ‖conj γ - γ * conj ω ^ 2‖ ≤ 2 * ‖ω - γ‖ := calc
    _ = ‖γ * (conj γ ^ 2 - conj ω ^ 2)‖ := by rw [mul_sub, hconj]
    _ = ‖γ * conj (γ ^ 2 - ω ^ 2)‖ := by simp only [map_sub, map_pow]
    _ = ‖γ ^ 2 - ω ^ 2‖ := by rw [norm_mul, hγ, one_mul, Complex.norm_conj]
    _ ≤ _ := by simpa only [norm_sub_rev γ ω] using norm_sq_sub_le hγ hω
  have hone : ‖1 - conj γ‖ ≤ 2 * ‖1 - α‖ := by
    have hnorm : ‖1 - conj γ‖ = ‖1 - γ‖ := calc
      _ = ‖conj (1 - γ)‖ := by rw [map_sub, map_one]
      _ = _ := Complex.norm_conj _
    rw [hnorm]
    simpa only [one_pow] using norm_sq_sub_le (v := 1) (by simp) hα
  calc
    ‖1 - α ^ 2 * conj ω ^ 2‖ = ‖(1 - conj γ) + (conj γ - γ * conj ω ^ 2)‖ := by
      rw [sub_add_sub_cancel]
    _ ≤ ‖1 - conj γ‖ + ‖conj γ - γ * conj ω ^ 2‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hone hdiff

/-- A change of phase costs a squared phase discrepancy in the real-part deficit. -/
theorem phase_deficit_le_of_change {m : ℝ} {a α ω : ℂ} (hm : 0 < m) (ha : ‖a‖ ≤ m)
    (hα : ‖α‖ = 1) (hω : ‖ω‖ = 1) :
    m - (conj ω ^ 2 * a).re ≤
      2 * (m - (conj (α ^ 2) * a).re) + m * ‖1 - α ^ 2 * conj ω ^ 2‖ ^ 2 := by
  let z := conj (α ^ 2) * a / (m : ℂ)
  let u := α ^ 2 * conj ω ^ 2
  have hz : ‖z‖ ≤ 1 := by
    simp only [z, norm_div, norm_mul, Complex.norm_conj, norm_pow, hα, one_pow, one_mul,
      Complex.norm_of_nonneg hm.le]
    exact (div_le_one hm).mpr ha
  have hu : ‖u‖ = 1 := by simp [u, norm_pow, hα, hω]
  have hzre : z.re = (conj (α ^ 2) * a).re / m := Complex.div_ofReal_re _ _
  have hα' : conj (α ^ 2) * α ^ 2 = 1 := conj_mul_self (by simp [norm_pow, hα])
  have hproduct : z * u = conj ω ^ 2 * a / (m : ℂ) := calc
    _ = (conj (α ^ 2) * α ^ 2) * (conj ω ^ 2 * a / (m : ℂ)) := by dsimp only [z, u]; ring
    _ = _ := by rw [hα', one_mul]
  have huSq : 2 * (1 - u.re) = ‖1 - u‖ ^ 2 := by
    have h : ‖u‖ ^ 2 = 1 := by simp [hu]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im] at h ⊢
    nlinarith only [h]
  have h := mul_le_mul_of_nonneg_left (unit_phase_deficit hz hu) hm.le
  rw [hproduct, Complex.div_ofReal_re, hzre] at h
  have hlo (x : ℝ) : m * (1 - x / m) = m - x := by field_simp
  have hhi (x : ℝ) : m * (2 * (1 - x / m)) = 2 * (m - x) := by
    linear_combination 2 * hlo x
  simpa only [hlo, mul_add, hhi, huSq] using h

/-- Squared discrepancy of the two prefix phases controls the phase-change term. -/
theorem norm_one_sub_phaseAdjustment_sq_le {α ω : ℂ} (hα : ‖α‖ = 1) (hω : ‖ω‖ = 1) :
    ‖1 - α ^ 2 * conj ω ^ 2‖ ^ 2 ≤ 8 * (‖1 - α‖ ^ 2 + ‖ω - α ^ 2‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_one_sub_phaseAdjustment_le hα hω) 2
  nlinarith only [h, sq_nonneg (‖1 - α‖ - ‖ω - α ^ 2‖)]

/-- The target phase-aligned coefficient at `2 * n - 1` is invariant under rotation. -/
theorem phaseAligned_coeff_rotate (f : ℂ → ℂ) {lam : ℂ} (hlam : ‖lam‖ = 1) {n : ℕ} (hn : 1 ≤ n) :
    conj (coeff (rotate lam f) n / (‖coeff (rotate lam f) n‖ : ℂ)) ^ 2 *
      coeff (rotate lam f) (2 * n - 1) =
    conj (coeff f n / (‖coeff f n‖ : ℂ)) ^ 2 * coeff f (2 * n - 1) := by
  rw [coeff_rotate f hlam hn, coeff_rotate f hlam (show 1 ≤ 2 * n - 1 by omega)]
  simp only [norm_mul, norm_pow, hlam, one_pow, one_mul]
  let u := lam ^ (n - 1)
  have hu : ‖u‖ = 1 := by simp [u, norm_pow, hlam]
  have hunit : conj u * u = 1 := conj_mul_self hu
  rw [show 2 * n - 1 - 1 = (n - 1) * 2 by omega, pow_mul]
  change conj (u * coeff f n / (‖coeff f n‖ : ℂ)) ^ 2 *
    (u ^ 2 * coeff f (2 * n - 1)) = _
  rw [mul_div_assoc, map_mul]
  calc
    _ = (conj u * u) ^ 2 *
        (conj (coeff f n / (‖coeff f n‖ : ℂ)) ^ 2 * coeff f (2 * n - 1)) := by ring
    _ = _ := by rw [hunit, one_pow, one_mul]

end Zalcman
