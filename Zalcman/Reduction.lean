/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reduction of the Zalcman bound to quantitative phase transfer

The final argument uses the Bieberbach coefficient bound and its equality case together
with an estimate controlling the phase of the coefficient at index `2 * n - 1` in terms
of the magnitude deficit at index `n`. This file proves the algebraic reduction and the
uniform choice of threshold, independently of how the coefficient estimates are obtained.
-/

public section

open Filter
open scoped ComplexConjugate

namespace Zalcman

/-- Multiplication by a unit complex number increases the real-part deficit by at most
twice the sum of the two original deficits. -/
theorem unit_phase_deficit {z u : ℂ} (hz : ‖z‖ ≤ 1) (hu : ‖u‖ = 1) :
    1 - (z * u).re ≤ 2 * (1 - z.re) + 2 * (1 - u.re) := by
  have hzSq : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have hzSq : ‖z‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz _
    rw [Complex.sq_norm, Complex.normSq_apply] at hzSq
    nlinarith only [hzSq]
  have huSq : u.re ^ 2 + u.im ^ 2 = 1 := by
    have huSq : ‖u‖ ^ 2 = 1 := by simp [hu]
    rw [Complex.sq_norm, Complex.normSq_apply] at huSq
    nlinarith only [huSq]
  rw [Complex.mul_re]
  nlinarith only [hzSq, huSq, sq_nonneg (z.re + u.re - 2), sq_nonneg (z.im - u.im)]

private theorem norm_sub_real_sq (x : ℝ) (z : ℂ) :
    ‖(x : ℂ) - z‖ ^ 2 = x ^ 2 - 2 * x * z.re + ‖z‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Any coefficient pair that reaches the conjectured bound must have first coefficient
magnitude close to `n`, and its phase-aligned second coefficient has deficit at least
`n * (n - ‖a‖) / 4`. -/
theorem candidate_deficit {n : ℝ} {a c : ℂ} (hn : 8 ≤ n) (ha : ‖a‖ ≤ n)
    (hc : ‖c‖ ≤ 2 * n - 1) (h : n ^ 2 - (2 * n - 1) ≤ ‖a ^ 2 - c‖) :
    0 < ‖a‖ ∧ 0 ≤ n - ‖a‖ ∧ n - ‖a‖ ≤ 3 ∧
      n * (n - ‖a‖) / 4 ≤ (2 * n - 1) - (conj (a / (‖a‖ : ℂ)) ^ 2 * c).re := by
  let m : ℝ := 2 * n - 1
  let A : ℝ := ‖a‖
  have hA0 : 0 ≤ A := norm_nonneg _
  have hA2 : n ^ 2 - 2 * m ≤ A ^ 2 := by
    have htri := norm_sub_le (a ^ 2) c
    rw [norm_pow] at htri
    linarith
  have hApos : 0 < A := by
    by_contra! hA
    have hzero : A = 0 := le_antisymm hA hA0
    rw [hzero] at hA2
    dsimp only [m] at hA2
    nlinarith only [hA2, hn, sq_nonneg (n - 8)]
  have hA3 : n - A ≤ 3 := by
    have hsq : (n - 3) ^ 2 ≤ A ^ 2 := by
      dsimp only [m] at hA2
      nlinarith only [hA2, hn]
    by_contra! hlt
    have hlt' : A < n - 3 := by linarith
    exact (not_lt_of_ge hsq) (pow_lt_pow_left₀ hlt' hA0 (by decide : (2 : ℕ) ≠ 0))
  let ω : ℂ := a / (A : ℂ)
  let b : ℂ := conj ω ^ 2 * c
  have hAne : (A : ℂ) ≠ 0 := by exact_mod_cast hApos.ne'
  have hω : ‖ω‖ = 1 := by
    dsimp only [ω]
    rw [norm_div, Complex.norm_of_nonneg hA0, div_self hApos.ne']
  have hrot : conj ω * ω = 1 := by rw [Complex.conj_mul', hω]; norm_num
  have haω : a = (A : ℂ) * ω := by
    rw [mul_comm, div_mul_cancel₀ _ hAne]
  have hrotA : conj ω ^ 2 * a ^ 2 = (A : ℂ) ^ 2 := calc
    _ = (A : ℂ) ^ 2 * (conj ω * ω) ^ 2 := by rw [haω]; ring
    _ = _ := by rw [hrot]; ring
  have hbc : ‖b‖ = ‖c‖ := by simp [b, norm_pow, hω]
  have hb : ‖b‖ ≤ m := hbc.trans_le hc
  have hnorm : ‖a ^ 2 - c‖ = ‖((A ^ 2 : ℝ) : ℂ) - b‖ := by
    rw [Complex.ofReal_pow, ← hrotA]
    change ‖a ^ 2 - c‖ = ‖conj ω ^ 2 * a ^ 2 - conj ω ^ 2 * c‖
    rw [← mul_sub, norm_mul, norm_pow, Complex.norm_conj, hω]
    ring
  have hleft : 0 ≤ n ^ 2 - m := by
    dsimp only [m]
    nlinarith only [sq_nonneg (n - 1)]
  have hsq := pow_le_pow_left₀ hleft h 2
  rw [hnorm, norm_sub_real_sq] at hsq
  have hbSq : ‖b‖ ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hfactor : (n ^ 2 - A ^ 2) * (n ^ 2 + A ^ 2 - 2 * m) ≤
      2 * A ^ 2 * (m - b.re) := by
    nlinarith only [hsq, hbSq]
  have hD : 0 ≤ n - A := sub_nonneg.mpr ha
  have hfactor₁ : n * (n - A) ≤ n ^ 2 - A ^ 2 := calc
    _ ≤ (n + A) * (n - A) := by gcongr; linarith
    _ = _ := by ring
  have hfactor₂ : n ^ 2 / 2 ≤ n ^ 2 + A ^ 2 - 2 * m := by
    dsimp only [m] at hA2 ⊢
    nlinarith only [hA2, hn, sq_nonneg (n - 8)]
  have hgap : 0 ≤ m - b.re := sub_nonneg.mpr ((Complex.re_le_norm _).trans hb)
  have hAupper : A ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ hA0 ha 2
  have hquant : n * (n - A) * (n ^ 2 / 2) ≤ 2 * n ^ 2 * (m - b.re) := calc
    _ ≤ (n ^ 2 - A ^ 2) * (n ^ 2 + A ^ 2 - 2 * m) :=
      mul_le_mul hfactor₁ hfactor₂ (by positivity) (le_trans (by positivity) hfactor₁)
    _ ≤ 2 * A ^ 2 * (m - b.re) := hfactor
    _ ≤ _ := by gcongr
  refine ⟨hApos, hD, hA3, ?_⟩
  change n * (n - A) / 4 ≤ m - b.re
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * n ^ 2 by positivity)).mp
  nlinarith only [hquant]

private theorem exists_phase_threshold {C : ℝ} (hC : 0 < C) :
    ∃ L : ℕ, ∀ n : ℕ, L ≤ n →
      C * Real.log (n : ℝ) ^ 2 ≤ Real.sqrt (n : ℝ) / 8 := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) 2 (by norm_num)).def
    (show 0 < 1 / (8 * C) by positivity)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hsmall
  obtain ⟨L, hL⟩ := exists_nat_ge x₀
  refine ⟨L, fun n hn ↦ ?_⟩
  have h := hx₀ (n : ℝ) (hL.trans (by exact_mod_cast hn))
  have hpow (x : ℝ) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by exact Real.rpow_two x
  rw [hpow, ← Real.sqrt_eq_rpow, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (Real.sqrt_nonneg _)] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 8 * C)] at h
  nlinarith only [h]

/-- The coefficients of a Koebe rotation attain the Zalcman bound at every positive index. -/
theorem koebe_pair_norm {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖((n : ℂ) * ζ ^ (n - 1)) ^ 2 -
      (↑(2 * n - 1 : ℕ) : ℂ) * ζ ^ (2 * n - 1 - 1)‖ = ((n : ℝ) - 1) ^ 2 := by
  have hexp : 2 * n - 1 - 1 = (n - 1) * 2 := by omega
  have hcast : ((2 * n - 1 : ℕ) : ℂ) = 2 * (n : ℂ) - 1 := by
    simp only [Nat.cast_sub (by omega : 1 ≤ 2 * n), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [hexp, pow_mul, mul_pow, hcast, ← sub_mul, norm_mul, norm_pow, norm_pow, hζ]
  have hscalar : (n : ℂ) ^ 2 - (2 * (n : ℂ) - 1) =
      Complex.ofReal (((n : ℝ) - 1) ^ 2) := by
    simp only [Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one]
    ring
  rw [hscalar, Complex.norm_of_nonneg (sq_nonneg _)]
  simp

/-- Given the coefficient bound, its rigidity statement, and quantitative phase transfer,
the Zalcman inequality with Koebe rigidity holds above a single threshold. -/
theorem eventually_zalcman_of_phase_transfer {F : Type*} (a : F → ℕ → ℂ)
    (isRotation : F → Prop)
    (coefficient_bound : ∀ f j, ‖a f j‖ ≤ j)
    (coefficient_rigidity : ∀ f j, 2 ≤ j → ‖a f j‖ = j → isRotation f)
    (rotation_coefficients : ∀ f, isRotation f →
      ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ j : ℕ, 1 ≤ j → a f j = j * ζ ^ (j - 1))
    {C : ℝ} {N₀ : ℕ} (hC : 0 < C)
    (phase_transfer : ∀ f (n : ℕ), N₀ ≤ n → (n : ℝ) - ‖a f n‖ ≤ 3 →
      (↑(2 * n - 1 : ℕ) : ℝ) - (conj (a f n / (‖a f n‖ : ℂ)) ^ 2 *
        a f (2 * n - 1)).re ≤ C * ((n : ℝ) - ‖a f n‖) * Real.sqrt (n : ℝ) *
          Real.log (n : ℝ) ^ 2) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ f (n : ℕ), N ≤ n →
      ‖a f n ^ 2 - a f (2 * n - 1)‖ ≤ ((n : ℝ) - 1) ^ 2 ∧
      (‖a f n ^ 2 - a f (2 * n - 1)‖ = ((n : ℝ) - 1) ^ 2 ↔ isRotation f) := by
  obtain ⟨L, hL⟩ := exists_phase_threshold hC
  refine ⟨max 8 (max N₀ L), by omega, fun f n hn ↦ ?_⟩
  have hn8 : 8 ≤ n := by omega
  have hn8' : (8 : ℝ) ≤ n := by exact_mod_cast hn8
  have hm : (↑(2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    simp only [Nat.cast_sub (by omega : 1 ≤ 2 * n), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  let D : ℝ := n - ‖a f n‖
  have is_candidate (h : ((n : ℝ) - 1) ^ 2 ≤ ‖a f n ^ 2 - a f (2 * n - 1)‖) :
      isRotation f := by
    have hc := coefficient_bound f (2 * n - 1)
    rw [hm] at hc
    have hcand : (n : ℝ) ^ 2 - (2 * n - 1) ≤ ‖a f n ^ 2 - a f (2 * n - 1)‖ := by
      nlinarith only [h]
    obtain ⟨_, hD0, hD3, hlow⟩ := candidate_deficit hn8' (coefficient_bound f n) hc hcand
    change 0 ≤ D at hD0
    have hhigh := phase_transfer f n (by omega) hD3
    rw [← hm] at hlow
    have hupper : C * D * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) * D / 8 := calc
      _ = (D * Real.sqrt (n : ℝ)) * (C * Real.log (n : ℝ) ^ 2) := by ring
      _ ≤ (D * Real.sqrt (n : ℝ)) * (Real.sqrt (n : ℝ) / 8) :=
        mul_le_mul_of_nonneg_left (hL n (by omega)) (by positivity)
      _ = _ := by
        rw [show D * Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) / 8) =
          D * (Real.sqrt (n : ℝ)) ^ 2 / 8 by ring, Real.sq_sqrt (by positivity)]
        ring
    have hDle : (n : ℝ) * D / 4 ≤ (n : ℝ) * D / 8 := hlow.trans (hhigh.trans hupper)
    have hnD : (n : ℝ) * D ≤ 0 := by linarith only [hDle]
    have hn0 : 0 < (n : ℝ) := by linarith
    have hDz : D = 0 := le_antisymm (nonpos_of_mul_nonpos_right hnD hn0) hD0
    apply coefficient_rigidity f n (by omega)
    exact sub_eq_zero.mp hDz |>.symm
  have is_eq (h : isRotation f) :
      ‖a f n ^ 2 - a f (2 * n - 1)‖ = ((n : ℝ) - 1) ^ 2 := by
    obtain ⟨ζ, hζ, hcoeff⟩ := rotation_coefficients f h
    rw [hcoeff n (by omega), hcoeff (2 * n - 1) (by omega)]
    exact koebe_pair_norm (by omega) hζ
  refine ⟨?_, ⟨fun h ↦ is_candidate h.ge, is_eq⟩⟩
  by_contra! h
  exact (is_eq (is_candidate h.le)).not_gt h

end Zalcman
