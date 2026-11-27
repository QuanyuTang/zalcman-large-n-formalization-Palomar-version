/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Milin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# From a nearly constant coefficient block to its unit reference phase

The block mean minimizes squared distance. The linear mean-error terms vanish
in the reflected convolution, which gives a linear bound for the phase error.
-/

public section

namespace Zalcman.MilinCoefficients

open Finset
open scoped ComplexConjugate

private theorem complex_norm_sub_sq (z a : ℂ) :
    ‖z - a‖ ^ 2 = ‖z‖ ^ 2 + ‖a‖ ^ 2 - 2 * (z * conj a).re := by
  rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]

private theorem sum_norm_sub_sq (z : ℕ → ℂ) (n : ℕ) (a : ℂ) :
    (∑ j ∈ range n, ‖z j - a‖ ^ 2) =
      (∑ j ∈ range n, ‖z j‖ ^ 2) + (n : ℝ) * ‖a‖ ^ 2 -
        2 * ((∑ j ∈ range n, z j) * conj a).re := by
  simp only [complex_norm_sub_sq,
    sum_add_distrib, sum_sub_distrib, ← mul_sum, ← Complex.re_sum, ← sum_mul,
    sum_const, card_range, nsmul_eq_mul]

private theorem norm_reflected_prod_sum_le (z : ℕ → ℂ) (n : ℕ) :
    ‖∑ j ∈ range n, z j * z (n - 1 - j)‖ ≤ ∑ j ∈ range n, ‖z j‖ ^ 2 := by
  calc
    _ ≤ ∑ j ∈ range n, ‖z j * z (n - 1 - j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range n, (‖z j‖ ^ 2 + ‖z (n - 1 - j)‖ ^ 2) / 2 := by
      apply sum_le_sum
      intro j _
      rw [norm_mul]
      nlinarith only [sq_nonneg (‖z j‖ - ‖z (n - 1 - j)‖)]
    _ = _ := by
      simp only [div_eq_mul_inv, ← sum_mul, sum_add_distrib,
        sum_range_reflect (fun i => ‖z i‖ ^ 2) n]
      ring

/-- When the block is already close to a constant, it is close to a unit constant whose square
is close to the phase of its reflected convolution. -/
theorem exists_unit_const_of_near_const (d : MilinCoefficients) {n : ℕ} (hn : 0 < n)
    (hMass : d.partialMass n ≤ n) {b : ℂ} {E : ℝ}
    (hE : (∑ j ∈ range n, ‖d.c j - b‖ ^ 2) ≤ E)
    (hNear : (n : ℝ) - ‖d.squareCoeff n‖ + E < n)
    (hDhalf : (n : ℝ) - ‖d.squareCoeff n‖ ≤ (n : ℝ) / 2) :
    ∃ α : ℂ, ‖α‖ = 1 ∧
      (∑ j ∈ range n, ‖d.c j - α‖ ^ 2) ≤ (n : ℝ) - ‖d.squareCoeff n‖ + 2 * E ∧
      ‖d.squareCoeff n / (‖d.squareCoeff n‖ : ℂ) - α ^ 2‖ ≤
        4 * ((n : ℝ) - ‖d.squareCoeff n‖ + E) / (n : ℝ) := by
  let q := d.squareCoeff n
  let D : ℝ := n - ‖q‖
  let mean : ℂ := (∑ j ∈ range n, d.c j) / (n : ℂ)
  let S : ℝ := ∑ j ∈ range n, ‖d.c j - mean‖ ^ 2
  change D + E < n at hNear
  change D ≤ (n : ℝ) / 2 at hDhalf
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hmean : (∑ j ∈ range n, d.c j) = (n : ℂ) * mean := by
    dsimp only [mean]
    rw [mul_div_cancel₀ _ hnC]
  have hMassMean : d.partialMass n = S + (n : ℝ) * ‖mean‖ ^ 2 := by
    dsimp only [S, partialMass]
    rw [sum_norm_sub_sq, hmean, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.ofReal_re]
    ring
  have hShift (a : ℂ) : (∑ j ∈ range n, ‖d.c j - a‖ ^ 2) = S + (n : ℝ) * ‖mean - a‖ ^ 2 := by
    rw [sum_norm_sub_sq, ← partialMass, hMassMean, hmean, mul_assoc,
      ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    rw [complex_norm_sub_sq mean a]
    ring
  have hS₀ : 0 ≤ S := sum_nonneg (fun _ _ => sq_nonneg _)
  have hS : S ≤ E := by
    rw [hShift] at hE
    linarith only [hE, mul_nonneg hnR.le (sq_nonneg ‖mean - b‖)]
  have hD₀ : 0 ≤ D := sub_nonneg.mpr ((d.norm_squareCoeff_le_partialMass n).trans hMass)
  have hBsq : ‖mean‖ ^ 2 ≤ 1 := by
    have hh : (n : ℝ) * ‖mean‖ ^ 2 ≤ (n : ℝ) * 1 := by linarith only [hMassMean, hMass, hS₀]
    exact (mul_le_mul_iff_of_pos_left hnR).mp hh
  have hB : ‖mean‖ ≤ 1 := (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp (by
    simpa only [one_pow] using hBsq)
  have hgap : (n : ℝ) * (1 - ‖mean‖ ^ 2) ≤ D + E := by
    linarith only [hMassMean, d.norm_squareCoeff_le_partialMass n, hS]
  have hBpos : 0 < ‖mean‖ := by
    by_contra! h
    have hz : ‖mean‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [hz] at hgap
    norm_num at hgap
    linarith only [hgap, hNear]
  have hBne : ((‖mean‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hBpos.ne'
  let α := mean / (‖mean‖ : ℂ)
  have hα : ‖α‖ = 1 := by
    dsimp only [α]
    rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self hBpos.ne']
  have hrep : mean = (‖mean‖ : ℂ) * α := (mul_div_cancel₀ _ hBne).symm
  have hdiff : ‖mean - α‖ = 1 - ‖mean‖ := by
    have hEq : mean - α = ((‖mean‖ - 1 : ℝ) : ℂ) * α := calc
      _ = (‖mean‖ : ℂ) * α - α := congrArg (fun z : ℂ => z - α) hrep
      _ = _ := by rw [Complex.ofReal_sub, sub_mul, Complex.ofReal_one, one_mul]
    rw [hEq,
      norm_mul, hα, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hB)]
    ring
  have hphaseE : (∑ j ∈ range n, ‖d.c j - α‖ ^ 2) ≤ D + 2 * E := by
    rw [hShift, hdiff]
    have hh : (1 - ‖mean‖) ^ 2 ≤ 1 - ‖mean‖ ^ 2 := by
      nlinarith only [mul_nonneg (norm_nonneg mean) (sub_nonneg.mpr hB)]
    linarith only [mul_le_mul_of_nonneg_left hh hnR.le, hgap, hS]
  let X (j : ℕ) := d.c j - mean
  have hX : ∑ j ∈ range n, X j = 0 := by
    simp only [X, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, hmean, sub_self]
  have hXconv : q - (n : ℂ) * mean ^ 2 = ∑ j ∈ range n, X j * X (n - 1 - j) := by
    have hX' : ∑ j ∈ range n, X (n - 1 - j) = 0 := by rw [sum_range_reflect, hX]
    have hc (j : ℕ) : d.c j = X j + mean := by simp [X]
    change d.squareCoeff n - _ = _
    simp only [squareCoeff, hc, mul_add, add_mul, sum_add_distrib, ← sum_mul, ← mul_sum,
      hX, hX', zero_mul, mul_zero, add_zero, zero_add, sum_const, card_range, nsmul_eq_mul, pow_two]
    ring
  have hConv : ‖q - (n : ℂ) * mean ^ 2‖ ≤ E := by
    rw [hXconv]
    exact (norm_reflected_prod_sum_le X n).trans hS
  have hβ₂ : ‖mean ^ 2 - α ^ 2‖ = 1 - ‖mean‖ ^ 2 := by
    have hEq : mean ^ 2 - α ^ 2 = ((‖mean‖ ^ 2 - 1 : ℝ) : ℂ) * α ^ 2 := calc
      _ = ((‖mean‖ : ℂ) * α) ^ 2 - α ^ 2 := congrArg (fun z : ℂ => z ^ 2 - α ^ 2) hrep
      _ = _ := by rw [mul_pow, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one, sub_mul, one_mul]
    rw [hEq,
      norm_mul, norm_pow, hα, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hBsq)]
    ring
  have hqphase : ‖q - (n : ℂ) * α ^ 2‖ ≤ D + 2 * E := calc
    _ = ‖(q - (n : ℂ) * mean ^ 2) + (n : ℂ) * (mean ^ 2 - α ^ 2)‖ := by congr 1; ring
    _ ≤ ‖q - (n : ℂ) * mean ^ 2‖ + (n : ℝ) * (1 - ‖mean‖ ^ 2) := by
      have h := norm_add_le (q - (n : ℂ) * mean ^ 2) ((n : ℂ) * (mean ^ 2 - α ^ 2))
      rw [Complex.norm_mul, Complex.norm_natCast, hβ₂] at h
      exact h
    _ ≤ _ := by linarith only [hConv, hgap]
  have hq₀ : 0 < ‖q‖ := by dsimp only [D] at hDhalf; linarith
  have hqC : ((‖q‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq₀.ne'
  have hnum : ‖q - (‖q‖ : ℂ) * α ^ 2‖ ≤ 2 * (D + E) := calc
    _ = ‖(q - (n : ℂ) * α ^ 2) + (D : ℂ) * α ^ 2‖ := by
      congr 1
      simp only [D, Complex.ofReal_sub, Complex.ofReal_natCast]
      ring
    _ ≤ ‖q - (n : ℂ) * α ^ 2‖ + D := by
      have h := norm_add_le (q - (n : ℂ) * α ^ 2) ((D : ℂ) * α ^ 2)
      rw [Complex.norm_mul, norm_pow, hα, one_pow, mul_one, Complex.norm_of_nonneg hD₀] at h
      exact h
    _ ≤ _ := by linarith only [hqphase]
  refine ⟨α, hα, hphaseE, ?_⟩
  change ‖q / (‖q‖ : ℂ) - α ^ 2‖ ≤ _
  rw [show q / (‖q‖ : ℂ) - α ^ 2 = (q - (‖q‖ : ℂ) * α ^ 2) / (‖q‖ : ℂ) by
    field_simp [hqC] <;> ring, norm_div, Complex.norm_of_nonneg (norm_nonneg _)]
  refine ((div_le_div_of_nonneg_right hnum hq₀.le)).trans ?_
  apply (div_le_div_iff₀ hq₀ hnR).mpr
  nlinarith only [mul_nonneg (add_nonneg hD₀ (hS₀.trans hS))
    (show 0 ≤ 2 * ‖q‖ - n by dsimp only [D] at hDhalf; linarith)]

end Zalcman.MilinCoefficients
