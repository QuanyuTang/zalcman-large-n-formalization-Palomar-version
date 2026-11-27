/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CoefficientBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The quadratic low-degree inequality from Milin positivity
-/

public section

namespace Zalcman.MilinCoefficients

open Finset

/-- The second and third Milin sums imply the sharp quadratic real-part bound
on the second and third coefficients. -/
theorem squareCoeff_two_im_sq_le_three_sub_squareCoeff_three_re (d : MilinCoefficients)
    (h₂ : 0 ≤ d.milinSum 2) (h₃ : 0 ≤ d.milinSum 3) :
    (d.squareCoeff 2).im ^ 2 ≤ 3 - (d.squareCoeff 3).re := by
  let a := 1 - ‖d.t 1‖ ^ 2
  have ha : 0 ≤ a := by
    dsimp [a]
    norm_num [milinSum, sum_range_succ] at h₂ ⊢
    exact h₂
  have hnorm : ‖d.t 2‖ ^ 2 ≤ 1 + 4 * a := by
    dsimp [a]
    norm_num [milinSum, sum_range_succ] at h₃
    linarith only [h₃]
  have hreal : (d.t 2).re ≤ 1 + 2 * a :=
    (Complex.re_le_norm _).trans
      (le_of_sq_le_sq (hnorm.trans (by nlinarith only [sq_nonneg a])) (by linarith only [ha]))
  have hrec : d.t 2 + (d.t 1) ^ 2 = 2 * d.c 2 := by
    have h := d.recursion 2
    norm_num [sum_range_succ, d.c_zero, ← d.t_one_eq_c_one] at h
    linear_combination h
  have hcoeff : d.squareCoeff 3 = 2 * d.c 2 + (d.t 1) ^ 2 := by
    norm_num [squareCoeff, sum_range_succ, d.c_zero, ← d.t_one_eq_c_one]
    <;> ring
  have hrel : d.t 2 = d.squareCoeff 3 - 2 * (d.t 1) ^ 2 := by
    rw [hcoeff, ← hrec]
    ring
  rw [hrel] at hreal
  dsimp [a] at hreal
  simp only [pow_two, Complex.sub_re, Complex.mul_re, Complex.mul_im,
    Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero, zero_add, add_zero, sub_zero,
    Complex.sq_norm, Complex.normSq_apply] at hreal
  have hnorm_first : ‖d.t 1‖ ^ 2 = (d.t 1).re ^ 2 + (d.t 1).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [d.squareCoeff_two]
  simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
  nlinarith only [hreal, hnorm_first]

end Zalcman.MilinCoefficients

namespace Zalcman

/-- The sharp quadratic inequality for Taylor coefficients under Milin positivity. -/
theorem im_coeff_two_sq_le_three_sub_re_coeff_three_of_milin {f : ℂ → ℂ}
    (hf : NormalizedUnivalent f) (h₂ : 0 ≤ (milinCoefficients hf).milinSum 2)
    (h₃ : 0 ≤ (milinCoefficients hf).milinSum 3) :
    (coeff f 2).im ^ 2 ≤ 3 - (coeff f 3).re := by
  simpa only [milinCoefficients_squareCoeff hf] using
    (milinCoefficients hf).squareCoeff_two_im_sq_le_three_sub_squareCoeff_three_re h₂ h₃

end Zalcman
