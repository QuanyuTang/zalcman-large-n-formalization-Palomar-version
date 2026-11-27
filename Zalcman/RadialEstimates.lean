/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebraic estimates for the hyperbolic translates

The differential identities for the translated coefficients reduce parts of
the one-sided radial estimate and the diameter estimate to inequalities in
the second, third, and fourth coefficients at one point.
-/

public section

namespace Zalcman

private lemma re_sq_add_im_sq_le {z : ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) :
    z.re ^ 2 + z.im ^ 2 ≤ r ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) hz 2
  rw [Complex.sq_norm, Complex.normSq_apply] at h
  nlinarith only [h]

/-- The differential expression for `2 - Re q` is bounded by eight times that deficit. -/
theorem real_second_deficit_derivative_le {q a : ℂ} (hq : ‖q‖ ≤ 2)
    (hqa : ‖q ^ 2 - a‖ ≤ 1) :
    -(3 * a - 2 * q ^ 2 - 1).re ≤ 8 * (2 - q.re) := by
  have h₁ := re_sq_add_im_sq_le hq
  have h₂ := (Complex.re_le_norm (q ^ 2 - a)).trans hqa
  simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.one_re, zero_mul, sub_zero] at h₂ ⊢
  nlinarith only [h₁, h₂, sq_nonneg (q.re - 2)]

/-- Two-sided control of the amplitude deficit from the low-degree coefficient inequality. -/
theorem amplitude_deficit_bounds {q : ℂ} {d : ℝ} (h : q.im ^ 2 ≤ d) :
    2 * d ≤ 6 * d - 4 * q.im ^ 2 ∧ 6 * d - 4 * q.im ^ 2 ≤ 6 * d := by
  constructor <;> linarith [sq_nonneg q.im]

/-- The differential expression for the third real-part deficit is bounded by
`(4 * C + 11)` times the deficit when the two low-degree estimates hold with constant `C`. -/
theorem real_third_deficit_derivative_abs_le {q a b : ℂ} {C : ℝ}
    (hq : ‖q‖ ≤ 2) (ha : ‖a‖ ≤ 3) (hqi : q.im ^ 2 ≤ 3 - a.re)
    (hb : |(b - 2 * q).re| ≤ C * (3 - a.re)) :
    |(4 * b - 2 * q - 2 * q * a).re| ≤ (4 * C + 11) * (3 - a.re) := by
  let d := 3 - a.re
  have hd : 0 ≤ d := (sq_nonneg _).trans hqi
  have hai : a.im ^ 2 ≤ 6 * d := by
    have h := re_sq_add_im_sq_le ha
    nlinarith only [h, sq_nonneg d, show d = 3 - a.re from rfl]
  have hqr := (Complex.abs_re_le_norm q).trans hq
  have habs : |q.im * a.im| ≤ 7 / 2 * d := by
    rw [abs_le]
    constructor <;> nlinarith only [hqi, hai, sq_nonneg (q.im + a.im),
      sq_nonneg (q.im - a.im), show d = 3 - a.re from rfl]
  have hre : |(q * (a - 3)).re| ≤ 11 / 2 * d := by
    have ht : |q.re * (a.re - 3)| ≤ 2 * d := by
      rw [abs_mul, show a.re - 3 = -d by simp [d], abs_neg, abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_right hqr hd
    have h : |q.re * (a.re - 3) - q.im * a.im| ≤
        |q.re * (a.re - 3)| + |q.im * a.im| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le (q.re * (a.re - 3)) (-(q.im * a.im)))
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.re_ofNat,
      Complex.im_ofNat, sub_zero]
    linarith only [h, ht, habs]
  have hrew : 4 * b - 2 * q - 2 * q * a = 4 * (b - 2 * q) - 2 * (q * (a - 3)) := by
    ring
  have hreal (x y : ℂ) : (4 * x - 2 * y).re = 4 * x.re - 2 * y.re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero]
  rw [hrew, hreal]
  calc
    _ ≤ |4 * (b - 2 * q).re| + |2 * (q * (a - 3)).re| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le (4 * (b - 2 * q).re) (-(2 * (q * (a - 3)).re)))
    _ = 4 * |(b - 2 * q).re| + 2 * |(q * (a - 3)).re| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]
    _ ≤ (4 * C + 11) * (3 - a.re) := by
      dsimp only [d] at hre
      nlinarith only [hb, hre]

end Zalcman
