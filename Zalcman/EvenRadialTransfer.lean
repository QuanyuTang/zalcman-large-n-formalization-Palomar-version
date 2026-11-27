/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.RadialProjection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absorption using the even projection and signed-radius bound
-/

public section

namespace Zalcman

open Finset

/-- Pointwise comparison of nonnegative, linearly bounded coefficients gives
comparison of the radial deficit series at a positive radius. -/
theorem radialDeficitSeries_mono_of_linear_bound {d e : ℕ → ℝ}
    (hd : ∀ j, 0 ≤ d j) (he : ∀ j, 0 ≤ e j)
    (hb : ∀ j : ℕ, e j ≤ 2 * ((j : ℝ) + 1)) (hle : ∀ j, d j ≤ e j)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    radialDeficitSeries d r ≤ radialDeficitSeries e r := by
  have habs : |r| < 1 := (abs_of_nonneg hr).trans_lt hr1
  have hd' : ∀ j : ℕ, d j ≤ 2 * ((j : ℝ) + 1) := fun j ↦ (hle j).trans (hb j)
  unfold radialDeficitSeries
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact (summable_radialDeficit_of_le hd hd' habs).of_norm.tsum_le_tsum
    (fun j ↦ mul_le_mul_of_nonneg_right (hle j) (pow_nonneg hr _))
    (summable_radialDeficit_of_le he hb habs).of_norm

/-- The even projection, tail comparison and signed-radius estimate control
the full positive radial deficit by the even prefix and the signed-radius error. -/
theorem radialDeficitSeries_even_exp_absorb {d : ℕ → ℝ}
    (hd : ∀ j, 0 ≤ d j) (hb : ∀ j : ℕ, d j ≤ 2 * ((j : ℝ) + 1))
    (n : ℕ) {R x A B C : ℝ} (hR : 1 ≤ R) (hx : 0 < x)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hprop : radialDeficitSeries d (Real.exp (-x)) ≤
      A * radialDeficitSeries d (Real.exp (-(R * x))))
    (hnegative : radialDeficitSeries d (-Real.exp (-(R * x))) ≤
      B * radialDeficitSeries d (Real.exp (-x)) + C)
    (hsmall₁ : 2 * A * R ^ 2 * Real.exp (-((R - 1) * x) * n) ≤ 1 / 4)
    (hsmall₂ : A * (R * x) ^ 2 * B ≤ 1 / 4) :
    radialDeficitSeries d (Real.exp (-x)) ≤
      4 * A * (R * x) ^ 2 * (∑ j ∈ range n, evenCoefficientDeficits d j) +
        2 * A * (R * x) ^ 2 * C := by
  let r := Real.exp (-(R * x))
  let s := Real.exp (-x)
  let h := radialDeficitSeries d s
  let M := ∑ j ∈ range n, evenCoefficientDeficits d j
  let E := R ^ 2 * Real.exp (-((R - 1) * x) * n)
  have hE₀ : 0 ≤ E := mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
  have hxR : 0 < R * x := mul_pos (zero_lt_one.trans_le hR) hx
  have hr : 0 < r := Real.exp_pos _
  have hs : 0 < s := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hxR)
  have hs1 : s < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
  have hr_abs : |r| < 1 := (abs_of_pos hr).trans_lt hr1
  have hr_abs_neg : |-r| < 1 := (abs_neg r).trans_lt hr_abs
  have hh0 : 0 ≤ h := radialDeficitSeries_nonneg hd hs.le
  have he₀ (j : ℕ) : 0 ≤ evenCoefficientDeficits d j := by
    unfold evenCoefficientDeficits
    split
    · exact le_rfl
    · exact hd j
  have he_le (j : ℕ) : evenCoefficientDeficits d j ≤ d j := by
    unfold evenCoefficientDeficits
    split
    · exact hd j
    · exact le_rfl
  have heb (j : ℕ) : evenCoefficientDeficits d j ≤ 2 * ((j : ℝ) + 1) :=
    (he_le j).trans (hb j)
  have he_s : radialDeficitSeries (evenCoefficientDeficits d) s ≤ h :=
    radialDeficitSeries_mono_of_linear_bound he₀ hd hb he_le hs.le hs1
  have htail : radialDeficitSeries (evenCoefficientDeficits d) r ≤ (R * x) ^ 2 * M + E * h := by
    exact (radialDeficitSeries_exp_tail_compare he₀ heb n hR hx).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left he_s hE₀) _)
  have hproj := (radialDeficitSeries_projections d hr.le
    (summable_radialDeficit_of_le hd hb hr_abs).of_norm
    (summable_radialDeficit_of_le hd hb hr_abs_neg).of_norm).1
  have hratio : ((1 - r) / (1 + r)) ^ 2 ≤ (R * x) ^ 2 := by
    have hgap : 0 ≤ 1 - r := sub_nonneg.mpr hr1.le
    have hdiv : (1 - r) / (1 + r) ≤ 1 - r := by
      rw [div_le_iff₀ (by positivity : 0 < 1 + r)]
      nlinarith only [mul_nonneg hgap hr.le]
    have hexp : 1 - r ≤ R * x := by
      dsimp [r]
      linarith only [Real.one_sub_le_exp_neg (R * x)]
    exact pow_le_pow_left₀ (by positivity) (hdiv.trans hexp) 2
  have hneg : ((1 - r) / (1 + r)) ^ 2 * radialDeficitSeries d (-r) ≤
      (R * x) ^ 2 * (B * h + C) :=
    (mul_le_mul_of_nonneg_left hnegative (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hratio (add_nonneg (mul_nonneg hB hh0) hC))
  have hr_bound : radialDeficitSeries d r ≤
      2 * ((R * x) ^ 2 * M + E * h) + (R * x) ^ 2 * (B * h + C) := by
    rw [hproj]
    exact add_le_add (mul_le_mul_of_nonneg_left htail (by norm_num)) hneg
  have hpre : h ≤
      2 * A * (R * x) ^ 2 * M + (2 * A * E) * h + (A * (R * x) ^ 2 * B) * h +
        A * (R * x) ^ 2 * C := by
    calc
      _ ≤ A * radialDeficitSeries d r := hprop
      _ ≤ _ := mul_le_mul_of_nonneg_left hr_bound hA
      _ = _ := by ring
  have hsmall₁' : 2 * A * E ≤ 1 / 4 := by
    unfold E
    rwa [← mul_assoc]
  have hcut₁ := mul_le_mul_of_nonneg_right hsmall₁' hh0
  have hcut₂ := mul_le_mul_of_nonneg_right hsmall₂ hh0
  change h ≤ 4 * A * (R * x) ^ 2 * M + 2 * A * (R * x) ^ 2 * C
  nlinarith only [hpre, hcut₁, hcut₂]

end Zalcman
