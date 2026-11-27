/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Propagation from the logarithmic derivative inequality

An exponential estimate in the hyperbolic coordinate gives the polynomial
comparison in Euclidean radii, even when the deficit can vanish.
-/

public section

namespace Zalcman

open Set

/-- An upper differential bound gives an exponential comparison on the interval. -/
theorem le_exp_mul_of_hasDerivAt_le {H H' : ℝ → ℝ} {C x y : ℝ} (hxy : x ≤ y)
    (hd : ∀ v ∈ Icc x y, HasDerivAt H (H' v) v)
    (hbound : ∀ v ∈ Icc x y, H' v ≤ C * H v) :
    H y ≤ Real.exp (C * (y - x)) * H x := by
  let g (v : ℝ) := Real.exp (-C * v) * H v
  have hg (v : ℝ) (hv : v ∈ Icc x y) : HasDerivAt g
      (Real.exp (-C * v) * (H' v - C * H v)) v := by
    have h := (((hasDerivAt_id v).const_mul (-C)).exp).fun_mul (hd v hv)
    convert h using 1 <;> try rfl
    simp only [id, mul_one]
    ring
  have hanti : AntitoneOn g (Icc x y) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc x y)
    · exact fun v hv => (hg v hv).continuousAt.continuousWithinAt
    · exact fun v hv => (hg v (interior_subset hv)).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [(hg v (interior_subset hv)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sub_nonpos.mpr (hbound v (interior_subset hv)))
  have hh := hanti (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy
  dsimp only [g] at hh
  have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (C * y)).le
  calc
    H y = Real.exp (C * y) * (Real.exp (-C * y) * H y) := by
      rw [← mul_assoc, ← Real.exp_add, show C * y + -C * y = 0 by ring, Real.exp_zero, one_mul]
    _ ≤ Real.exp (C * y) * (Real.exp (-C * x) * H x) := hm
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]; congr 2 <;> ring

/-- Exponential distance in the hyperbolic coordinate is controlled by the Euclidean gaps. -/
theorem exp_artanh_sub_le {r s C : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s < 1)
    (hC : 0 ≤ C) :
    Real.exp (C * (Real.artanh s - Real.artanh r)) ≤ (2 : ℝ) ^ (C / 2) *
      ((1 - r) / (1 - s)) ^ (C / 2) := by
  have hr' : r ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hrs.trans_lt hs⟩
  have hs' : s ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hs⟩
  let d := Real.artanh s - Real.artanh r
  have hratioS : 0 ≤ (1 + s) / (1 - s) := div_nonneg (by linarith) (by linarith)
  have hratioR : 0 ≤ (1 + r) / (1 - r) := div_nonneg (by linarith) (by linarith)
  have hExp : Real.exp (2 * d) = ((1 + s) / (1 - s)) / ((1 + r) / (1 - r)) := by
    rw [two_mul, Real.exp_add, ← pow_two, show d = Real.artanh s - Real.artanh r by rfl,
      Real.exp_sub, div_pow, Real.exp_artanh hr', Real.exp_artanh hs',
      Real.sq_sqrt hratioS, Real.sq_sqrt hratioR]
  have hgap : 0 < (1 - r) / (1 - s) := div_pos (by linarith) (by linarith)
  have hfac : (1 + s) / (1 + r) ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hstep : Real.exp (2 * d) ≤ 2 * ((1 - r) / (1 - s)) := calc
    _ = ((1 + s) / (1 + r)) * ((1 - r) / (1 - s)) := by
      rw [hExp]
      field_simp [show 1 - r ≠ 0 by linarith, show 1 - s ≠ 0 by linarith,
        show 1 + r ≠ 0 by linarith]
    _ ≤ _ := mul_le_mul_of_nonneg_right hfac hgap.le
  change Real.exp (C * d) ≤ _
  have he : Real.exp (C * d) = Real.exp (2 * d) ^ (C / 2) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  rw [he, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hgap.le]
  exact Real.rpow_le_rpow (Real.exp_pos _).le hstep (by positivity)

/-- A monotone positive normalization preserves the two-radius propagation estimate. -/
theorem normalized_deficit_le_of_hasDerivAt_le {H H' Z : ℝ → ℝ} {C r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s < 1) (hC : 0 ≤ C)
    (hd : ∀ v ∈ Icc (Real.artanh r) (Real.artanh s), HasDerivAt H (H' v) v)
    (hbound : ∀ v ∈ Icc (Real.artanh r) (Real.artanh s), H' v ≤ C * H v)
    (hH : 0 ≤ H (Real.artanh r)) (hZ : 0 < Z (Real.artanh r))
    (hZmono : Z (Real.artanh r) ≤ Z (Real.artanh s)) :
    H (Real.artanh s) / Z (Real.artanh s) ≤ (2 : ℝ) ^ (C / 2) *
      ((1 - r) / (1 - s)) ^ (C / 2) * (H (Real.artanh r) / Z (Real.artanh r)) := by
  have hxy := Real.artanh_le_artanh (show -1 < r by linarith) hs hrs
  have hHs := le_exp_mul_of_hasDerivAt_le hxy hd hbound
  have hZs := hZ.trans_le hZmono
  calc
    _ ≤ (Real.exp (C * (Real.artanh s - Real.artanh r)) * H (Real.artanh r)) /
          Z (Real.artanh s) := div_le_div_of_nonneg_right hHs hZs.le
    _ ≤ (Real.exp (C * (Real.artanh s - Real.artanh r)) * H (Real.artanh r)) /
          Z (Real.artanh r) := div_le_div_of_nonneg_left (mul_nonneg (Real.exp_pos _).le hH) hZ hZmono
    _ = Real.exp (C * (Real.artanh s - Real.artanh r)) *
          (H (Real.artanh r) / Z (Real.artanh r)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (exp_artanh_sub_le hr hrs hs hC) (div_nonneg hH hZ.le)

end Zalcman
