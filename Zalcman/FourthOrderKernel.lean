/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The real kernel in the fourth-order integral estimate
-/

public section

namespace Zalcman

open MeasureTheory Set

/-- Cauchy–Schwarz against the constant function on the unit interval. -/
theorem unit_intervalIntegral_sq_le_integral_sq {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 1)
    (hg₂ : IntervalIntegrable (fun t ↦ g t ^ 2) volume 0 1) :
    (∫ t in (0 : ℝ)..1, g t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, g t ^ 2 := by
  let M := ∫ t in (0 : ℝ)..1, g t
  have hzero : 0 ≤ ∫ t in (0 : ℝ)..1, (g t - M) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall zero_le_one fun _ ↦ sq_nonneg _
  have hform : (∫ t in (0 : ℝ)..1, (g t - M) ^ 2) =
      (∫ t in (0 : ℝ)..1, g t ^ 2) - M ^ 2 := by
    calc
      _ = ∫ t in (0 : ℝ)..1, g t ^ 2 - (2 * M) * g t + M ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hg₂.sub (hg.const_mul (2 * M))) intervalIntegrable_const,
          intervalIntegral.integral_sub hg₂ (hg.const_mul (2 * M)), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul]
        change (∫ t in (0 : ℝ)..1, g t ^ 2) - (2 * M) * M + M ^ 2 = _
        ring
  rw [hform] at hzero
  exact sub_nonneg.mp hzero

private lemma integral_primitive_product {v w : ℝ → ℝ}
    (hv : IntervalIntegrable v volume 0 1) (hw : IntervalIntegrable w volume 0 1) :
    (∫ t in (0 : ℝ)..1, v t * (∫ s in (0 : ℝ)..t, w s) +
      w t * (∫ s in (0 : ℝ)..t, v s)) =
      (∫ t in (0 : ℝ)..1, v t) * (∫ t in (0 : ℝ)..1, w t) := by
  let V (t : ℝ) := ∫ s in (0 : ℝ)..t, v s
  let W (t : ℝ) := ∫ s in (0 : ℝ)..t, w s
  have haV : AbsolutelyContinuousOnInterval V 0 1 :=
    hv.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have haW : AbsolutelyContinuousOnInterval W 0 1 :=
    hw.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hd : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc (0 : ℝ) 1 →
      HasDerivAt (fun x ↦ V x * W x) (v t * W t + w t * V t) t := by
    filter_upwards [hv.ae_hasDerivAt_integral, hw.ae_hasDerivAt_integral] with t hV hW ht
    have hv' : HasDerivAt V (v t) t := hV (uIoc_subset_uIcc ht) 0 left_mem_uIcc
    have hw' : HasDerivAt W (w t) t := hW (uIoc_subset_uIcc ht) 0 left_mem_uIcc
    simpa only [mul_comm (w t) (V t)] using hv'.fun_mul hw'
  change (∫ t in (0 : ℝ)..1, v t * W t + w t * V t) = V 1 * W 1
  calc
    _ = ∫ t in (0 : ℝ)..1, deriv (fun x ↦ V x * W x) t := by
      apply intervalIntegral.integral_congr_ae
      exact hd.mono fun _ h ht ↦ (h ht).deriv.symm
    _ = _ := by
      simpa only [V, W, intervalIntegral.integral_same, mul_zero, sub_zero] using
        (haV.fun_mul haW).integral_deriv_eq_sub

/-- The constant and symmetric linear parts of the triangular kernel can be
integrated by the product rule on one-dimensional primitives. -/
theorem fourth_order_main_kernel_integral_identity {v : ℝ → ℝ}
    (hv : IntervalIntegrable v volume 0 1) :
    let V (t : ℝ) := ∫ s in (0 : ℝ)..t, v s
    let W (t : ℝ) := ∫ s in (0 : ℝ)..t, (1 - s) * v s
    (∫ t in (0 : ℝ)..1, v t * (∫ s in (0 : ℝ)..t, (48 - 24 * s - 16 * t) * v s)) =
      4 * V 1 ^ 2 + 24 * V 1 * W 1 - 8 * (∫ t in (0 : ℝ)..1, (1 - t) * v t * V t) := by
  let V (t : ℝ) := ∫ s in (0 : ℝ)..t, v s
  let w (t : ℝ) := (1 - t) * v t
  let W (t : ℝ) := ∫ s in (0 : ℝ)..t, w s
  have hw : IntervalIntegrable w volume 0 1 :=
    hv.continuousOn_mul (continuous_const.sub continuous_id).continuousOn
  have hVc : ContinuousOn V (uIcc (0 : ℝ) 1) :=
    (hv.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
  have hWc : ContinuousOn W (uIcc (0 : ℝ) 1) :=
    (hw.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
  have hvV := hv.mul_continuousOn hVc
  have hvW := hv.mul_continuousOn hWc
  have hwV := hw.mul_continuousOn hVc
  have hsym : (∫ t in (0 : ℝ)..1, v t * W t + w t * V t) = V 1 * W 1 :=
    integral_primitive_product hv hw
  have hsq : 2 * (∫ t in (0 : ℝ)..1, v t * V t) = V 1 ^ 2 := by
    have h := integral_primitive_product hv hv
    simpa only [V, ← two_mul, intervalIntegral.integral_const_mul, pow_two] using h
  have hinner (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      (∫ s in (0 : ℝ)..t, (48 - 24 * s - 16 * t) * v s) =
        8 * V t + 24 * W t + (16 * (1 - t)) * V t := by
    have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc_right ht.2
    have hvt := hv.mono_set hsub
    have hwt := hw.mono_set hsub
    calc
      _ = ∫ s in (0 : ℝ)..t, 8 * v s + 24 * w s + (16 * (1 - t)) * v s := by
        apply intervalIntegral.integral_congr
        intro s _
        unfold w
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add ((hvt.const_mul 8).add (hwt.const_mul 24))
            (hvt.const_mul (16 * (1 - t))),
          intervalIntegral.integral_add (hvt.const_mul 8) (hwt.const_mul 24)]
        simp only [intervalIntegral.integral_const_mul, V, W]
  change _ = 4 * V 1 ^ 2 + 24 * V 1 * W 1 - 8 * (∫ t in (0 : ℝ)..1, w t * V t)
  calc
    _ = ∫ t in (0 : ℝ)..1,
        8 * (v t * V t) + 24 * (v t * W t + w t * V t) - 8 * (w t * V t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change v t * (∫ s in (0 : ℝ)..t, (48 - 24 * s - 16 * t) * v s) =
        8 * (v t * V t) + 24 * (v t * W t + w t * V t) - 8 * (w t * V t)
      rw [hinner t ht]
      unfold w
      ring
    _ = 8 * (∫ t in (0 : ℝ)..1, v t * V t) + 24 * (V 1 * W 1) -
        8 * (∫ t in (0 : ℝ)..1, w t * V t) := by
      rw [intervalIntegral.integral_sub ((hvV.const_mul 8).add ((hvW.add hwV).const_mul 24))
          (hwV.const_mul 8),
        intervalIntegral.integral_add (hvV.const_mul 8) ((hvW.add hwV).const_mul 24)]
      simp only [intervalIntegral.integral_const_mul, hsym]
    _ = _ := by linear_combination 4 * hsq

/-- The remaining triangular term is bounded by the weighted square integral. -/
theorem fourth_order_weighted_primitive_abs_le {v : ℝ → ℝ}
    (hv : IntervalIntegrable v volume 0 1)
    (hweight : IntervalIntegrable (fun t ↦ (1 - t) * v t ^ 2) volume 0 1) :
    |∫ t in (0 : ℝ)..1, (1 - t) * v t * (∫ s in (0 : ℝ)..t, v s)| ≤
      ∫ t in (0 : ℝ)..1, (1 - t) * v t ^ 2 := by
  let V (t : ℝ) := ∫ s in (0 : ℝ)..t, v s
  let g (t : ℝ) := Real.sqrt (1 - t) * |v t|
  let M := ∫ t in (0 : ℝ)..1, g t
  have hgInt : IntervalIntegrable g volume 0 1 :=
    hv.abs.continuousOn_mul (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousOn
  have hg₀ (t : ℝ) : 0 ≤ g t := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hg₂ (t : ℝ) (ht : t ≤ 1) : g t ^ 2 = (1 - t) * v t ^ 2 := by
    simp only [g, mul_pow, Real.sq_sqrt (sub_nonneg.mpr ht), sq_abs]
  have hnonneg (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : 0 ≤ 1 - t := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact sub_nonneg.mpr ht.2
  have hIntg₂ : IntervalIntegrable (fun t ↦ g t ^ 2) volume 0 1 := by
    apply hweight.congr_ae
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht ↦ (hg₂ t ht.2).symm)
  have hM₂ : M ^ 2 ≤ ∫ t in (0 : ℝ)..1, (1 - t) * v t ^ 2 := by
    refine (unit_intervalIntegral_sq_le_integral_sq hgInt hIntg₂).trans_eq ?_
    apply intervalIntegral.integral_congr
    intro t ht
    exact hg₂ t (sub_nonneg.mp (hnonneg t ht))
  have hVcont : ContinuousOn V (uIcc (0 : ℝ) 1) :=
    (hv.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
  have hVint : IntervalIntegrable (fun t ↦ (1 - t) * v t * V t) volume 0 1 :=
    (hv.continuousOn_mul (continuous_const.sub continuous_id).continuousOn).mul_continuousOn hVcont
  have hVbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (1 - t) * |V t| ≤ Real.sqrt (1 - t) * M := by
    have ht₀ : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
      rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc_right ht.2
    have hGsub := hgInt.mono_set hsub
    calc
      _ ≤ (1 - t) * (∫ s in (0 : ℝ)..t, |v s|) := mul_le_mul_of_nonneg_left
        (intervalIntegral.abs_integral_le_integral_abs ht.1) ht₀
      _ = ∫ s in (0 : ℝ)..t, (1 - t) * |v s| := (intervalIntegral.integral_const_mul _ _).symm
      _ ≤ ∫ s in (0 : ℝ)..t, Real.sqrt (1 - t) * g s := by
        apply intervalIntegral.integral_mono_on ht.1 ((hv.abs.mono_set hsub).const_mul _)
          (hGsub.const_mul _)
        intro s hs
        have hsT : 1 - t ≤ 1 - s := sub_le_sub_left hs.2 1
        have hCS : 1 - t ≤ Real.sqrt (1 - t) * Real.sqrt (1 - s) := calc
          _ = Real.sqrt (1 - t) * Real.sqrt (1 - t) := (Real.mul_self_sqrt ht₀).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsT) (Real.sqrt_nonneg _)
        simpa only [g, mul_assoc] using mul_le_mul_of_nonneg_right hCS (abs_nonneg (v s))
      _ = Real.sqrt (1 - t) * (∫ s in (0 : ℝ)..t, g s) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
          (ae_of_all _ hg₀) hgInt) (Real.sqrt_nonneg _)
  change |∫ t in (0 : ℝ)..1, (1 - t) * v t * V t| ≤ _
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, |(1 - t) * v t * V t| :=
      intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, M * g t := by
      apply intervalIntegral.integral_mono_on zero_le_one hVint.abs (hgInt.const_mul M)
      intro t ht
      rw [show (1 - t) * v t * V t = v t * ((1 - t) * V t) by ring,
        abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2)]
      calc
        _ ≤ |v t| * (Real.sqrt (1 - t) * M) :=
          mul_le_mul_of_nonneg_left (hVbound t ht) (abs_nonneg _)
        _ = _ := by unfold g; ring
    _ = M ^ 2 := by rw [intervalIntegral.integral_const_mul, pow_two]
    _ ≤ _ := hM₂

/-- A signed bound for the triangular kernel in terms of the imaginary driving
mean and its weighted square integral. -/
theorem fourth_order_main_kernel_abs_le {v : ℝ → ℝ}
    (hv : IntervalIntegrable v volume 0 1)
    (hweight : IntervalIntegrable (fun t ↦ (1 - t) * v t ^ 2) volume 0 1) :
    |∫ t in (0 : ℝ)..1, v t * (∫ s in (0 : ℝ)..t, (48 - 24 * s - 16 * t) * v s)| ≤
      16 * (∫ t in (0 : ℝ)..1, v t) ^ 2 + 20 * (∫ t in (0 : ℝ)..1, (1 - t) * v t ^ 2) := by
  let w (t : ℝ) := (1 - t) * v t
  let ν := ∫ t in (0 : ℝ)..1, v t
  let μ := ∫ t in (0 : ℝ)..1, w t
  let S := ∫ t in (0 : ℝ)..1, (1 - t) * v t ^ 2
  let R := ∫ t in (0 : ℝ)..1, w t * (∫ s in (0 : ℝ)..t, v s)
  have hw : IntervalIntegrable w volume 0 1 :=
    hv.continuousOn_mul (continuous_const.sub continuous_id).continuousOn
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      w t ^ 2 ≤ (1 - t) * v t ^ 2 := by
    dsimp only [w]
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith only [mul_nonneg (sub_nonneg.mpr ht.2) ht.1]
  have hw₂ : IntervalIntegrable (fun t ↦ w t ^ 2) volume 0 1 := by
    apply hweight.mono_fun' (hw.aestronglyMeasurable_restrict_uIoc.aemeasurable.pow_const 2).aestronglyMeasurable
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply (ae_restrict_iff' measurableSet_Ioc).2
    exact ae_of_all _ fun t ht ↦ by
      change ‖w t ^ 2‖ ≤ (1 - t) * v t ^ 2
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpoint t (Ioc_subset_Icc_self ht)
  have hμ : μ ^ 2 ≤ S :=
    (unit_intervalIntegral_sq_le_integral_sq hw hw₂).trans
      (intervalIntegral.integral_mono_on zero_le_one hw₂ hweight hpoint)
  have hR : |R| ≤ S := fourth_order_weighted_primitive_abs_le hv hweight
  rw [fourth_order_main_kernel_integral_identity hv]
  change |4 * ν ^ 2 + 24 * ν * μ - 8 * R| ≤ 16 * ν ^ 2 + 20 * S
  have h₁ := norm_sub_le (4 * ν ^ 2 + 24 * ν * μ) (8 * R)
  have h₂ := norm_add_le (4 * ν ^ 2) (24 * ν * μ)
  have hprod : 2 * |ν| * |μ| ≤ ν ^ 2 + μ ^ 2 := by
    have h := sq_nonneg (|ν| - |μ|)
    nlinarith only [h, sq_abs ν, sq_abs μ]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)] at h₁
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg ν)),
    abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24)] at h₂
  nlinarith only [h₁, h₂, hprod, hμ, hR]

end Zalcman
