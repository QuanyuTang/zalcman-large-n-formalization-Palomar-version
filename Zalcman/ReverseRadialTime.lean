/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Absolute continuity in reverse radial time

A finite chain continued by a constant normalized terminal map can be
reparametrized by \(t=e^{-u}\) without losing absolute continuity at \(t=0\).
-/

public section

namespace Zalcman

open Set
open scoped NNReal

/-- The reverse radial time path, including its prescribed value at zero. -/
@[expose] noncomputable def reverseRadialPath {X : Type*} (B : ℝ → X) (terminal : X)
    (t : ℝ) : X :=
  if 0 < t then B (-Real.log t) else terminal

/-- A path that is Lipschitz on \([0,T]\) and constant thereafter remains
Lipschitz on \([0,1]\) in reverse radial time. -/
theorem lipschitzOnWith_reverseRadialPath {X : Type*} [PseudoMetricSpace X]
    {B : ℝ → X} {terminal : X} {T : ℝ} {K : ℝ≥0} (hT : 0 ≤ T)
    (hB : LipschitzOnWith K B (Icc 0 T)) (hEnd : ∀ u ≥ T, B u = terminal) :
    LipschitzOnWith (K * ⟨Real.exp T, (Real.exp_pos T).le⟩)
      (reverseRadialPath B terminal) (Icc 0 1) := by
  let a := Real.exp (-T)
  let C : ℝ≥0 := ⟨Real.exp T, (Real.exp_pos T).le⟩
  have ha₀ : 0 < a := Real.exp_pos _
  have ha₁ : a ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hT)
  have hlogA : Real.log a = -T := Real.log_exp _
  have hAinv : a⁻¹ = Real.exp T := by simp only [a, Real.exp_neg, inv_inv]
  have hLog : LipschitzOnWith C (fun t ↦ -Real.log t) (Icc a 1) := by
    refine (convex_Icc _ _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht ↦ ((Real.hasDerivAt_log (ha₀.trans_le ht.1).ne').fun_neg).hasDerivWithinAt) ?_
    intro t ht
    rw [← NNReal.coe_le_coe, coe_nnnorm, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (ha₀.trans_le ht.1).le)]
    change t⁻¹ ≤ Real.exp T
    rw [← hAinv]
    exact inv_anti₀ ha₀ ht.1
  have hLogRange : MapsTo (fun t ↦ -Real.log t) (Icc a 1) (Icc 0 T) := by
    intro t ht
    have ht₀ := ha₀.trans_le ht.1
    refine ⟨neg_nonneg.mpr ((Real.log_le_log ht₀ ht.2).trans_eq Real.log_one), ?_⟩
    have h := Real.log_le_log ha₀ ht.1
    rw [hlogA] at h
    simpa only [neg_neg] using neg_le_neg h
  have hClampLip : LipschitzOnWith 1 (fun t : ℝ ↦ max a t) (Icc 0 1) :=
    (LipschitzWith.id.const_max a).lipschitzOnWith
  have hClampRange : MapsTo (fun t : ℝ ↦ max a t) (Icc 0 1) (Icc a 1) :=
    fun t ht ↦ ⟨le_max_left _ _, max_le ha₁ ht.2⟩
  have hComp : LipschitzOnWith (K * C) (fun t ↦ B (-Real.log (max a t))) (Icc 0 1) := by
    simpa only [mul_one, Function.comp_def] using
      hB.comp (hLog.comp hClampLip hClampRange) (hLogRange.comp hClampRange)
  have hEq (t : ℝ) :
      reverseRadialPath B terminal t = B (-Real.log (max a t)) := by
    by_cases ht₀ : 0 < t
    · rw [reverseRadialPath, ite_eq_left ht₀]
      by_cases hat : a ≤ t
      · rw [max_eq_right hat]
      · have hta : t ≤ a := (lt_of_not_ge hat).le
        have h := Real.log_le_log ht₀ hta
        rw [hlogA] at h
        have htime : T ≤ -Real.log t := by simpa only [neg_neg] using neg_le_neg h
        rw [hEnd _ htime, max_eq_left hta, hlogA, neg_neg, hEnd T le_rfl]
    · have hta := (le_of_not_gt ht₀).trans ha₀.le
      rw [reverseRadialPath, ite_eq_right ht₀, max_eq_left hta, hlogA, neg_neg, hEnd T le_rfl]
  refine LipschitzOnWith.of_dist_le_mul fun s hs t ht ↦ ?_
  rw [hEq s, hEq t]
  exact hComp.dist_le_mul s hs t ht

/-- The reverse radial coefficient path is absolutely continuous up to zero. -/
theorem absolutelyContinuousOnInterval_reverseRadialPath {X : Type*} [PseudoMetricSpace X]
    {B : ℝ → X} {terminal : X} {T : ℝ} {K : ℝ≥0} (hT : 0 ≤ T)
    (hB : LipschitzOnWith K B (Icc 0 T)) (hEnd : ∀ u ≥ T, B u = terminal) :
    AbsolutelyContinuousOnInterval (reverseRadialPath B terminal) 0 1 := by
  have hLip := lipschitzOnWith_reverseRadialPath hT hB hEnd
  rw [← uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hLip
  exact hLip.absolutelyContinuousOnInterval

end Zalcman
