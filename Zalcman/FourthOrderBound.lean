/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.QuadraticDriving
public import Zalcman.FourthOrderIntegrand
public import Zalcman.FourthOrderRemainder
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The fourth-order estimate for a unit reverse driver
-/

@[expose] public section

noncomputable section

namespace Zalcman

open MeasureTheory Set

/-- A continuous expression in time and a measurable unit driver is integrable
on the unit interval. -/
theorem intervalIntegrable_unit_driver_comp {η : ℝ → ℂ}
    (hη : Measurable η) (hunit : ∀ t ∈ Ioc (0 : ℝ) 1, ‖η t‖ = 1)
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (G : ℝ × ℂ → E) (hG : Continuous G) :
    IntervalIntegrable (fun t ↦ G (t, η t)) volume 0 1 := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let _ : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    norm_num⟩
  have hc : IsCompact (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn hG.continuousOn
  rw [intervalIntegrable_iff, uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hm : Measurable (fun t : ℝ ↦ G (t, η t)) := hG.measurable.comp (measurable_id.prodMk hη)
  apply Integrable.of_bound hm.aestronglyMeasurable B
  have ha : ∀ᵐ t ∂μ, t ∈ Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  filter_upwards [ha] with t ht
  exact hB _ ⟨Ioc_subset_Icc_self ht, by
    rw [Metric.mem_closedBall, dist_zero_right, hunit t ht]⟩

private lemma intervalIntegrable_realPart {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t ↦ (f t).re) volume a b :=
  ⟨Complex.reCLM.integrable_comp hf.1, Complex.reCLM.integrable_comp hf.2⟩

private lemma interval_integral_realPart {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, (f t).re) = (∫ t in a..b, f t).re := by
  simpa only [Complex.reCLM_apply] using Complex.reCLM.intervalIntegral_comp_comm hf

private lemma integrable_times_primitive {E : Type*} [NormedRing E] [NormedAlgebra ℝ E]
    [CompleteSpace E] {f g : ℝ → E} (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) :
    IntervalIntegrable (fun t ↦ f t * (∫ s in (0 : ℝ)..t, g s)) volume 0 1 :=
  hf.mul_continuousOn (intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc)

private lemma driving_y_bounds {z : ℂ} (h : ‖z‖ = 1) :
    0 ≤ (1 - z.re) / 2 ∧ (1 - z.re) / 2 ≤ 1 := by
  have hr := Complex.abs_re_le_norm z
  rw [h] at hr
  obtain ⟨hla, hhi⟩ := abs_le.mp hr
  constructor <;> linarith only [hla, hhi]

private lemma real_of_driving {z : ℂ} :
    z.re = 1 - 2 * ((1 - z.re) / 2) := by ring

/-- The linear fourth-order integral costs at most 32 times the quadratic energy. -/
theorem abs_fourth_order_linear_integral_le {η : ℝ → ℂ}
    (hη : Measurable η) (hunit : ∀ t ∈ Ioc (0 : ℝ) 1, ‖η t‖ = 1) :
    let y (t : ℝ) := (1 - (η t).re) / 2
    |(∫ t in (0 : ℝ)..1, 8 * fourthDrivingA (η t) + 6 * fourthDrivingB t (η t) +
        fourthDrivingC t (η t)).re| ≤
      32 * ∫ t in (0 : ℝ)..1, (1 - t) * y t + t * y t ^ 2 := by
  let y (t : ℝ) := (1 - (η t).re) / 2
  let H (t : ℝ) := 8 * fourthDrivingA (η t) + 6 * fourthDrivingB t (η t) + fourthDrivingC t (η t)
  let E (t : ℝ) := (1 - t) * y t + t * y t ^ 2
  change |(∫ t in (0 : ℝ)..1, H t).re| ≤ 32 * ∫ t in (0 : ℝ)..1, E t
  have hH : IntervalIntegrable H volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit
      (fun p ↦ 8 * fourthDrivingA p.2 + 6 * fourthDrivingB p.1 p.2 + fourthDrivingC p.1 p.2)
      (by unfold fourthDrivingA fourthDrivingB fourthDrivingC; fun_prop)
  have hE : IntervalIntegrable E volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit
      (fun p ↦ (1 - p.1) * ((1 - p.2.re) / 2) + p.1 * ((1 - p.2.re) / 2) ^ 2) (by fun_prop)
  rw [← interval_integral_realPart hH]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, |(H t).re| :=
      intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, 32 * E t := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
        (intervalIntegrable_realPart hH).abs (hE.const_mul 32)
      intro t ht
      have hut := hunit t ⟨ht.1, ht.2.le⟩
      have ⟨hy₀, hy₁⟩ := driving_y_bounds hut
      exact abs_fourthDriving_linear_integrand_re_le hut real_of_driving rfl hy₀ hy₁ ht.1.le ht.2.le
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- The integral of the second-order velocity is expressed by its two driving means. -/
theorem fourth_order_secondVelocity_integral_parts {η : ℝ → ℂ}
    (hη : Measurable η) (hunit : ∀ t ∈ Ioc (0 : ℝ) 1, ‖η t‖ = 1) :
    let y (t : ℝ) := (1 - (η t).re) / 2
    let v (t : ℝ) := (η t).im
    let I := ∫ t in (0 : ℝ)..1, fourthDrivingA (η t)
    I.re = -4 * (∫ t in (0 : ℝ)..1, y t) ∧ I.im = 2 * (∫ t in (0 : ℝ)..1, v t) := by
  let A (t : ℝ) := fourthDrivingA (η t)
  let y (t : ℝ) := (1 - (η t).re) / 2
  let v (t : ℝ) := (η t).im
  have hA : IntervalIntegrable A volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit (fun z ↦ fourthDrivingA z.2)
      (by unfold fourthDrivingA; fun_prop)
  change (∫ t in (0 : ℝ)..1, A t).re = -4 * (∫ t in (0 : ℝ)..1, y t) ∧
    (∫ t in (0 : ℝ)..1, A t).im = 2 * (∫ t in (0 : ℝ)..1, v t)
  constructor
  · rw [← interval_integral_realPart hA, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    exact (fourthDrivingA_re_im (η := η t) real_of_driving rfl).1
  · have hi := Complex.imCLM.intervalIntegral_comp_comm hA
    simp only [Complex.imCLM_apply] at hi
    rw [← hi, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    exact (fourthDrivingA_re_im (η := η t) real_of_driving rfl).2

/-- The mixed summand in the real part of the triangular fourth-order integral. -/
def fourthOrderMixedRemainder (y v : ℝ → ℝ) (s t : ℝ) : ℝ :=
  192 * y s * y t - 192 * s * y t * y s * (1 - y s) - 128 * t * y t * y s * (1 - y t) -
    48 * s * y s * v s * v t - 32 * t * y t * v s * v t

private theorem fourthOrderMixedRemainder_inner {y v : ℝ → ℝ}
    (hy : IntervalIntegrable y volume 0 1) (hv : IntervalIntegrable v volume 0 1)
    (hy₁ : IntervalIntegrable (fun s ↦ s * y s * (1 - y s)) volume 0 1)
    (hv₁ : IntervalIntegrable (fun s ↦ s * y s * v s) volume 0 1)
    {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) 1) :
    IntervalIntegrable (fun s ↦ fourthOrderMixedRemainder y v s t) volume 0 t ∧
      (∫ s in (0 : ℝ)..t, fourthOrderMixedRemainder y v s t) =
        192 * y t * (∫ s in (0 : ℝ)..t, y s) -
          192 * y t * (∫ s in (0 : ℝ)..t, s * y s * (1 - y s)) -
          128 * (t * y t * (1 - y t)) * (∫ s in (0 : ℝ)..t, y s) -
          48 * v t * (∫ s in (0 : ℝ)..t, s * y s * v s) -
          32 * (t * y t * v t) * (∫ s in (0 : ℝ)..t, v s) := by
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc_right ht.2
  let a := 192 * y t
  let b := 128 * (t * y t * (1 - y t))
  let c := 48 * v t
  let d := 32 * (t * y t * v t)
  have hfun : (fun s ↦ fourthOrderMixedRemainder y v s t) =
      fun s ↦ a * y s - a * (s * y s * (1 - y s)) - b * y s -
        c * (s * y s * v s) - d * v s := by
    funext s
    dsimp only [fourthOrderMixedRemainder, a, b, c, d]
    ring
  have ha := (hy.mono_set hsub).const_mul a
  have ha' := (hy₁.mono_set hsub).const_mul a
  have hb := (hy.mono_set hsub).const_mul b
  have hc := (hv₁.mono_set hsub).const_mul c
  have hd := (hv.mono_set hsub).const_mul d
  rw [hfun]
  refine ⟨(((ha.sub ha').sub hb).sub hc).sub hd, ?_⟩
  rw [intervalIntegral.integral_sub (((ha.sub ha').sub hb).sub hc) hd,
    intervalIntegral.integral_sub ((ha.sub ha').sub hb) hc,
    intervalIntegral.integral_sub (ha.sub ha') hb, intervalIntegral.integral_sub ha ha']
  simp only [intervalIntegral.integral_const_mul, a, b, c, d]

private theorem fourthOrderMixedRemainder_outer {y v : ℝ → ℝ}
    (hy : IntervalIntegrable y volume 0 1) (hv : IntervalIntegrable v volume 0 1)
    (hy₁ : IntervalIntegrable (fun s ↦ s * y s * (1 - y s)) volume 0 1)
    (hv₁ : IntervalIntegrable (fun s ↦ s * y s * v s) volume 0 1) :
    IntervalIntegrable (fun t ↦ ∫ s in (0 : ℝ)..t, fourthOrderMixedRemainder y v s t) volume 0 1 := by
  have ha := integrable_times_primitive (hy.const_mul 192) hy
  have ha' := integrable_times_primitive (hy.const_mul 192) hy₁
  have hb := integrable_times_primitive (hy₁.const_mul 128) hy
  have hc := integrable_times_primitive (hv.const_mul 48) hv₁
  have hd := integrable_times_primitive (hv₁.const_mul 32) hv
  apply ((((ha.sub ha').sub hb).sub hc).sub hd).congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).2
  exact ae_of_all _ fun t ht ↦ (fourthOrderMixedRemainder_inner hy hv hy₁ hv₁ (uIoc_subset_uIcc ht)).2.symm

set_option maxHeartbeats 1500000 in
/-- The triangular fourth-order integral splits into the signed kernel and
the mixed remainder. Both are bounded by quadratic driving moments. -/
theorem abs_fourth_order_triangular_integral_le {η : ℝ → ℂ}
    (hη : Measurable η) (hunit : ∀ t ∈ Ioc (0 : ℝ) 1, ‖η t‖ = 1) {E : ℝ} :
    let y (t : ℝ) := (1 - (η t).re) / 2
    let v (t : ℝ) := (η t).im
    let A (t : ℝ) := fourthDrivingA (η t)
    let B (t : ℝ) := fourthDrivingB t (η t)
    let P (t : ℝ) := ∫ s in (0 : ℝ)..t, A s
    let Q (t : ℝ) := ∫ s in (0 : ℝ)..t, B s
    (∫ t in (0 : ℝ)..1, y t) ^ 2 ≤ E →
    (∫ t in (0 : ℝ)..1, y t ^ 2) ≤ E →
    (∫ t in (0 : ℝ)..1, v t ^ 2) ≤ 4 * (∫ t in (0 : ℝ)..1, y t) →
    |(∫ t in (0 : ℝ)..1, 12 * A t * P t + (2 * B t * P t + 3 * A t * Q t)).re| ≤
      16 * (∫ t in (0 : ℝ)..1, v t) ^ 2 + 20 * (∫ t in (0 : ℝ)..1, (1 - t) * v t ^ 2) + 832 * E := by
  let y (t : ℝ) := (1 - (η t).re) / 2
  let v (t : ℝ) := (η t).im
  let A (t : ℝ) := fourthDrivingA (η t)
  let B (t : ℝ) := fourthDrivingB t (η t)
  let P (t : ℝ) := ∫ s in (0 : ℝ)..t, A s
  let Q (t : ℝ) := ∫ s in (0 : ℝ)..t, B s
  let H (t : ℝ) := 12 * A t * P t + (2 * B t * P t + 3 * A t * Q t)
  change (∫ t in (0 : ℝ)..1, y t) ^ 2 ≤ E →
    (∫ t in (0 : ℝ)..1, y t ^ 2) ≤ E →
    (∫ t in (0 : ℝ)..1, v t ^ 2) ≤ 4 * (∫ t in (0 : ℝ)..1, y t) →
    |(∫ t in (0 : ℝ)..1, H t).re| ≤
      16 * (∫ t in (0 : ℝ)..1, v t) ^ 2 + 20 * (∫ t in (0 : ℝ)..1, (1 - t) * v t ^ 2) + 832 * E
  intro hY₂ hEY hVY
  have hA : IntervalIntegrable A volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit (fun p ↦ fourthDrivingA p.2)
      (by unfold fourthDrivingA; fun_prop)
  have hB : IntervalIntegrable B volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit (fun p ↦ fourthDrivingB p.1 p.2)
      (by unfold fourthDrivingB; fun_prop)
  have hH : IntervalIntegrable H volume 0 1 :=
    (integrable_times_primitive (hA.const_mul 12) hA).add
      ((integrable_times_primitive (hB.const_mul 2) hA).add
        (integrable_times_primitive (hA.const_mul 3) hB))
  have hy : IntervalIntegrable y volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit (fun p ↦ (1 - p.2.re) / 2) (by fun_prop)
  have hv : IntervalIntegrable v volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit (fun p ↦ p.2.im) (by fun_prop)
  have hy₂ : IntervalIntegrable (fun t ↦ y t ^ 2) volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit (fun p ↦ ((1 - p.2.re) / 2) ^ 2) (by fun_prop)
  have hv₂ : IntervalIntegrable (fun t ↦ v t ^ 2) volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit (fun p ↦ p.2.im ^ 2) (by fun_prop)
  have hyv : IntervalIntegrable (fun t ↦ y t * |v t|) volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit (fun p ↦ ((1 - p.2.re) / 2) * |p.2.im|) (by fun_prop)
  have hy₁ : IntervalIntegrable (fun t ↦ t * y t * (1 - y t)) volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit
      (fun p ↦ p.1 * ((1 - p.2.re) / 2) * (1 - (1 - p.2.re) / 2)) (by fun_prop)
  have hv₁ : IntervalIntegrable (fun t ↦ t * y t * v t) volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit (fun p ↦ p.1 * ((1 - p.2.re) / 2) * p.2.im) (by fun_prop)
  have hvw : IntervalIntegrable (fun t ↦ (1 - t) * v t ^ 2) volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit (fun p ↦ (1 - p.1) * p.2.im ^ 2) (by fun_prop)
  let R := fourthOrderMixedRemainder y v
  let J (t : ℝ) := ∫ s in (0 : ℝ)..t, R s t
  let M (t : ℝ) := v t * (∫ s in (0 : ℝ)..t, (48 - 24 * s - 16 * t) * v s)
  have hJ : IntervalIntegrable J volume 0 1 := fourthOrderMixedRemainder_outer hy hv hy₁ hv₁
  have hy₀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : 0 ≤ y t := (driving_y_bounds (hunit t ht)).1
  have hPoint (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : (H t).re = -M t + J t := by
    have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
      rw [uIcc_of_le ht.1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc_right ht.2
    let Ht (s : ℝ) := 12 * A t * A s + 3 * A t * B s + 2 * B t * A s
    have hF₁ := (hA.mono_set hsub).const_mul (12 * A t)
    have hF₂ := (hB.mono_set hsub).const_mul (3 * A t)
    have hF₃ := (hA.mono_set hsub).const_mul (2 * B t)
    have hHt : IntervalIntegrable Ht volume 0 t := (hF₁.add hF₂).add hF₃
    have hEq : (∫ s in (0 : ℝ)..t, Ht s) = H t := by
      unfold Ht
      rw [intervalIntegral.integral_add (hF₁.add hF₂) hF₃, intervalIntegral.integral_add hF₁ hF₂]
      simp only [intervalIntegral.integral_const_mul, H, P, Q]
      ring
    rw [← hEq, ← interval_integral_realPart hHt]
    let g (s : ℝ) := (48 - 24 * s - 16 * t) * v s
    have hg : IntervalIntegrable g volume 0 t :=
      (hv.mono_set hsub).continuousOn_mul
        (show Continuous (fun s : ℝ ↦ 48 - 24 * s - 16 * t) by fun_prop).continuousOn
    have hRt := (fourthOrderMixedRemainder_inner hy hv hy₁ hv₁ (hsub (right_mem_uIcc))).1
    calc
      _ = ∫ s in (0 : ℝ)..t, (-v t) * g s + R s t := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht.1.le
        intro s hs
        have hsu := hunit s ⟨hs.1, hs.2.le.trans ht.2⟩
        have h := fourthDriving_triangle_integrand_re hsu (hunit t ht) real_of_driving real_of_driving
          rfl rfl s t
        change (Ht s).re = (-v t) * g s + R s t
        rw [show (Ht s).re = _ from h]
        dsimp only [g, R, fourthOrderMixedRemainder]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hg.const_mul (-v t)) hRt,
          intervalIntegral.integral_const_mul]
        dsimp only [M, J, g]
        ring
  have hM : IntervalIntegrable M volume 0 1 := by
    apply (hJ.sub (intervalIntegrable_realPart hH)).congr_ae
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply (ae_restrict_iff' measurableSet_Ioc).2
    exact ae_of_all _ fun t ht ↦ by
      change J t - (H t).re = M t
      linarith only [hPoint t ht]
  have hTransfer : (∫ t in (0 : ℝ)..1, H t).re =
      -(∫ t in (0 : ℝ)..1, M t) + ∫ t in (0 : ℝ)..1, J t := by
    have hMneg : IntervalIntegrable (fun t ↦ -M t) volume 0 1 := hM.neg
    rw [← interval_integral_realPart hH, ← intervalIntegral.integral_neg,
      ← intervalIntegral.integral_add hMneg hJ]
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    exact fun t ht ↦ hPoint t ⟨ht.1, ht.2.le⟩
  have hKernel := fourth_order_main_kernel_abs_le hv hvw
  have hRemainder := abs_fourth_order_remainder_integral_le hy hv hyv hy₀
    (fun t ht ↦ (fourthOrderMixedRemainder_inner hy hv hy₁ hv₁
      (by rw [uIcc_of_le zero_le_one]; exact ⟨ht.1.le, ht.2.le⟩)).1)
    hJ (fun t ht s hs ↦ abs_fourthDriving_triangle_remainder_le hs.1.le (hs.2.le.trans ht.2.le)
      ht.1.le ht.2.le (hy₀ s ⟨hs.1, hs.2.le.trans ht.2.le⟩)
      (driving_y_bounds (hunit s ⟨hs.1, hs.2.le.trans ht.2.le⟩)).2
      (hy₀ t ⟨ht.1, ht.2.le⟩) (driving_y_bounds (hunit t ⟨ht.1, ht.2.le⟩)).2)
  have hMoment := mixed_fourth_order_moments_le hy hv hy₂ hv₂ hy₀ hY₂ hEY hVY
  change |∫ t in (0 : ℝ)..1, M t| ≤ _ at hKernel
  change |∫ t in (0 : ℝ)..1, J t| ≤ _ at hRemainder
  rw [hTransfer]
  calc
    _ ≤ |∫ t in (0 : ℝ)..1, M t| + |∫ t in (0 : ℝ)..1, J t| := by
      simpa only [abs_neg] using abs_add_le (-(∫ t in (0 : ℝ)..1, M t)) (∫ t in (0 : ℝ)..1, J t)
    _ ≤ _ := by nlinarith only [hKernel, hRemainder, hMoment, hY₂]

/-- The integrated correction for the order-four coefficient in Koebe coordinates. -/
def fourthOrderIntegratedCorrection (η : ℝ → ℂ) : ℂ :=
  let A (t : ℝ) := fourthDrivingA (η t)
  let B (t : ℝ) := fourthDrivingB t (η t)
  let P (t : ℝ) := ∫ s in (0 : ℝ)..t, A s
  let Q (t : ℝ) := ∫ s in (0 : ℝ)..t, B s
  (∫ t in (0 : ℝ)..1, 8 * A t + 6 * B t + fourthDrivingC t (η t)) +
    (∫ t in (0 : ℝ)..1, 12 * A t * P t + (2 * B t * P t + 3 * A t * Q t)) + (P 1) ^ 3

/-- The fourth-order real-part bound follows from the three reverse-time
coefficient integral formulas. -/
theorem abs_fourth_coeff_sub_two_second_re_le_of_unit_driving {η : ℝ → ℂ} {a₂ a₃ a₄ : ℂ}
    (hη : Measurable η) (hunit : ∀ t ∈ Ioc (0 : ℝ) 1, ‖η t‖ = 1)
    (ha₂ : a₂ = 2 * ∫ t in (0 : ℝ)..1, η t)
    (ha₃ : a₃ = a₂ ^ 2 - 2 * ∫ t in (0 : ℝ)..1, (t : ℂ) * η t ^ 2)
    (ha₄ : a₄ - 2 * a₂ = fourthOrderIntegratedCorrection η)
    (ha₂sign : 0 ≤ a₂.re) :
    |(a₄ - 2 * a₂).re| ≤ 3800 * (3 - a₃.re) := by
  let y (t : ℝ) := (1 - (η t).re) / 2
  let v (t : ℝ) := (η t).im
  let Y := ∫ t in (0 : ℝ)..1, y t
  let ν := ∫ t in (0 : ℝ)..1, v t
  let E := ∫ t in (0 : ℝ)..1, (1 - t) * y t + t * y t ^ 2
  let d := 3 - a₃.re
  let A (t : ℝ) := fourthDrivingA (η t)
  let B (t : ℝ) := fourthDrivingB t (η t)
  let P (t : ℝ) := ∫ s in (0 : ℝ)..t, A s
  let Q (t : ℝ) := ∫ s in (0 : ℝ)..t, B s
  let I₁ := ∫ t in (0 : ℝ)..1, 8 * A t + 6 * B t + fourthDrivingC t (η t)
  let I₂ := ∫ t in (0 : ℝ)..1, 12 * A t * P t + (2 * B t * P t + 3 * A t * Q t)
  let I₃ := (P 1) ^ 3
  obtain ⟨hY₀, hY₁, hEd, hY₂, hEY, hVY, hVw, hν, _⟩ :=
    quadratic_moments_of_unit_driving hη hunit ha₂ ha₃ ha₂sign
  have hlin : |I₁.re| ≤ 32 * E := abs_fourth_order_linear_integral_le hη hunit
  have htri := abs_fourth_order_triangular_integral_le (E := E) hη hunit hY₂ hEY hVY
  change |I₂.re| ≤ 16 * ν ^ 2 + 20 * (∫ t in (0 : ℝ)..1, (1 - t) * v t ^ 2) + 832 * E at htri
  obtain ⟨hPr, hPi⟩ := fourth_order_secondVelocity_integral_parts hη hunit
  have hcub : |I₃.re| ≤ 64 * E + 12 * d :=
    abs_fourthDriving_cube_re_le hPr hPi hY₀ (hY₁.trans (by norm_num)) hY₂ hν
  have hd : 0 ≤ d := by
    change ν ^ 2 ≤ d / 4 at hν
    linarith only [hν, sq_nonneg ν]
  rw [ha₄]
  change |(I₁ + I₂ + I₃).re| ≤ 3800 * d
  rw [Complex.add_re, Complex.add_re]
  have hadd₁ := abs_add_le I₁.re I₂.re
  have hadd₂ := abs_add_le (I₁.re + I₂.re) I₃.re
  change E ≤ 65 * d / 16 at hEd
  change (∫ t in (0 : ℝ)..1, (1 - t) * v t ^ 2) ≤ d / 4 at hVw
  nlinarith only [hlin, htri, hcub, hν, hVw, hEd, hd, hadd₁, hadd₂]

end Zalcman
