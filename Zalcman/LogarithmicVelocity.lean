/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CoefficientVelocity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Time derivatives of the normalized logarithm

Spatial differentiation of the distinguished logarithm is quotient differentiation.
Local uniform convergence of the time slopes of the maps therefore gives local uniform
convergence of the time slopes of the logarithms, including at the origin.
-/

public section

namespace Zalcman

open Filter Set
open scoped Topology Uniformity

private theorem locallyUniform_fixed {ι : Type*} {l : Filter ι} (f : ℂ → ℂ) :
    TendstoLocallyUniformlyOn (fun _ : ι ↦ f) f l unitDisk := by
  intro v hv x hx
  exact ⟨unitDisk, self_mem_nhdsWithin, Eventually.of_forall fun _ _ _ ↦ refl_mem_uniformity hv⟩

private theorem dslope_holomorphic {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisk) :
    DifferentiableOn ℂ (dslope f 0) unitDisk :=
  (Complex.differentiableOn_dslope (unitDisk_isOpen.mem_nhds zero_mem_unitDisk)).mpr hf

private theorem locallyUniform_dslope_of_deriv {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, DifferentiableOn ℂ (F i) unitDisk) (hf : DifferentiableOn ℂ f unitDisk)
    (h : TendstoLocallyUniformlyOn (fun i ↦ deriv (F i)) (deriv f) l unitDisk) :
    TendstoLocallyUniformlyOn (fun i ↦ dslope (F i) 0) (dslope f 0) l unitDisk := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  have hz' := mem_unitDisk.mp hz
  obtain ⟨r, hzr, hr⟩ := exists_between hz'
  have hr₀ := (norm_nonneg z).trans_lt hzr
  let K := Metric.closedBall (0 : ℂ) r
  have hK : K ⊆ unitDisk := fun w hw ↦ mem_unitDisk.mpr
    ((by simpa [K, Metric.mem_closedBall, dist_zero_right] using hw : ‖w‖ ≤ r).trans_lt hr)
  have hzK : K ∈ 𝓝[unitDisk] z :=
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds_of_mem
      (by simpa only [Metric.mem_ball, dist_zero_right] using hzr))
  have hU := (tendstoLocallyUniformlyOn_iff_forall_isCompact unitDisk_isOpen).mp h
    K hK (isCompact_closedBall _ _)
  refine ⟨K, hzK, Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hU (ε / 2) (by positivity)] with i hi w hw
  by_cases hw₀ : w = 0
  · subst w
    simp only [dslope_same]
    exact (hi 0 hw).trans (half_lt_self hε)
  have hD (v : ℂ) (hv : v ∈ K) :
      HasDerivAt (fun x ↦ F i x - f x) (deriv (F i) v - deriv f v) v :=
    ((hF i).differentiableAt (unitDisk_isOpen.mem_nhds (hK hv))).hasDerivAt.sub
      ((hf.differentiableAt (unitDisk_isOpen.mem_nhds (hK hv))).hasDerivAt)
  have hbound (v : ℂ) (hv : v ∈ K) : ‖deriv (fun x ↦ F i x - f x) v‖ ≤ ε / 2 := by
    rw [(hD v hv).deriv, ← dist_eq_norm, dist_comm]
    exact (hi v hv).le
  have hzero : (0 : ℂ) ∈ K := Metric.mem_closedBall_self hr₀.le
  have hMV := (convex_closedBall (0 : ℂ) r).norm_image_sub_le_of_norm_deriv_le
    (fun v hv ↦ (hD v hv).differentiableAt) hbound hzero hw
  rw [sub_zero] at hMV
  have hds :
      dslope (F i) 0 w - dslope f 0 w =
        ((F i w - f w) - (F i 0 - f 0)) / w := by
    simp only [dslope_of_ne _ hw₀, slope_def_field, sub_zero]
    ring
  rw [dist_comm, dist_eq_norm, hds, norm_div]
  exact ((div_le_iff₀ (norm_pos_iff.mpr hw₀)).mpr hMV).trans_lt (half_lt_self hε)

private theorem locallyUniform_dslope {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, DifferentiableOn ℂ (F i) unitDisk) (hf : DifferentiableOn ℂ f unitDisk)
    (h : TendstoLocallyUniformlyOn F f l unitDisk) :
    TendstoLocallyUniformlyOn (fun i ↦ dslope (F i) 0) (dslope f 0) l unitDisk :=
  locallyUniform_dslope_of_deriv hF hf (h.deriv (Eventually.of_forall hF) unitDisk_isOpen)

private theorem locallyUniform_of_deriv_of_zero {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, DifferentiableOn ℂ (F i) unitDisk) (hf : DifferentiableOn ℂ f unitDisk)
    (hF₀ : ∀ i, F i 0 = 0) (hf₀ : f 0 = 0)
    (h : TendstoLocallyUniformlyOn (fun i ↦ deriv (F i)) (deriv f) l unitDisk) :
    TendstoLocallyUniformlyOn F f l unitDisk := by
  have hds := (locallyUniform_fixed (l := l) (fun z ↦ z)).fun_mul₀
    (locallyUniform_dslope_of_deriv hF hf h) continuous_id.continuousOn
    (dslope_holomorphic hf).continuousOn
  refine (hds.congr (fun i z _ ↦ ?_)).congr_right (fun z _ ↦ ?_)
  · simpa only [sub_zero, smul_eq_mul, hF₀ i] using sub_smul_dslope (F i) (0 : ℂ) z
  · simpa only [sub_zero, smul_eq_mul, hf₀] using sub_smul_dslope f (0 : ℂ) z

private theorem hasDerivAt_timeSlope {F : ℝ → ℂ → ℂ}
    (hF : ∀ t, DifferentiableOn ℂ (F t) unitDisk) (u t : ℝ) {z : ℂ} (hz : z ∈ unitDisk) :
    HasDerivAt (fun w ↦ slope (fun s ↦ F s w) u t)
      (slope (fun s ↦ deriv (F s) z) u t) z := by
  simp only [slope_def_module, Complex.real_smul]
  exact (((hF t).differentiableAt (unitDisk_isOpen.mem_nhds hz)).hasDerivAt.sub
    ((hF u).differentiableAt (unitDisk_isOpen.mem_nhds hz)).hasDerivAt).const_mul _

private theorem timeSlope_holomorphic {F : ℝ → ℂ → ℂ}
    (hF : ∀ t, DifferentiableOn ℂ (F t) unitDisk) (u t : ℝ) :
    DifferentiableOn ℂ (fun z ↦ slope (fun s ↦ F s z) u t) unitDisk :=
  fun _ hz ↦ (hasDerivAt_timeSlope hF u t hz).differentiableAt.differentiableWithinAt

/-- Time difference quotients of the normalized logarithm converge locally uniformly
when those of the underlying maps do. -/
theorem tendstoLocallyUniformlyOn_slope_normalizedLogarithm {F : ℝ → ℂ → ℂ}
    (hF : ∀ t, NormalizedUnivalent (F t)) {u : ℝ} {V : ℂ → ℂ}
    (hV : DifferentiableOn ℂ V unitDisk)
    (hS : TendstoLocallyUniformlyOn (fun t z ↦ slope (fun s ↦ F s z) u t)
      V (𝓝[≠] u) unitDisk) :
    TendstoLocallyUniformlyOn
      (fun t z ↦ slope (fun s ↦ normalizedLogarithm (hF s) z) u t)
      (fun z ↦ dslope V 0 z / dslope (F u) 0 z) (𝓝[≠] u) unitDisk := by
  let P (t : ℝ) := dslope (F t) 0
  let W := dslope V 0
  let A (t : ℝ) (z : ℂ) := slope (fun s ↦ P s z) u t
  let L (t : ℝ) := normalizedLogarithm (hF t)
  let B (t : ℝ) (z : ℂ) := slope (fun s ↦ L s z) u t
  let Q (z : ℂ) := W z / P u z
  have hP (t : ℝ) := (hF t).dslope_holomorphic
  have hP₀ (t : ℝ) : P t 0 = 1 := by simp [P, dslope_same, (hF t).deriv_zero]
  have hPNe (t : ℝ) (z : ℂ) (hz : z ∈ unitDisk) : P t z ≠ 0 :=
    (hF t).dslope_ne_zero hz
  have hW := dslope_holomorphic hV
  have hA := timeSlope_holomorphic hP u
  have hL (t : ℝ) := normalizedLogarithm_holomorphic (hF t)
  have hB := timeSlope_holomorphic hL u
  have hQ : DifferentiableOn ℂ Q unitDisk := hW.div (hP u) (hPNe u)
  have hAT : TendstoLocallyUniformlyOn A W (𝓝[≠] u) unitDisk := by
    refine (locallyUniform_dslope (timeSlope_holomorphic (fun t ↦ (hF t).holomorphic) u)
      hV hS).congr (fun t z hz ↦ ?_)
    by_cases hz₀ : z = 0
    · subst z
      simpa only [A, P, dslope_same] using
        (hasDerivAt_timeSlope (fun t ↦ (hF t).holomorphic) u t zero_mem_unitDisk).deriv
    · simp only [A, P, dslope_of_ne _ hz₀, slope_def_module, Complex.real_smul,
        smul_eq_mul, sub_zero]
      ring
  have hA₀ (t : ℝ) : A t 0 = 0 := by simp [A, hP₀, slope_def_module]
  have hW₀ : W 0 = 0 := by
    have ht := hAT.tendsto_at zero_mem_unitDisk
    simp only [hA₀] at ht
    exact (tendsto_nhds_unique ht tendsto_const_nhds)
  have hQ₀ : Q 0 = 0 := by simp [Q, hW₀]
  have hPconv : TendstoLocallyUniformlyOn P (P u) (𝓝[≠] u) unitDisk := by
    let D (t : ℝ) : ℂ := ((t - u : ℝ) : ℂ)
    have hD : Continuous D := by fun_prop
    have hD₀ : Tendsto D (𝓝[≠] u) (𝓝 0) := by
      simpa [D] using (hD.continuousAt (x := u)).tendsto.mono_left nhdsWithin_le_nhds
    have hDt : TendstoLocallyUniformlyOn (fun t (_ : ℂ) ↦ D t) (fun _ ↦ 0)
        (𝓝[≠] u) unitDisk :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact unitDisk_isOpen).mpr
        (fun K _ _ ↦ hD₀.tendstoUniformlyOn_const K)
    have h := (hDt.fun_mul₀ hAT continuousOn_const hW.continuousOn).fun_add
      (locallyUniform_fixed (l := 𝓝[≠] u) (P u))
    refine (h.congr (fun t z _ ↦ ?_)).congr_right (fun z _ ↦ by simp)
    have hsub := sub_smul_slope (fun s ↦ P s z) u t
    rw [Complex.real_smul, vsub_eq_sub] at hsub
    change D t * A t z + P u z = P t z
    rw [show D t * A t z = P t z - P u z from hsub, sub_add_cancel]
  have hPDer (t : ℝ) := (hP t).deriv unitDisk_isOpen
  have hWDer := hW.deriv unitDisk_isOpen
  have hADer := hAT.deriv (Eventually.of_forall hA) unitDisk_isOpen
  have hDerNumer := (hADer.fun_mul₀ (locallyUniform_fixed (P u))
      hWDer.continuousOn (hP u).continuousOn).fun_sub
    ((locallyUniform_fixed (deriv (P u))).fun_mul₀ hAT
      (hPDer u).continuousOn hW.continuousOn)
  have hDerDenom := hPconv.fun_mul₀ (locallyUniform_fixed (P u))
    (hP u).continuousOn (hP u).continuousOn
  have hDer := hDerNumer.fun_div₀ hDerDenom
    ((hWDer.continuousOn.mul (hP u).continuousOn).sub
      ((hPDer u).continuousOn.mul hW.continuousOn))
    ((hP u).continuousOn.mul (hP u).continuousOn)
    (fun z hz ↦ mul_ne_zero (hPNe u z hz) (hPNe u z hz))
  refine locallyUniform_of_deriv_of_zero hB hQ ?_ hQ₀ ?_
  · intro t
    simp [slope_def_module]
  · refine (hDer.congr (fun t z hz ↦ ?_)).congr_right (fun z hz ↦ ?_)
    · change (deriv (A t) z * P u z - deriv (P u) z * A t z) / (P t z * P u z) =
        deriv (B t) z
      rw [(hasDerivAt_timeSlope hL u t hz).deriv, (hasDerivAt_timeSlope hP u t hz).deriv]
      simp only [A, slope_def_module, Complex.real_smul]
      rw [(hasDerivAt_normalizedLogarithm (hF t) hz).deriv,
        (hasDerivAt_normalizedLogarithm (hF u) hz).deriv]
      have ht := hPNe t z hz
      have hu := hPNe u z hz
      change _ = ↑((t - u)⁻¹) * (deriv (P t) z / P t z - deriv (P u) z / P u z)
      field_simp <;> ring
    · have hDW : HasDerivAt W (deriv W z) z :=
        (hW.differentiableAt (unitDisk_isOpen.mem_nhds hz)).hasDerivAt
      have hDP : HasDerivAt (P u) (deriv (P u) z) z :=
        ((hP u).differentiableAt (unitDisk_isOpen.mem_nhds hz)).hasDerivAt
      change _ = deriv (fun w ↦ W w / P u w) z
      rw [(hDW.fun_div hDP (hPNe u z hz)).deriv, pow_two, mul_comm (W z) (deriv (P u) z)]

/-- In a radial normalized map equation, the logarithmic velocity is obtained
by dividing the map velocity by the normalized map and filling in the origin. -/
theorem tendstoLocallyUniformlyOn_radial_slope_normalizedLogarithm {F : ℝ → ℂ → ℂ}
    (hF : ∀ t, NormalizedUnivalent (F t)) {u : ℝ} {D : ℂ → ℂ}
    (hD : DifferentiableOn ℂ D unitDisk)
    (h : TendstoLocallyUniformlyOn (fun t z ↦ slope (fun s ↦ F s z) u t)
      (fun z ↦ z * deriv (F u) z * D z - F u z) (𝓝[≠] u) unitDisk) :
    TendstoLocallyUniformlyOn
      (fun t z ↦ slope (fun s ↦ normalizedLogarithm (hF s) z) u t)
      (fun z ↦ (1 + z * deriv (normalizedLogarithm (hF u)) z) * D z - 1)
      (𝓝[≠] u) unitDisk := by
  let P := dslope (F u) 0
  let V (z : ℂ) := z * deriv (F u) z * D z - F u z
  let U (z : ℂ) := deriv (F u) z * D z - P z
  have hP := (hF u).dslope_holomorphic
  have hFd := (hF u).holomorphic.deriv unitDisk_isOpen
  have hMul : (fun z ↦ z * P z) = F u := funext (hF u).mul_dslope
  have hV : DifferentiableOn ℂ V unitDisk :=
    ((differentiableOn_id.fun_mul hFd).fun_mul hD).fun_sub (hF u).holomorphic
  have hU : DifferentiableOn ℂ U unitDisk := (hFd.fun_mul hD).fun_sub hP
  have hfactor : V = fun z ↦ z * U z := by
    funext z
    change z * deriv (F u) z * D z - F u z = z * (deriv (F u) z * D z - P z)
    rw [← congrFun hMul z]
    ring
  have hfilled (z : ℂ) (hz : z ∈ unitDisk) : dslope V 0 z = U z := by
    by_cases hz₀ : z = 0
    · subst z
      rw [dslope_same, hfactor]
      have hD₀ := (hasDerivAt_id (0 : ℂ)).fun_mul
        (hU.differentiableAt (unitDisk_isOpen.mem_nhds zero_mem_unitDisk)).hasDerivAt
      simpa using hD₀.deriv
    · rw [dslope_of_ne _ hz₀, slope_def_field, hfactor]
      simp [hz₀, mul_div_cancel_left₀]
  refine (tendstoLocallyUniformlyOn_slope_normalizedLogarithm hF hV h).congr_right ?_
  intro z hz
  change dslope V 0 z / P z =
    (1 + z * deriv (normalizedLogarithm (hF u)) z) * D z - 1
  rw [hfilled z hz, (hasDerivAt_normalizedLogarithm (hF u) hz).deriv]
  have hDP : HasDerivAt P (deriv P z) z :=
    (hP.differentiableAt (unitDisk_isOpen.mem_nhds hz)).hasDerivAt
  have hFder : deriv (F u) z = P z + z * deriv P z := by
    simpa only [hMul, one_mul, id_eq] using ((hasDerivAt_id z).fun_mul hDP).deriv
  have hp₀ : P z ≠ 0 := (hF u).dslope_ne_zero hz
  change (deriv (F u) z * D z - P z) / P z =
    (1 + z * (deriv P z / P z)) * D z - 1
  rw [hFder]
  field_simp <;> ring


end Zalcman
