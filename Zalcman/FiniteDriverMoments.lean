/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.PositiveRealMoments
public import Zalcman.UnitMomentHull
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Ring

/-!
# Finite moments of positive-real functions

The real part on an interior circle is a probability density after normalizing
arc length. Its moment vector belongs to the closed convex hull of the unit
circle moment curve, and the limit as the radius grows to one has the same property.
-/

@[expose] public section

namespace Zalcman

open Complex Filter MeasureTheory Real Set
open scoped ENNReal Real Topology

private theorem scaled_coeff_mem_closedUnitMomentHull {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisk) (h₀ : f 0 = 1)
    (hRe : ∀ z ∈ unitDisk, 0 ≤ (f z).re) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) (M : ℕ) :
    (fun k : Fin M ↦ (r : ℂ) ^ (k.val + 1) * (coeff f (k.val + 1) / 2)) ∈ closedUnitMomentHull M := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  let a : ℝ := (2 * π)⁻¹
  let w : ℝ → ℝ := fun t ↦ a * (f (circleMap 0 r t)).re
  have hsub : Metric.closedBall (0 : ℂ) r ⊆ unitDisk := Metric.closedBall_subset_ball hr₁
  have hfd : DifferentiableOn ℂ f (Metric.closedBall 0 r) := hf.mono hsub
  have hci (t : ℝ) : circleMap 0 r t ∈ Metric.closedBall (0 : ℂ) r :=
    Metric.sphere_subset_closedBall (circleMap_mem_sphere _ hr.le _)
  have hc : Continuous (f ∘ circleMap 0 r) :=
    hfd.continuousOn.comp_continuous (continuous_circleMap _ _) hci
  have hwc : Continuous w := continuous_const.mul (Complex.continuous_re.comp hc)
  have hw₀ (t : ℝ) : 0 ≤ w t := mul_nonneg (inv_nonneg.mpr (by positivity)) (hRe _ (hsub (hci t)))
  have hwI : Integrable w μ :=
    (hwc.intervalIntegrable 0 (2 * π)).1
  have hwMass : ∫ t, w t ∂μ = 1 := by
    have hí := circleAverage_re_eq_center hr.le hfd
    rw [h₀, Complex.one_re, circleAverage_def, intervalIntegral.integral_of_le (by positivity),
      smul_eq_mul] at hí
    simpa only [w, integral_const_mul, a, μ] using hí
  let ρ : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (w t)
  let ν := μ.withDensity ρ
  have hρ : Measurable ρ := hwc.measurable.ennreal_ofReal
  have hprob : IsProbabilityMeasure ν := by
    constructor
    change μ.withDensity ρ univ = _
    rw [withDensity_apply ρ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hwI (.of_forall hw₀), hwMass, ENNReal.ofReal_one]
  letI := hprob
  let ζ := fun t : ℝ ↦ (r : ℂ) / circleMap 0 r t
  let g := fun t : ℝ ↦ unitMomentCurve M (ζ t)
  have hζ (t : ℝ) : ‖ζ t‖ = 1 := by
    dsimp only [ζ]
    rw [norm_div, Complex.norm_of_nonneg hr.le, norm_circleMap_zero, abs_of_nonneg hr.le,
      div_self hr.ne']
  have hcircleNe (t : ℝ) : circleMap 0 r t ≠ 0 := by
    apply norm_pos_iff.mp
    simpa only [norm_circleMap_zero, abs_of_nonneg hr.le] using hr
  have hζcont : Continuous ζ := continuous_const.div (continuous_circleMap _ _) hcircleNe
  have hgc : Continuous g := continuous_pi fun k ↦ hζcont.pow (k.val + 1)
  have hgI : Integrable g ν := Integrable.of_bound hgc.aestronglyMeasurable 1 (.of_forall fun t ↦ by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro k
    simp only [g, unitMomentCurve, norm_pow, hζ, one_pow, le_refl])
  have hgHull : ∀ᵐ t ∂ν, g t ∈ closedUnitMomentHull M := by
    refine .of_forall fun t ↦ subset_closure (subset_convexHull ℝ _ ?_)
    refine ⟨ζ t, ?_, rfl⟩
    simpa only [Metric.mem_sphere, dist_zero_right] using hζ t
  have hhull := (convex_convexHull ℝ _).closure.integral_mem isClosed_closure hgHull hgI
  have hmeq (k : Fin M) : (∫ t, g t ∂ν) k = (r : ℂ) ^ (k.val + 1) * (coeff f (k.val + 1) / 2) := by
    let L : (Fin M → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj k
    change L (∫ t, g t ∂ν) = _
    rw [← L.integral_comp_comm hgI]
    have hρFin : ∀ᵐ t ∂μ, ρ t < ∞ := .of_forall fun _ ↦ ENNReal.ofReal_lt_top
    rw [show ν = μ.withDensity ρ from rfl,
      integral_withDensity_eq_integral_toReal_smul hρ hρFin]
    simp_rw [show ∀ t, (ρ t).toReal = w t from fun t ↦ ENNReal.toReal_ofReal (hw₀ t)]
    let G : ℂ → ℂ := fun z ↦ ((r : ℂ) / z) ^ (k.val + 1) * ((f z).re : ℂ)
    have hG : (∫ t, w t • L (g t) ∂μ) = circleAverage G 0 r := by
      rw [circleAverage_def, intervalIntegral.integral_of_le (by positivity)]
      change (∫ t, w t • L (g t) ∂μ) = a • ∫ t, G (circleMap 0 r t) ∂μ
      rw [← integral_smul]
      apply integral_congr_ae
      refine .of_forall fun t ↦ ?_
      change (a * (f (circleMap 0 r t)).re) • ζ t ^ (k.val + 1) =
        a • (ζ t ^ (k.val + 1) * ((f (circleMap 0 r t)).re : ℂ))
      simp only [Complex.real_smul, Complex.ofReal_mul]
      ring
    rw [hG]
    have hG' : G = fun z ↦ (r : ℂ) ^ (k.val + 1) • (z⁻¹ ^ (k.val + 1) * ((f z).re : ℂ)) := by
      funext z
      simp only [G, smul_eq_mul, div_eq_mul_inv, mul_pow, mul_assoc]
    rw [hG', circleAverage_fun_smul, circleAverage_re_inv_pow_succ hr hfd, smul_eq_mul]
  exact (funext hmeq) ▸ hhull

/-- The first finitely many positive Taylor coefficients, divided by two, are
limits of convex combinations of the corresponding powers of unit points. -/
theorem coeff_mem_closedUnitMomentHull {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisk)
    (h₀ : f 0 = 1) (hRe : ∀ z ∈ unitDisk, 0 ≤ (f z).re) (M : ℕ) :
    (fun k : Fin M ↦ coeff f (k.val + 1) / 2) ∈ closedUnitMomentHull M := by
  let P := fun (r : ℝ) (k : Fin M) ↦ (r : ℂ) ^ (k.val + 1) * (coeff f (k.val + 1) / 2)
  have hPc : Continuous P := by
    apply continuous_pi
    intro k
    dsimp only [P]
    fun_prop
  have hlim : Tendsto P (𝓝[<] (1 : ℝ)) (𝓝 (P 1)) := (hPc.tendsto _).mono_left nhdsWithin_le_nhds
  have hMem : ∀ᶠ r in 𝓝[<] (1 : ℝ), P r ∈ closedUnitMomentHull M := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one))] with r hlt hr
    exact scaled_coeff_mem_closedUnitMomentHull hf h₀ hRe hr hlt M
  have hClosed : IsClosed (closedUnitMomentHull M) := isClosed_closure
  simpa only [P, Complex.ofReal_one, one_pow, one_mul] using hClosed.mem_of_tendsto hlim hMem

end Zalcman
