/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Basic
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Radial dilations of normalized univalent functions

For a positive dilation radius, the normalized dilation is holomorphic and
injective on the disk of reciprocal radius. For a radius below one, its
restriction to the unit circle is an embedding onto the frontier of the
image of the disk. The dilations converge locally uniformly as the radius
approaches one.
-/

@[expose] public section

namespace Zalcman

open Filter Set
open scoped Topology

/-- The dilation given by `z ↦ f (r * z) / r`. -/
noncomputable def normalizedDilation (r : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((r : ℂ) * z) / (r : ℂ)

private lemma mapsTo_dilation_disk {r : ℝ} (hr : 0 < r) :
    MapsTo (fun z : ℂ ↦ (r : ℂ) * z) (Metric.ball 0 r⁻¹) unitDisk := by
  intro z hz
  rw [mem_unitDisk, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hz' : ‖z‖ < r⁻¹ := by simpa [Metric.mem_ball, dist_zero_right] using hz
  calc
    r * ‖z‖ < r * r⁻¹ := mul_lt_mul_of_pos_left hz' hr
    _ = 1 := mul_inv_cancel₀ hr.ne'

/-- The original function's disk of holomorphic injectivity becomes the disk of radius `1 / r`. -/
theorem NormalizedUnivalent.normalizedDilation_on_ball {f : ℂ → ℂ}
    (hf : NormalizedUnivalent f) {r : ℝ} (hr : 0 < r) :
    DifferentiableOn ℂ (normalizedDilation r f) (Metric.ball 0 r⁻¹) ∧
      InjOn (normalizedDilation r f) (Metric.ball 0 r⁻¹) := by
  let s : Set ℂ := Metric.ball 0 r⁻¹
  have hmul : DifferentiableOn ℂ (fun z : ℂ ↦ (r : ℂ) * z) s :=
    (differentiableOn_id : DifferentiableOn ℂ (fun z : ℂ ↦ z) s).const_mul (r : ℂ)
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨(hf.holomorphic.comp hmul (mapsTo_dilation_disk hr)).div_const _, ?_⟩
  intro z hz w hw he
  apply mul_left_cancel₀ hrC
  apply hf.injective (mapsTo_dilation_disk hr hz) (mapsTo_dilation_disk hr hw)
  exact (div_left_inj' hrC).mp he

/-- Dilating by a radius in `(0, 1]` preserves membership in the normalized univalent class. -/
theorem NormalizedUnivalent.normalizedDilation {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) : NormalizedUnivalent (Zalcman.normalizedDilation r f) := by
  have hle : (1 : ℝ) ≤ r⁻¹ := one_le_inv_iff₀.mpr ⟨hr, hr₁⟩
  have hsub : unitDisk ⊆ Metric.ball 0 r⁻¹ := Metric.ball_subset_ball hle
  have h := hf.normalizedDilation_on_ball hr
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨h.1.mono hsub, h.2.mono hsub, by simp [Zalcman.normalizedDilation, hf.map_zero], ?_⟩
  change deriv (fun z : ℂ ↦ f ((r : ℂ) * z) / (r : ℂ)) 0 = 1
  rw [deriv_div_const, deriv_comp_mul_left, smul_eq_mul, mul_zero, hf.deriv_zero, mul_one,
    div_self hrC]

private lemma closedUnitDisk_subset_dilationDisk {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball 0 r⁻¹ :=
  Metric.closedBall_subset_ball (one_lt_inv_iff₀.mpr ⟨hr, hr₁⟩)

/-- The frontier of the image of the open disk is the image of the unit circle. -/
theorem NormalizedUnivalent.frontier_image_normalizedDilation {f : ℂ → ℂ}
    (hf : NormalizedUnivalent f) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    frontier (Zalcman.normalizedDilation r f '' unitDisk) =
      Zalcman.normalizedDilation r f '' Metric.sphere (0 : ℂ) 1 := by
  let g := Zalcman.normalizedDilation r f
  let K : Set ℂ := Metric.closedBall 0 1
  have hDomain : K ⊆ Metric.ball 0 r⁻¹ := closedUnitDisk_subset_dilationDisk hr hr₁
  have hDisk := hf.normalizedDilation_on_ball hr
  have hKcont : ContinuousOn g K := hDisk.1.continuousOn.mono hDomain
  have hKinj : InjOn g K := hDisk.2.mono hDomain
  have hUnitK : unitDisk ⊆ K := Metric.ball_subset_closedBall
  have hClosureUnit : closure unitDisk = K := closure_ball (0 : ℂ) one_ne_zero
  have hClosure : closure (g '' unitDisk) = g '' K := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono hUnitK)
        ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hKcont).isClosed
    · have h := hKcont
      rw [← hClosureUnit] at h ⊢
      exact h.image_closure
  have hNorm := hf.normalizedDilation hr hr₁.le
  have hOpen : IsOpen (g '' unitDisk) := by
    have h := (hNorm.holomorphic.analyticOnNhd Metric.isOpen_ball).is_constant_or_isOpen
      (convex_ball (0 : ℂ) 1).isPreconnected
    rcases h with ⟨c, hc⟩ | hopen
    · exfalso
      have hm : (1 / 2 : ℂ) ∈ unitDisk := by norm_num [mem_unitDisk, norm_div]
      have he := hNorm.injective zero_mem_unitDisk hm
        ((hc 0 zero_mem_unitDisk).trans (hc _ hm).symm)
      norm_num at he
    · exact hopen _ Subset.rfl Metric.isOpen_ball
  calc
    frontier (g '' unitDisk) = g '' K \ g '' unitDisk := by
      rw [frontier, hClosure, hOpen.interior_eq]
    _ = g '' (K \ unitDisk) := (hKinj.image_sdiff_subset hUnitK).symm
    _ = g '' Metric.sphere (0 : ℂ) 1 := by
      change g '' (Metric.closedBall (0 : ℂ) 1 \ Metric.ball 0 1) = _
      rw [Metric.closedBall_sdiff_ball]

/-- The image of the unit circle under a dilation is an embedded circle. -/
theorem NormalizedUnivalent.isEmbedding_normalizedDilation_unitCircle {f : ℂ → ℂ}
    (hf : NormalizedUnivalent f) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    Topology.IsEmbedding (fun z : Metric.sphere (0 : ℂ) 1 ↦ Zalcman.normalizedDilation r f z) := by
  let S : Set ℂ := Metric.sphere 0 1
  let g : S → ℂ := fun z ↦ Zalcman.normalizedDilation r f z
  have hsub : S ⊆ Metric.ball 0 r⁻¹ := Metric.sphere_subset_closedBall.trans
    (closedUnitDisk_subset_dilationDisk hr hr₁)
  have h := hf.normalizedDilation_on_ball hr
  have hc : Continuous g := continuousOn_iff_continuous_restrict.mp (h.1.continuousOn.mono hsub)
  have hi : Function.Injective g := fun z w he ↦ Subtype.ext (h.2 (hsub z.property) (hsub w.property) he)
  letI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : ℂ) 1)
  exact (hc.isClosedEmbedding hi).isEmbedding

/-- A continuous function on the disk is the locally uniform limit of its normalized dilations. -/
theorem tendstoLocallyUniformlyOn_normalizedDilation {f : ℂ → ℂ}
    (hf : ContinuousOn f unitDisk) :
    TendstoLocallyUniformlyOn (fun r : ℝ ↦ normalizedDilation r f) f (𝓝[<] (1 : ℝ)) unitDisk := by
  refine (Metric.isOpen_ball.tendstoLocallyUniformlyOn_iff_forall_tendsto).mpr ?_
  intro z hz
  refine tendsto_uniformity_iff_dist_tendsto_zero.mpr ?_
  have hcont := hf.continuousAt (Metric.isOpen_ball.mem_nhds hz)
  have hF : ContinuousAt (fun p : ℝ × ℂ ↦ f p.2) (1, z) :=
    hcont.comp continuous_snd.continuousAt
  have hR : Continuous (fun p : ℝ × ℂ ↦ (p.1 : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_fst
  have hmul : Continuous (fun p : ℝ × ℂ ↦ (p.1 : ℂ) * p.2) := hR.mul continuous_snd
  have hcomp : ContinuousAt (fun p : ℝ × ℂ ↦ f ((p.1 : ℂ) * p.2)) (1, z) :=
    hcont.comp_of_eq hmul.continuousAt (by simp)
  have hD : ContinuousAt (fun p : ℝ × ℂ ↦ normalizedDilation p.1 f p.2) (1, z) :=
    hcomp.div hR.continuousAt (by simp)
  have hT := (hF.tendsto.dist hD.tendsto).mono_left
    (show (𝓝[<] (1 : ℝ)) ×ˢ 𝓝 z ≤ 𝓝 ((1 : ℝ), z) by
      rw [nhds_prod_eq]
      exact Filter.prod_mono_left _ nhdsWithin_le_nhds)
  simpa [normalizedDilation] using hT

end Zalcman
