/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Upstream.Crouzeix.Riemann
import all Mathlib.Analysis.Complex.RiemannMapping
import Mathlib.Analysis.Calculus.Deriv.Comp
import Zalcman.Upstream.Crouzeix.DiskAutomorphism

/-!
# The Riemann mapping theorem for proper domains

The preliminary disk embedding from Mathlib supplies a seed without a
boundedness assumption. We normalize it by a disk automorphism and use the
same derivative extremal and omitted-point argument as in the bounded case.
-/

public section

namespace OAI.CrouzeixHilbert.Conformal

open Function Metric Set
open scoped ComplexConjugate

/-- A proper simply connected open subset of the plane maps biholomorphically onto the disk. -/
theorem riemann_mapping_proper {U : Set ℂ} (hU : IsOpen U) (hproper : U ≠ univ)
    (hc : IsSimplyConnected U) {a : ℂ} (ha : a ∈ U) :
    ∃ f, DiskEmbedding U a f ∧ deriv f a ≠ 0 ∧ BijOn f U (ball 0 1) := by
  obtain ⟨q, hqmap, hqinj, hqder⟩ :=
    Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero hU hc hproper
  have hqnorm (z : ℂ) (hz : z ∈ U) : ‖q z‖ < 1 := mem_ball_zero_iff.mp (hqmap hz)
  let w := q a
  let g := diskShift w ∘ q
  have hw : ‖w‖ < 1 := hqnorm a ha
  have hgd (z : ℂ) (hz : z ∈ U) :
      HasDerivAt g ((1 - conj w * w) / (1 - conj w * q z) ^ 2 * deriv q z) z :=
    (hasDerivAt_diskShift hw (hqnorm z hz).le).comp z
      (differentiableAt_of_deriv_ne_zero (hqder z hz)).hasDerivAt
  have hg : DiskEmbedding U a g :=
    ⟨fun z hz ↦ (hgd z hz).differentiableAt.differentiableWithinAt,
      (diskShift_injOn hw).comp hqinj (fun z hz ↦ mem_closedBall_zero_iff.mpr (hqnorm z hz).le),
      fun z hz ↦ diskShift_into_disk hw (hqnorm z hz), diskShift_self w⟩
  have hgder : deriv g a ≠ 0 := by
    rw [(hgd a ha).deriv]
    exact mul_ne_zero
      (div_ne_zero (diskShift_den_ne hw hw.le) (pow_ne_zero 2 (diskShift_den_ne hw hw.le)))
      (hqder a ha)
  obtain ⟨f, hf, hfd, hext⟩ := exists_extremal hU hc.isPathConnected.isConnected.isPreconnected ha hg hgder
  refine ⟨f, hf, hfd, ⟨fun z hz ↦ mem_ball_zero_iff.mpr (hf.into_disk z hz), hf.injective, ?_⟩⟩
  intro y hy
  by_contra hyo
  obtain ⟨ψ, hψ, hgt⟩ := exists_improved_of_omitted hU hc ha hf hfd (mem_ball_zero_iff.mp hy) hyo
  exact (hext ψ hψ).not_gt hgt

end OAI.CrouzeixHilbert.Conformal
