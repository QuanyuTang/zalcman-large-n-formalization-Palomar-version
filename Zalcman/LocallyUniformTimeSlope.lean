/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Tactic.Linarith

/-!
# Locally uniform time slopes

Joint continuity of the time derivative controls the difference quotients
uniformly on compact subsets of the spatial domain.
-/

public section

namespace Zalcman

open Filter Set
open scoped Topology

/-- A jointly continuous real-time derivative is the locally uniform slope limit. -/
theorem tendstoLocallyUniformlyOn_slope_of_continuous_time_deriv
    {F G : ℝ → ℂ → ℂ} {I : Set ℝ} {D : Set ℂ} {u : ℝ}
    (hI : IsOpen I) (hu : u ∈ I) (hD : IsOpen D)
    (hG : ContinuousOn (fun p : ℝ × ℂ ↦ G p.1 p.2) (I ×ˢ D))
    (hTime : ∀ t ∈ I, ∀ z ∈ D, HasDerivAt (fun s ↦ F s z) (G t z) t) :
    TendstoLocallyUniformlyOn (fun t z ↦ slope (fun s ↦ F s z) u t)
      (G u) (𝓝[≠] u) D := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hD]
  intro K hKD hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨r, hr, hrI⟩ := Metric.isOpen_iff.mp hI u hu
  let J := Icc (u - r / 2) (u + r / 2)
  have hJI : J ⊆ I := by
    intro t ht
    apply hrI
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    change u - r / 2 ≤ t ∧ t ≤ u + r / 2 at ht
    constructor <;> linarith [ht.1, ht.2]
  have huJ : u ∈ J := by
    change u - r / 2 ≤ u ∧ u ≤ u + r / 2
    constructor <;> linarith
  have hJ : IsCompact J := isCompact_Icc
  have hCont := hG.mono (show J ×ˢ K ⊆ I ×ˢ D from fun _ hp ↦ ⟨hJI hp.1, hKD hp.2⟩)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    ((hJ.prod hK).uniformContinuousOn_of_continuous hCont) (ε / 2) (by linarith)
  let η := min (r / 2) (δ / 2)
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  let L := Icc (u - η) (u + η)
  have hηr : η ≤ r / 2 := min_le_left _ _
  have hηδ : η < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hLJ : L ⊆ J := by
    intro t ht
    change u - η ≤ t ∧ t ≤ u + η at ht
    change u - r / 2 ≤ t ∧ t ≤ u + r / 2
    constructor <;> linarith [ht.1, ht.2]
  have huL : u ∈ L := by
    change u - η ≤ u ∧ u ≤ u + η
    constructor <;> linarith
  have hnear : ∀ᶠ t in 𝓝[≠] u, t ∈ Metric.ball u η :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds u hη)
  have hne : ∀ᶠ t in 𝓝[≠] u, t ≠ u := self_mem_nhdsWithin
  filter_upwards [hnear, hne] with t ht htu z hz
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
  have htL : t ∈ L := by
    change u - η ≤ t ∧ t ≤ u + η
    constructor <;> linarith [ht.1, ht.2]
  let A := fun v : ℝ ↦ F v z - (v - u) • G u z
  have hd (v : ℝ) (hv : v ∈ L) : HasDerivWithinAt A (G v z - G u z) L v := by
    have hlin := ((hasDerivAt_id v).sub_const u).smul_const (G u z)
    exact ((hTime v (hJI (hLJ hv)) z (hKD hz)).sub
      (by simpa only [id, one_smul] using hlin)).hasDerivWithinAt
  have hb (v : ℝ) (hv : v ∈ L) : ‖G v z - G u z‖ ≤ ε / 2 := by
    have hvu : dist (v, z) (u, z) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq]
      change u - η ≤ v ∧ v ≤ u + η at hv
      exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩) hηδ
    have h := hmod (v, z) ⟨hLJ hv, hz⟩ (u, z) ⟨huJ, hz⟩ hvu
    exact (by simpa only [dist_eq_norm] using h : ‖G v z - G u z‖ < ε / 2).le
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (show Convex ℝ L from convex_Icc _ _) huL htL
  have hdiff : slope (fun s ↦ F s z) u t - G u z = (t - u)⁻¹ • (A t - A u) := by
    simp only [slope_def_module, A, sub_self, zero_smul, sub_zero]
    rw [sub_right_comm (F t z)]
    simp only [smul_sub, inv_smul_smul₀ (sub_ne_zero.mpr htu)]
  rw [dist_comm, dist_eq_norm, hdiff, norm_smul, norm_inv]
  calc
    ‖t - u‖⁻¹ * ‖A t - A u‖ ≤ ‖t - u‖⁻¹ * (ε / 2 * ‖t - u‖) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (norm_nonneg _))
    _ = ε / 2 := by
      rw [mul_left_comm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr htu)), mul_one]
    _ < ε := by linarith

end Zalcman
