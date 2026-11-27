/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.Order.OrderClosed

/-!
# Exhaustion by expanding images of disks

A plane homeomorphism fixing the origin sends expanding disks to proper simply
connected domains. The two one-sided limits follow from the limits of the radii.
-/

@[expose] public section

namespace Zalcman

open Set Filter
open scoped Topology

def expandingHomeomorphDomain (e : ℂ ≃ₜ ℂ) (u : ℝ) : Set ℂ := e '' Metric.ball 0 (1 + u)

theorem expandingHomeomorphDomain_isOpen (e : ℂ ≃ₜ ℂ) (u : ℝ) :
    IsOpen (expandingHomeomorphDomain e u) := e.isOpenMap _ Metric.isOpen_ball

theorem expandingHomeomorphDomain_isSimplyConnected (e : ℂ ≃ₜ ℂ) {u : ℝ} (hu : 0 ≤ u) :
    IsSimplyConnected (expandingHomeomorphDomain e u) := by
  have hr : 0 < 1 + u := zero_lt_one.trans_le (le_add_of_nonneg_right hu)
  have : ContractibleSpace (Metric.ball (0 : ℂ) (1 + u)) :=
    (convex_ball _ _).contractibleSpace ⟨0, Metric.mem_ball_self hr⟩
  have hsc : SimplyConnectedSpace (Metric.ball (0 : ℂ) (1 + u)) := inferInstance
  exact e.isSimplyConnected_image.mpr hsc

theorem expandingHomeomorphDomain_zero_mem {e : ℂ ≃ₜ ℂ} (he : e 0 = 0) {u : ℝ} (hu : 0 ≤ u) :
    0 ∈ expandingHomeomorphDomain e u :=
  ⟨0, Metric.mem_ball_self (zero_lt_one.trans_le (le_add_of_nonneg_right hu)), he⟩

theorem expandingHomeomorphDomain_ne_univ (e : ℂ ≃ₜ ℂ) {u : ℝ} (hu : 0 ≤ u) :
    expandingHomeomorphDomain e u ≠ univ := by
  intro h
  let z : ℂ := ((1 + u : ℝ) : ℂ)
  have hz : z ∈ Metric.ball (0 : ℂ) (1 + u) := by
    have hh : e z ∈ expandingHomeomorphDomain e u := h.symm ▸ mem_univ _
    obtain ⟨w, hw, he⟩ := hh
    exact e.injective he ▸ hw
  change (((1 + u : ℝ) : ℂ)) ∈ Metric.ball (0 : ℂ) (1 + u) at hz
  rw [Metric.mem_ball, dist_zero_right, Complex.norm_of_nonneg (add_nonneg zero_le_one hu)] at hz
  exact hz.false

theorem expandingHomeomorphDomain_strictMonoOn (e : ℂ ≃ₜ ℂ) :
    StrictMonoOn (expandingHomeomorphDomain e) (Ici 0) := by
  intro u hu v _ huv
  refine Set.ssubset_iff_subset_ne.mpr ⟨image_mono (Metric.ball_subset_ball (add_le_add_right huv.le 1)), ?_⟩
  intro heq
  let z : ℂ := ((1 + u : ℝ) : ℂ)
  have hzV : z ∈ Metric.ball (0 : ℂ) (1 + v) := by
    change ((1 + u : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) (1 + v)
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_of_nonneg (add_nonneg zero_le_one hu)]
    exact add_lt_add_right huv 1
  have him : e z ∈ expandingHomeomorphDomain e v := ⟨z, hzV, rfl⟩
  rw [← heq] at him
  obtain ⟨w, hw, he⟩ := him
  have hzU : z ∈ Metric.ball (0 : ℂ) (1 + u) := e.injective he ▸ hw
  change ((1 + u : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) (1 + u) at hzU
  rw [Metric.mem_ball, dist_zero_right, Complex.norm_of_nonneg (add_nonneg zero_le_one hu)] at hzU
  exact hzU.false

theorem iUnion_expandingHomeomorphDomain_of_lt_tendsto (e : ℂ ≃ₜ ℂ) {s : ℕ → ℝ} {u : ℝ}
    (hs : ∀ n, s n < u) (ht : Tendsto s atTop (𝓝 u)) :
    (⋃ n, expandingHomeomorphDomain e (s n)) = expandingHomeomorphDomain e u := by
  simp only [expandingHomeomorphDomain, ← image_iUnion]
  congr 1
  refine le_antisymm (iUnion_subset fun n ↦ Metric.ball_subset_ball (add_le_add_right (hs n).le 1)) ?_
  intro z hz
  have hlt : dist z 0 < 1 + u := Metric.mem_ball.mp hz
  have hlim : Tendsto (fun n ↦ 1 + s n) atTop (𝓝 (1 + u)) := tendsto_const_nhds.add ht
  obtain ⟨n, hn⟩ := (hlim.eventually_const_lt hlt).exists
  exact mem_iUnion.mpr ⟨n, Metric.mem_ball.mpr hn⟩

theorem interior_iInter_expandingHomeomorphDomain_of_gt_tendsto (e : ℂ ≃ₜ ℂ)
    {s : ℕ → ℝ} {u : ℝ} (hs : ∀ n, u < s n) (ht : Tendsto s atTop (𝓝 u)) :
    interior (⋂ n, expandingHomeomorphDomain e (s n)) = expandingHomeomorphDomain e u := by
  have hlimit : (⋂ n, Metric.ball (0 : ℂ) (1 + s n)) = Metric.closedBall 0 (1 + u) := by
    refine le_antisymm ?_ (subset_iInter fun n ↦ Metric.closedBall_subset_ball (add_lt_add_right (hs n) 1))
    intro z hz
    have hlim : Tendsto (fun n ↦ 1 + s n) atTop (𝓝 (1 + u)) := tendsto_const_nhds.add ht
    exact Metric.mem_closedBall.mpr (ge_of_tendsto hlim (.of_forall fun n ↦
      (Metric.mem_ball.mp (mem_iInter.mp hz n)).le))
  simp only [expandingHomeomorphDomain, ← Set.image_iInter e.bijective, ← e.image_interior,
    hlimit, interior_closedBall']

theorem iUnion_nat_expandingHomeomorphDomain_eq_univ (e : ℂ ≃ₜ ℂ) :
    (⋃ n : ℕ, expandingHomeomorphDomain e n) = univ := by
  apply eq_univ_of_forall
  intro w
  obtain ⟨z, rfl⟩ := e.surjective w
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  refine mem_iUnion.mpr ⟨n, z, ?_, rfl⟩
  rw [Metric.mem_ball, dist_zero_right]
  exact hn.trans_le (le_add_of_nonneg_left zero_le_one)

end Zalcman
