/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Order.OrderClosed

/-!
# Tail complements of a proper plane slit

The domains obtained by shortening a proper injective ray are strictly nested.
Their one-sided set limits give the union and interior-intersection conditions
for convergence of conformal radii.
-/

@[expose] public section

namespace Zalcman

open Set Filter
open scoped Topology

/-- The complement of the part of the slit from parameter `u` onward. -/
def slitTailDomain (γ : ℝ → ℂ) (u : ℝ) : Set ℂ := (γ '' Ici u)ᶜ

theorem slitTailDomain_mono (γ : ℝ → ℂ) : Monotone (slitTailDomain γ) := by
  intro u v huv
  exact compl_subset_compl.mpr (image_mono (Ici_subset_Ici.mpr huv))

theorem slitTailDomain_strictMonoOn {γ : ℝ → ℂ} (hγ : InjOn γ (Ici 0)) :
    StrictMonoOn (slitTailDomain γ) (Ici 0) := by
  intro u hu v hv huv
  refine Set.ssubset_iff_subset_ne.mpr ⟨slitTailDomain_mono γ huv.le, ?_⟩
  intro he
  have hmem : γ u ∈ slitTailDomain γ v := by
    rintro ⟨w, hw, heq⟩
    have hw₀ : w ∈ Ici (0 : ℝ) := (show 0 ≤ v from hv).trans (show v ≤ w from hw)
    have huw := hγ hw₀ hu heq
    exact (not_le_of_gt huv) (huw ▸ hw)
  rw [← he] at hmem
  exact hmem ⟨u, self_mem_Ici, rfl⟩

private theorem isClosed_slitTail_image {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hinfty : Tendsto (fun u ↦ ‖γ u‖) atTop atTop) (u : ℝ) : IsClosed (γ '' Ici u) := by
  apply isOpen_compl_iff.mp
  rw [isOpen_iff_mem_nhds]
  intro w hw
  obtain ⟨a, ha⟩ := eventually_atTop.mp (hinfty.eventually_gt_atTop (‖w‖ + 1))
  have hK : IsClosed (γ '' Icc u a) := (isCompact_Icc.image hγ).isClosed
  have hwK : w ∈ (γ '' Icc u a)ᶜ := by
    rintro ⟨t, ht, rfl⟩
    exact hw ⟨t, ht.1, rfl⟩
  have hwB : w ∈ Metric.ball (0 : ℂ) (‖w‖ + 1) := by simp
  refine mem_of_superset (inter_mem (hK.isOpen_compl.mem_nhds hwK)
    (Metric.isOpen_ball.mem_nhds hwB)) ?_
  rintro z ⟨hzK, hzB⟩ ⟨t, ht, rfl⟩
  by_cases hta : t ≤ a
  · exact hzK ⟨t, ⟨ht, hta⟩, rfl⟩
  · have hzNorm : ‖γ t‖ < ‖w‖ + 1 := by simpa [Metric.mem_ball, dist_zero_right] using hzB
    exact (not_lt_of_ge (ha t (le_of_not_ge hta)).le) hzNorm

theorem isOpen_slitTailDomain {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hinfty : Tendsto (fun u ↦ ‖γ u‖) atTop atTop) (u : ℝ) : IsOpen (slitTailDomain γ u) :=
  (isClosed_slitTail_image hγ hinfty u).isOpen_compl

/-- Approaching a time from below exhausts the domain at that time. -/
theorem iUnion_slitTailDomain_of_lt_tendsto {γ : ℝ → ℂ} (hγ : InjOn γ (Ici 0))
    {u : ℝ} {s : ℕ → ℝ} (hs₀ : ∀ n, 0 ≤ s n) (hs : ∀ n, s n < u)
    (ht : Tendsto s atTop (𝓝 u)) : (⋃ n, slitTailDomain γ (s n)) = slitTailDomain γ u := by
  refine le_antisymm (iUnion_subset fun n ↦ slitTailDomain_mono γ (hs n).le) ?_
  intro w hw
  by_cases hwr : w ∈ γ '' Ici (0 : ℝ)
  · obtain ⟨v, hv, rfl⟩ := hwr
    have hvu : v < u := lt_of_not_ge fun hvu ↦ hw ⟨v, hvu, rfl⟩
    obtain ⟨n, hn⟩ := (ht.eventually_const_lt hvu).exists
    refine mem_iUnion.mpr ⟨n, ?_⟩
    rintro ⟨t, htn, heq⟩
    have htv := hγ ((hs₀ n).trans htn) hv heq
    exact hn.not_ge (htv ▸ htn)
  · exact mem_iUnion.mpr ⟨0, fun hw₀ ↦ hwr (image_mono (Ici_subset_Ici.mpr (hs₀ 0)) hw₀)⟩

/-- Approaching a time from above gives the domain as the interior of the intersection. -/
theorem interior_iInter_slitTailDomain_of_gt_tendsto {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hinfty : Tendsto (fun u ↦ ‖γ u‖) atTop atTop)
    {u : ℝ} {s : ℕ → ℝ} (hs : ∀ n, u < s n)
    (ht : Tendsto s atTop (𝓝 u)) : interior (⋂ n, slitTailDomain γ (s n)) = slitTailDomain γ u := by
  have hU : (⋃ n, γ '' Ici (s n)) = γ '' Ioi u := by
    refine le_antisymm (iUnion_subset fun n ↦ image_mono (fun t ht' ↦ (hs n).trans_le ht')) ?_
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨n, hn⟩ := (ht.eventually_lt_const hv).exists
    exact mem_iUnion.mpr ⟨n, v, hn.le, rfl⟩
  have hC : closure (γ '' Ioi u) = γ '' Ici u := by
    refine le_antisymm (closure_minimal (image_mono Ioi_subset_Ici_self)
      (isClosed_slitTail_image hγ hinfty u)) ?_
    rw [← closure_Ioi]
    exact image_closure_subset_closure_image hγ
  simp only [slitTailDomain, ← compl_iUnion, hU, interior_eq_compl_closure_compl,
    compl_compl, hC]

/-- The tail complements of a proper ray exhaust the plane. -/
theorem iUnion_nat_slitTailDomain_eq_univ {γ : ℝ → ℂ}
    (hinfty : Tendsto (fun u ↦ ‖γ u‖) atTop atTop) :
    (⋃ n : ℕ, slitTailDomain γ n) = univ := by
  apply eq_univ_of_forall
  intro w
  obtain ⟨a, ha⟩ := eventually_atTop.mp (hinfty.eventually_gt_atTop ‖w‖)
  obtain ⟨n, hn⟩ := exists_nat_ge a
  refine mem_iUnion.mpr ⟨n, ?_⟩
  rintro ⟨v, hv, rfl⟩
  exact (ha v (hn.trans hv)).false

end Zalcman
