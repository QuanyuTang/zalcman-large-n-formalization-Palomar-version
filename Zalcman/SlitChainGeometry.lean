/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.DomainChainGeometry
public import Zalcman.SlitTail

/-!
# Conformal-radius time for a slit

Riemann maps of the tail complements are parametrized by the logarithm of
their conformal radius.
-/

public section

namespace Zalcman

open Filter Set

/-- A proper injective ray with simply connected tail complements admits a normalized
increasing chain of Riemann maps. The conformal radius is the time parameter, up to
the initial radius and the exponential change of variables. -/
theorem exists_slit_chain_conformal_radius {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hinj : InjOn γ (Ici 0)) (hinfty : Tendsto (fun t ↦ ‖γ t‖) atTop atTop)
    (hzero : 0 ∈ slitTailDomain γ 0)
    (hsc : ∀ t ∈ Ici 0, IsSimplyConnected (slitTailDomain γ t)) :
    ∃ (F : ℝ → ℂ → ℂ) (τ : ℝ → ℝ) (r₀ : ℝ), 0 < r₀ ∧ τ 0 = 0 ∧
      MapsTo τ (Ici 0) (Ici 0) ∧ StrictMonoOn τ (Ici 0) ∧
      ∀ t ∈ Ici 0, DifferentiableOn ℂ (F t) unitDisk ∧
        BijOn (F t) unitDisk (slitTailDomain γ (τ t)) ∧ F t 0 = 0 ∧
        deriv (F t) 0 = ((r₀ * Real.exp t : ℝ) : ℂ) := by
  refine exists_domain_chain_conformal_radius (U := slitTailDomain γ)
    (fun t _ ↦ isOpen_slitTailDomain hγ hinfty t) ?_ hsc hzero
    (slitTailDomain_strictMonoOn hinj) ?_ ?_ (iUnion_nat_slitTailDomain_eq_univ hinfty)
  · intro t _ h
    have ht : γ t ∈ slitTailDomain γ t := h.symm ▸ mem_univ _
    exact ht ⟨t, self_mem_Ici, rfl⟩
  · intro u s hs₀ hs ht
    exact iUnion_slitTailDomain_of_lt_tendsto hinj hs₀ hs ht
  · intro u s hu hs ht
    exact interior_iInter_slitTailDomain_of_gt_tendsto hγ hinfty hs ht

end Zalcman
