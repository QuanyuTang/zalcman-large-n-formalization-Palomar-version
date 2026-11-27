/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.AmbientDilation
public import Zalcman.Dilation
public import Zalcman.DomainChainGeometry
public import Zalcman.HomeomorphicBallExhaustion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
# Radial chains from analytic disk embeddings

The plane extension of an analytic disk embedding supplies a nested exhaustion.
Conformal radius gives the normalized time without boundary regularity of the
outer domains.
-/

@[expose] public section

namespace Zalcman

open Set Filter
open scoped Topology

/-- A normalized holomorphic embedding of the closed disk into a larger disk
admits a nested normalized conformal continuation. -/
theorem exists_nested_chain_of_analytic_disk {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) (hi : InjOn f (Metric.ball 0 R))
    (h₀ : f 0 = 0) (h₁ : deriv f 0 = 1) :
    ∃ F : ℝ → ℂ → ℂ, EqOn (F 0) f unitDisk ∧
      (∀ t ∈ Ici 0, DifferentiableOn ℂ (F t) unitDisk ∧ InjOn (F t) unitDisk ∧
        F t 0 = 0 ∧ deriv (F t) 0 = (Real.exp t : ℂ)) ∧
      ∀ s ∈ Ici 0, ∀ t ∈ Ici 0, s ≤ t → F s '' unitDisk ⊆ F t '' unitDisk := by
  obtain ⟨e, he⟩ := exists_plane_homeomorph_extends_analytic_disk hR hf hi h₀ h₁
  have he₀ : e 0 = 0 := (he (Metric.mem_closedBall_self zero_le_one)).trans h₀
  have heeq : EqOn e f unitDisk := he.mono Metric.ball_subset_closedBall
  have hImage : expandingHomeomorphDomain e 0 = f '' unitDisk := by
    change e '' Metric.ball 0 (1 + 0) = _
    rw [add_zero]
    exact heeq.image_eq
  have hstrict := expandingHomeomorphDomain_strictMonoOn e
  obtain ⟨F, τ, r₀, hr₀, hτ₀, hτ, hτmono, hF⟩ := exists_domain_chain_conformal_radius
    (fun t _ ↦ expandingHomeomorphDomain_isOpen e t)
    (fun _ ht ↦ expandingHomeomorphDomain_ne_univ e ht)
    (fun _ ht ↦ expandingHomeomorphDomain_isSimplyConnected e ht)
    (expandingHomeomorphDomain_zero_mem he₀ le_rfl) hstrict
    (fun _ hs ht ↦ iUnion_expandingHomeomorphDomain_of_lt_tendsto e hs ht)
    (fun _ hs ht ↦ interior_iInter_expandingHomeomorphDomain_of_gt_tendsto e hs ht)
    (iUnion_nat_expandingHomeomorphDomain_eq_univ e)
  obtain ⟨hFD, hFB, hF₀, hFder⟩ := hF 0 self_mem_Ici
  have hfD : DifferentiableOn ℂ f unitDisk := hf.mono (Metric.ball_subset_ball hR.le)
  have hfI : InjOn f unitDisk := hi.mono (Metric.ball_subset_ball hR.le)
  have hFImage : F 0 '' unitDisk = f '' unitDisk := by rw [hFB.image_eq, hτ₀, hImage]
  have hFder₀ : deriv (F 0) 0 = (r₀ : ℂ) := by
    simpa only [Real.exp_zero, mul_one] using hFder
  have hFinit := eqOn_of_image_eq_of_positive_conformal_radius hFD hfD hFB.injOn hfI hF₀ h₀
    hr₀ zero_lt_one hFder₀ (by simpa using h₁) hFImage
  have hr : r₀ = 1 := by
    have heq : F 0 =ᶠ[nhds (0 : ℂ)] f := by
      filter_upwards [Metric.isOpen_ball.mem_nhds zero_mem_unitDisk] with z hz
      exact hFinit hz
    apply Complex.ofReal_injective
    rw [Complex.ofReal_one, ← hFder₀, ← h₁]
    exact heq.deriv_eq
  refine ⟨F, hFinit, ?_, ?_⟩
  · intro t ht
    obtain ⟨hd, hb, hz, he'⟩ := hF t ht
    exact ⟨hd, hb.injOn, hz, by simpa only [hr, one_mul] using he'⟩
  · intro s hs t ht hst
    rw [(hF s hs).2.1.image_eq, (hF t ht).2.1.image_eq]
    exact hstrict.monotoneOn (hτ hs) (hτ ht) (hτmono.monotoneOn hs ht hst)

/-- The initial maps of nested normalized conformal chains are dense in the
normalized univalent class for locally uniform convergence. -/
theorem exists_nested_chain_approximation {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    ∃ F : ℕ → ℝ → ℂ → ℂ,
      TendstoLocallyUniformlyOn (fun n ↦ F n 0) f atTop unitDisk ∧
      (∀ n, ∀ t ∈ Ici 0, DifferentiableOn ℂ (F n t) unitDisk ∧ InjOn (F n t) unitDisk ∧
        F n t 0 = 0 ∧ deriv (F n t) 0 = (Real.exp t : ℂ)) ∧
      ∀ n, ∀ s ∈ Ici 0, ∀ t ∈ Ici 0, s ≤ t → F n s '' unitDisk ⊆ F n t '' unitDisk := by
  let d := fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) + 1)
  let r := fun n ↦ 1 - d n
  have hd (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hr₀ (n : ℕ) : 0 < r n := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [r, d]
    rw [sub_pos, div_lt_one (by positivity)]
    push_cast
    linarith
  have hr₁ (n : ℕ) : r n < 1 := sub_lt_self 1 (hd n)
  have hdt : Tendsto d atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr tendsto_one_div_add_atTop_nhds_zero_nat
  have hrt : Tendsto r atTop (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, .of_forall hr₁⟩
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub hdt : Tendsto (fun n ↦ 1 - d n) atTop (𝓝 (1 - 0)))
  have hex (n : ℕ) := by
    have hh := hf.normalizedDilation_on_ball (hr₀ n)
    have hNorm := hf.normalizedDilation (hr₀ n) (hr₁ n).le
    exact exists_nested_chain_of_analytic_disk ((one_lt_inv₀ (hr₀ n)).mpr (hr₁ n))
      hh.1 hh.2 hNorm.map_zero hNorm.deriv_zero
  choose F hF₀ hF hInc using hex
  have hconv : TendstoLocallyUniformlyOn (fun n ↦ normalizedDilation (r n) f) f atTop unitDisk := by
    intro V hV z hz
    obtain ⟨W, hW, hWV⟩ := tendstoLocallyUniformlyOn_normalizedDilation hf.holomorphic.continuousOn
      V hV z hz
    exact ⟨W, hW, hrt.eventually hWV⟩
  exact ⟨F, hconv.congr fun n ↦ (hF₀ n).symm, hF, hInc⟩

end Zalcman
