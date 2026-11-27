/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.FiniteDriverChain
public import Zalcman.ChainTime
public import Zalcman.ChainMapVelocity

/-!
# Continuing a finite driver chain by Koebe

After its terminal time, a finite chain ending at Koebe can be continued
by positive dilations. This also gives a circle Lipschitz bound on the
original time interval.
-/

public section

namespace Zalcman

open Filter MeasureTheory Set
open scoped NNReal Topology

/-- The finite data of a unit-driven chain with a positive duration and
the Koebe terminal map. -/
structure FiniteKoebeDriverChain where
  duration : ℝ
  duration_pos : 0 < duration
  driver : ℝ → ℂ
  measurable_driver : Measurable driver
  norm_driver : ∀ t, ‖driver t‖ = 1
  chain : FiniteDriverChain 0 duration driver (fun z ↦ (Real.exp duration : ℂ) * koebe z)

/-- Extend a realization by the Koebe chain outside its given time interval. -/
noncomputable def FiniteDriverChain.koebeContinuation {T : ℝ} {κ : ℝ → ℂ}
    (P : FiniteDriverChain 0 T κ (fun z ↦ (Real.exp T : ℂ) * koebe z))
    (t : ℝ) : ℂ → ℂ :=
  if t ∈ Icc (0 : ℝ) T then P.maps t else fun z ↦ (Real.exp t : ℂ) * koebe z

theorem FiniteDriverChain.koebeContinuation_eq {T : ℝ} {κ : ℝ → ℂ}
    (P : FiniteDriverChain 0 T κ (fun z ↦ (Real.exp T : ℂ) * koebe z))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    P.koebeContinuation t = P.maps t := ite_eq_left ht

theorem FiniteDriverChain.koebeContinuation_eq_koebe {T : ℝ} {κ : ℝ → ℂ}
    (P : FiniteDriverChain 0 T κ (fun z ↦ (Real.exp T : ℂ) * koebe z))
    {t : ℝ} (ht : t ∉ Icc (0 : ℝ) T) :
    P.koebeContinuation t = fun z ↦ (Real.exp t : ℂ) * koebe z := ite_eq_right ht

/-- Every map in the extended family has the exponential normalization. -/
theorem FiniteDriverChain.koebeContinuation_map {T : ℝ} {κ : ℝ → ℂ}
    (P : FiniteDriverChain 0 T κ (fun z ↦ (Real.exp T : ℂ) * koebe z)) (t : ℝ) :
    ExponentialDiskMap t (P.koebeContinuation t) := by
  by_cases ht : t ∈ Icc (0 : ℝ) T
  · simpa only [P.koebeContinuation_eq ht] using P.map_on t ht
  · simpa only [FiniteDriverChain.koebeContinuation, ite_eq_right ht] using
      ExponentialDiskMap.of_normalizedUnivalent koebe_normalizedUnivalent t

/-- The continued chain is nested at all nonnegative times. -/
theorem FiniteDriverChain.koebeContinuation_nested {T : ℝ} (hT : 0 ≤ T) {κ : ℝ → ℂ}
    (P : FiniteDriverChain 0 T κ (fun z ↦ (Real.exp T : ℂ) * koebe z))
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s ≤ t) :
    P.koebeContinuation s '' unitDisk ⊆ P.koebeContinuation t '' unitDisk := by
  by_cases h : t ≤ T
  · rw [P.koebeContinuation_eq ⟨hs, hst.trans h⟩, P.koebeContinuation_eq ⟨ht, h⟩]
    exact P.nested s ⟨hs, hst.trans h⟩ t ⟨ht, h⟩ hst
  · have htOut : t ∉ Icc (0 : ℝ) T := fun ht' ↦ h ht'.2
    rw [P.koebeContinuation_eq_koebe htOut]
    by_cases hsT : s ≤ T
    · rw [P.koebeContinuation_eq ⟨hs, hsT⟩]
      refine (P.nested s ⟨hs, hsT⟩ T ⟨hT, le_rfl⟩ hsT).trans ?_
      rw [P.terminal.image_eq]
      exact koebe_scaled_image_mono (Real.exp_pos T) (Real.exp_le_exp.mpr (le_of_not_ge h))
    · have hsOut : s ∉ Icc (0 : ℝ) T := fun hs' ↦ hsT hs'.2
      rw [P.koebeContinuation_eq_koebe hsOut]
      exact koebe_scaled_image_mono (Real.exp_pos s) (Real.exp_le_exp.mpr hst)

/-- The continued family retains its point-driver slope away from the seams. -/
theorem FiniteDriverChain.koebeContinuation_velocity_off_seams {T : ℝ} {κ : ℝ → ℂ}
    (P : FiniteDriverChain 0 T κ (fun z ↦ (Real.exp T : ℂ) * koebe z))
    {u : ℝ} (hut : u ∈ Ioo 0 T) (hNot : u ∉ P.seams) :
    ‖κ u‖ = 1 ∧
      TendstoLocallyUniformlyOn
        (fun t z ↦ slope (fun s ↦ P.koebeContinuation s z) u t)
        (fun z ↦ z * deriv (P.koebeContinuation u) z * radialDriver (κ u) z)
        (𝓝[≠] u) unitDisk := by
  obtain ⟨hκ, hSlope⟩ := P.velocity_off_seams u hut hNot
  have hu' : u ∈ Icc (0 : ℝ) T := ⟨hut.1.le, hut.2.le⟩
  refine ⟨hκ, ?_⟩
  rw [P.koebeContinuation_eq hu']
  have hTarget : (fun z ↦ z * radialDriver (κ u) z * deriv (P.maps u) z) =
      (fun z ↦ z * deriv (P.maps u) z * radialDriver (κ u) z) :=
    funext (fun _ ↦ mul_right_comm _ _ _)
  rw [← hTarget]
  refine hSlope.congr_inseparable ?_
  have hNear : ∀ᶠ t in 𝓝[≠] u, t ∈ Icc (0 : ℝ) T :=
    nhdsWithin_le_nhds (Icc_mem_nhds hut.1 hut.2)
  filter_upwards [hNear] with t ht z _
  exact Inseparable.of_eq (by simp only [slope_def_module,
    P.koebeContinuation_eq hu', P.koebeContinuation_eq ht])

/-- The direct equation for the continued family, in almost-everywhere form. -/
theorem FiniteDriverChain.koebeContinuation_velocity {T : ℝ} {κ : ℝ → ℂ}
    (P : FiniteDriverChain 0 T κ (fun z ↦ (Real.exp T : ℂ) * koebe z)) :
    ∀ᵐ u : ℝ ∂volume, u ∈ Ioo 0 T → ‖κ u‖ = 1 ∧
      TendstoLocallyUniformlyOn
        (fun t z ↦ slope (fun s ↦ P.koebeContinuation s z) u t)
        (fun z ↦ z * deriv (P.koebeContinuation u) z * radialDriver (κ u) z)
        (𝓝[≠] u) unitDisk := by
  filter_upwards [P.seams.finite_toSet.countable.ae_notMem (volume : Measure ℝ)] with u hNot hut
  exact P.koebeContinuation_velocity_off_seams hut hNot

/-- The chain provides a certificate for the logarithmic energy calculation. -/
theorem FiniteDriverChain.exists_koebeTerminatingLogarithmicChain {T : ℝ} (hT : 0 ≤ T) {κ : ℝ → ℂ}
    (P : FiniteDriverChain 0 T κ (fun z ↦ (Real.exp T : ℂ) * koebe z)) :
    ∃ Q : KoebeTerminatingLogarithmicChain, Q.maps 0 = P.maps 0 := by
  let G := P.koebeContinuation
  have hG t := P.koebeContinuation_map t
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_nested_chain (T := T) (r := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)
    (fun t _ ↦ (hG t).holomorphic) (fun t _ ↦ (hG t).injective) (fun t _ ↦ (hG t).map_zero)
    (fun t _ ↦ (hG t).deriv_zero)
    (fun _ hs _ ht hst ↦ P.koebeContinuation_nested hT hs ht hst)
  have hGterm : EqOn (G T) (fun z ↦ (Real.exp T : ℂ) * koebe z) unitDisk := by
    rw [show G T = P.maps T from P.koebeContinuation_eq ⟨hT, le_rfl⟩]
    exact P.terminal
  have hLip : ∃ K r : ℝ≥0, 0 < r ∧ (r : ℝ) < 1 ∧
      ∀ z ∈ Metric.sphere (0 : ℂ) r, LipschitzOnWith K (fun t ↦ G t z) (Icc 0 T) := by
    let r : ℝ≥0 := 1 / 2
    have hr : 0 < r := by norm_num [r]
    have hr₁ : (r : ℝ) < 1 := by norm_num [r]
    have hr' : (r : ℝ) = 1 / 2 := by norm_num [r]
    refine ⟨K, r, hr, hr₁, fun z hz ↦ hK z ?_⟩
    rw [Metric.mem_sphere, dist_zero_right] at hz
    simpa only [hr'] using hz.le
  obtain ⟨Q, hQ⟩ := exists_koebeTerminating_chain_of_unnormalized_family hT
    (fun t _ ↦ (hG t).holomorphic) (fun t _ ↦ (hG t).injective) (fun t _ ↦ (hG t).map_zero)
    (fun t _ ↦ (hG t).deriv_zero) hGterm κ hLip P.koebeContinuation_velocity
  exact ⟨Q, hQ.trans (P.koebeContinuation_eq ⟨le_rfl, hT⟩)⟩

/-- The initial map of the finite realization is normalized and univalent. -/
theorem FiniteKoebeDriverChain.normalized_initial (P : FiniteKoebeDriverChain) :
    NormalizedUnivalent (P.chain.maps 0) := by
  have h := (P.chain.map_on 0 ⟨le_rfl, P.duration_pos.le⟩).normalizedUnivalent
  simpa only [neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul] using h

end Zalcman
