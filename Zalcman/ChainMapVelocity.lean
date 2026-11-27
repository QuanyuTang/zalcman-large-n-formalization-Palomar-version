/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.ExpNormalization
public import Zalcman.LogarithmicVelocity
public import Zalcman.NormalizedChainEnergy
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Ring

/-!
# Certified terminal chains from radial map velocities

Scaling a direct chain by its conformal radius gives the normalized velocity.
Uniform time Lipschitz estimates on one circle survive this scaling.
-/

public section

namespace Zalcman

open Filter MeasureTheory Set
open scoped NNReal Topology

/-- Normalized map velocities give the corresponding certificate for the Milin
energy calculation, using the normalized logarithm on the disk. -/
@[expose] def KoebeTerminatingLogarithmicChain.of_normalizedMapVelocity
    (F : ℝ → ℂ → ℂ) (hF : ∀ t, NormalizedUnivalent (F t)) (T : ℝ) (hT : 0 ≤ T)
    (hTerminal : EqOn (F T) koebe unitDisk) (κ : ℝ → ℂ)
    (hLip : ∃ K r : ℝ≥0, 0 < r ∧ (r : ℝ) < 1 ∧
      ∀ z ∈ Metric.sphere (0 : ℂ) r, LipschitzOnWith K (fun t ↦ F t z) (Icc 0 T))
    (hVelocity : ∀ᵐ u : ℝ ∂volume, u ∈ Ioc 0 T → ‖κ u‖ = 1 ∧
      TendstoLocallyUniformlyOn (fun t z ↦ slope (fun s ↦ F s z) u t)
        (fun z ↦ z * deriv (F u) z * radialDriver (κ u) z - F u z)
        (𝓝[≠] u) unitDisk) :
    KoebeTerminatingLogarithmicChain where
  maps := F
  normalized := hF
  duration := T
  duration_nonneg := hT
  terminal := hTerminal
  driver := κ
  time_lipschitz := hLip
  logarithmic_velocity := by
    filter_upwards [hVelocity] with u hu hut
    obtain ⟨hκ, hSlope⟩ := hu hut
    exact ⟨hκ, tendstoLocallyUniformlyOn_radial_slope_normalizedLogarithm hF
      (radialDriver_holomorphic hκ.le) hSlope⟩

private theorem norm_exp_neg_le_one {t : ℝ} (ht : 0 ≤ t) :
    ‖(Real.exp (-t) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)

private theorem lipschitzOnWith_exp_neg_ofReal (T : ℝ) :
    LipschitzOnWith 1 (fun t : ℝ ↦ (Real.exp (-t) : ℂ)) (Icc 0 T) := by
  refine (convex_Icc _ _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t _ ↦ (hasDerivAt_exp_neg_ofReal t).hasDerivWithinAt) ?_
  intro t ht
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, norm_neg]
  exact norm_exp_neg_le_one ht.1

/-- A common time Lipschitz constant on a circle is preserved under
exponential normalization on a compact time interval. -/
theorem exists_lipschitzOnWith_exp_normalization
    {F : ℝ → ℂ → ℂ} {T : ℝ} (hT : 0 ≤ T) {K r : ℝ≥0} (hr₁ : (r : ℝ) < 1)
    (hF₀ : ContinuousOn (F 0) unitDisk)
    (hL : ∀ z ∈ Metric.sphere (0 : ℂ) r, LipschitzOnWith K (fun t ↦ F t z) (Icc 0 T)) :
    ∃ K' : ℝ≥0, ∀ z ∈ Metric.sphere (0 : ℂ) r,
      LipschitzOnWith K' (fun t ↦ (Real.exp (-t) : ℂ) * F t z) (Icc 0 T) := by
  let E (t : ℝ) : ℂ := Real.exp (-t)
  have hsub : Metric.sphere (0 : ℂ) r ⊆ unitDisk := by
    intro z hz
    have hzr : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    rw [mem_unitDisk, hzr]
    exact hr₁
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) (r : ℝ)).exists_bound_of_continuousOn
    (hF₀.mono hsub)
  let B : ℝ≥0 := ⟨max C 0 + (K : ℝ) * T,
    add_nonneg (le_max_right _ _) (mul_nonneg K.coe_nonneg hT)⟩
  have hBound (t : ℝ) (ht : t ∈ Icc 0 T) (z : ℂ)
      (hz : z ∈ Metric.sphere (0 : ℂ) r) : ‖F t z‖ ≤ (B : ℝ) := by
    have hDist := (hL z hz).dist_le_mul t ht 0 ⟨le_rfl, hT⟩
    rw [dist_eq_norm, Real.dist_eq, sub_zero, abs_of_nonneg ht.1] at hDist
    calc
      _ = ‖(F t z - F 0 z) + F 0 z‖ := by rw [sub_add_cancel]
      _ ≤ ‖F t z - F 0 z‖ + ‖F 0 z‖ := norm_add_le _ _
      _ ≤ (K : ℝ) * T + max C 0 :=
        add_le_add (hDist.trans (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg))
          ((hC z hz).trans (le_max_left _ _))
      _ = (B : ℝ) := by
        change _ = max C 0 + (K : ℝ) * T
        exact add_comm _ _
  refine ⟨K + B, fun z hz ↦ LipschitzOnWith.of_dist_le_mul ?_⟩
  intro s hs t ht
  have hFDist := (hL z hz).dist_le_mul s hs t ht
  have hEDist := (lipschitzOnWith_exp_neg_ofReal T).dist_le_mul s hs t ht
  rw [dist_eq_norm] at hFDist hEDist ⊢
  simp only [NNReal.coe_one, one_mul] at hEDist
  change ‖E s * F s z - E t * F t z‖ ≤ _
  calc
    _ = ‖E s * (F s z - F t z) + (E s - E t) * F t z‖ := by congr 1; ring
    _ ≤ ‖E s‖ * ‖F s z - F t z‖ + ‖E s - E t‖ * ‖F t z‖ := by
      simpa only [norm_mul] using norm_add_le (E s * (F s z - F t z)) ((E s - E t) * F t z)
    _ ≤ 1 * ((K : ℝ) * dist s t) + dist s t * (B : ℝ) :=
      add_le_add (mul_le_mul (norm_exp_neg_le_one hs.1) hFDist (norm_nonneg _) zero_le_one)
        (mul_le_mul hEDist (hBound t ht z hz) (norm_nonneg _) dist_nonneg)
    _ = ((K + B : ℝ≥0) : ℝ) * dist s t := by rw [NNReal.coe_add]; ring

/-- A direct radial chain with terminal map \(\exp(T)k\) certifies its
initial map for the Milin energy representation. Its maps outside the compact
time interval have no role and are replaced by Koebe. -/
theorem exists_koebeTerminating_chain_of_unnormalized_family
    {F : ℝ → ℂ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hDiff : ∀ t ∈ Icc 0 T, DifferentiableOn ℂ (F t) unitDisk)
    (hInj : ∀ t ∈ Icc 0 T, InjOn (F t) unitDisk)
    (hZero : ∀ t ∈ Icc 0 T, F t 0 = 0)
    (hDeriv : ∀ t ∈ Icc 0 T, deriv (F t) 0 = (Real.exp t : ℂ))
    (hTerminal : EqOn (F T) (fun z ↦ (Real.exp T : ℂ) * koebe z) unitDisk) (κ : ℝ → ℂ)
    (hLip : ∃ K r : ℝ≥0, 0 < r ∧ (r : ℝ) < 1 ∧
      ∀ z ∈ Metric.sphere (0 : ℂ) r, LipschitzOnWith K (fun t ↦ F t z) (Icc 0 T))
    (hVelocity : ∀ᵐ u : ℝ ∂volume, u ∈ Ioo 0 T → ‖κ u‖ = 1 ∧
      TendstoLocallyUniformlyOn
        (fun t z ↦ slope (fun s ↦ F s z) u t)
        (fun z ↦ z * deriv (F u) z * radialDriver (κ u) z) (𝓝[≠] u) unitDisk) :
    ∃ P : KoebeTerminatingLogarithmicChain, P.maps 0 = F 0 := by
  classical
  let E (t : ℝ) : ℂ := Real.exp (-t)
  let G (t : ℝ) (z : ℂ) := E t * F t z
  let H (t : ℝ) : ℂ → ℂ := if t ∈ Icc 0 T then G t else koebe
  have hHG (t : ℝ) (ht : t ∈ Icc 0 T) : H t = G t := ite_eq_left ht
  have hExpCancel (t : ℝ) : E t * (Real.exp t : ℂ) = 1 := by
    dsimp only [E]
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  have hH (t : ℝ) : NormalizedUnivalent (H t) := by
    by_cases ht : t ∈ Icc 0 T
    · rw [hHG t ht]
      have hEnz : E t ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
      refine ⟨(hDiff t ht).const_mul _, fun _ hz _ hw hEq ↦
        hInj t ht hz hw (mul_left_cancel₀ hEnz hEq), ?_, ?_⟩
      · simp only [G, hZero t ht, mul_zero]
      · simp only [G, deriv_const_mul_field, hDeriv t ht, hExpCancel t]
    · simpa only [H, ite_eq_right ht] using koebe_normalizedUnivalent
  have hHT : EqOn (H T) koebe unitDisk := by
    intro z hz
    rw [hHG T ⟨hT, le_rfl⟩]
    change E T * F T z = koebe z
    rw [hTerminal hz, ← mul_assoc, hExpCancel T, one_mul]
  have hHLip : ∃ K r : ℝ≥0, 0 < r ∧ (r : ℝ) < 1 ∧
      ∀ z ∈ Metric.sphere (0 : ℂ) r, LipschitzOnWith K (fun t ↦ H t z) (Icc 0 T) := by
    obtain ⟨K, r, hr, hr₁, hF⟩ := hLip
    obtain ⟨K', hG⟩ := exists_lipschitzOnWith_exp_normalization hT hr₁
      (hDiff 0 ⟨le_rfl, hT⟩).continuousOn hF
    refine ⟨K', r, hr, hr₁, fun z hz ↦ LipschitzOnWith.of_dist_le_mul ?_⟩
    intro s hs t ht
    simpa only [hHG s hs, hHG t ht, G, E] using (hG z hz).dist_le_mul s hs t ht
  have hHVelocity : ∀ᵐ u : ℝ ∂volume, u ∈ Ioc 0 T → ‖κ u‖ = 1 ∧
      TendstoLocallyUniformlyOn (fun t z ↦ slope (fun s ↦ H s z) u t)
        (fun z ↦ z * deriv (H u) z * radialDriver (κ u) z - H u z)
        (𝓝[≠] u) unitDisk := by
    have hTae : ∀ᵐ u : ℝ ∂volume, u ≠ T := by
      rw [ae_iff]
      simp
    filter_upwards [hVelocity, hTae] with u hu hne hut
    have huo : u ∈ Ioo 0 T := ⟨hut.1, lt_of_le_of_ne hut.2 hne⟩
    have huc : u ∈ Icc 0 T := ⟨hut.1.le, hut.2⟩
    obtain ⟨hκ, hSlope⟩ := hu huo
    have hG := tendstoLocallyUniformlyOn_slope_exp_normalization (hDiff u huc)
      (radialDriver_holomorphic hκ.le) hSlope
    refine ⟨hκ, ?_⟩
    rw [hHG u huc]
    refine hG.congr_inseparable ?_
    have hnear : ∀ᶠ t in 𝓝[≠] u, t ∈ Icc 0 T :=
      nhdsWithin_le_nhds (Icc_mem_nhds huo.1 huo.2)
    filter_upwards [hnear] with t ht z _
    have hEq : slope (fun s ↦ G s z) u t = slope (fun s ↦ H s z) u t := by
      simp only [slope_def_module, hHG t ht, hHG u huc]
    exact Inseparable.of_eq hEq
  let P := KoebeTerminatingLogarithmicChain.of_normalizedMapVelocity H hH T hT hHT κ hHLip hHVelocity
  refine ⟨P, ?_⟩
  change H 0 = F 0
  rw [hHG 0 ⟨le_rfl, hT⟩]
  funext z
  simp [G, E]


end Zalcman
