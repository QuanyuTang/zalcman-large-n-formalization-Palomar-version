/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.ChainTime
public import Zalcman.TransitionMoments
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive-real approximation to the time slope of a nested chain
-/
public section

namespace Zalcman

open Filter Set
open scoped Topology

/-- The slopes of a nested chain have a vanishing locally uniform remainder
from multiplication by the normalized positive-real transition drivers. -/
theorem exists_nested_chain_slope_approximation {F : ℝ → ℂ → ℂ} {u : ℝ} (hu : 0 ≤ u)
    (hd : ∀ t ∈ Ici 0, DifferentiableOn ℂ (F t) unitDisk)
    (hi : ∀ t ∈ Ici 0, InjOn (F t) unitDisk) (h₀ : ∀ t ∈ Ici 0, F t 0 = 0)
    (h₁ : ∀ t ∈ Ici 0, deriv (F t) 0 = (Real.exp t : ℂ))
    (hsub : ∀ s ∈ Ici 0, ∀ t ∈ Ici 0, s ≤ t → F s '' unitDisk ⊆ F t '' unitDisk) :
    ∃ (p : ℝ → ℂ → ℂ) (c : ℝ → ℂ),
      (∀ᶠ t in 𝓝[>] u, DifferentiableOn ℂ (p t) unitDisk ∧ p t 0 = 1 ∧
        ∀ z ∈ unitDisk, 0 ≤ (p t z).re) ∧
      Tendsto c (𝓝[>] u) (𝓝 (1 : ℂ)) ∧
      TendstoLocallyUniformlyOn
        (fun t z ↦ slope (fun s ↦ F s z) u t - c t * (p t z * (z * deriv (F u) z)))
        (fun _ ↦ 0) (𝓝[>] u) unitDisk := by
  classical
  have hT (t : ℝ) (ht : u < t) : ∃ φ : ℂ → ℂ,
      DifferentiableOn ℂ φ unitDisk ∧ MapsTo φ unitDisk unitDisk ∧ φ 0 = 0 ∧
      EqOn (fun z ↦ F t (φ z)) (F u) unitDisk ∧ deriv φ 0 = (Real.exp (u - t) : ℂ) := by
    have ht₀ := hu.trans ht.le
    obtain ⟨φ, hdφ, hmφ, hφ₀, hφE, hφDer⟩ := exists_normalized_disk_transition
      (hd u hu) (hd t ht₀) (hi t ht₀) (h₀ u hu) (h₀ t ht₀) (hsub u hu t ht₀ ht.le)
    refine ⟨φ, hdφ, hmφ, hφ₀, hφE, ?_⟩
    rw [hφDer, h₁ u hu, h₁ t ht₀, Real.exp_sub, Complex.ofReal_div]
  choose φ hφD hφM hφ₀ hφE hφDer using hT
  let Φ (t : ℝ) : ℂ → ℂ := if ht : u < t then φ t ht else id
  let a (t : ℝ) := Real.exp (u - t)
  let δ (t : ℝ) := t - u
  let p (t : ℝ) := transitionDriver (Φ t) (a t)
  let c (t : ℝ) : ℂ := ((1 - a t) / δ t : ℝ)
  have hΦ (t : ℝ) (ht : u < t) : Φ t = φ t ht := dite_eq_left ht
  have hΦD (t : ℝ) (ht : u < t) : DifferentiableOn ℂ (Φ t) unitDisk := by
    simpa only [hΦ t ht] using hφD t ht
  have hΦM (t : ℝ) (ht : u < t) : MapsTo (Φ t) unitDisk unitDisk := by
    simpa only [hΦ t ht] using hφM t ht
  have hΦ₀ (t : ℝ) (ht : u < t) : Φ t 0 = 0 := by
    simpa only [hΦ t ht] using hφ₀ t ht
  have hΦE (t : ℝ) (ht : u < t) : EqOn (fun z ↦ F t (Φ t z)) (F u) unitDisk := by
    simpa only [hΦ t ht] using hφE t ht
  have hΦDer (t : ℝ) (ht : u < t) : deriv (Φ t) 0 = (a t : ℂ) := by
    simpa only [hΦ t ht] using hφDer t ht
  have ha (t : ℝ) (ht : u < t) : a t < 1 := Real.exp_lt_one_iff.mpr (sub_neg.mpr ht)
  have hδ : Tendsto δ (𝓝[>] u) (𝓝 0) := by
    have h : Tendsto δ (𝓝 u) (𝓝 (u - u)) := tendsto_id.sub_const u
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hδ₀ : ∀ᶠ t in 𝓝[>] u, 0 < δ t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_pos.mpr ht
  have hδne : Tendsto δ (𝓝[>] u) (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδ, hδ₀.mono fun _ ht ↦ ht.ne'⟩
  have hδa (t : ℝ) : -(δ t) = u - t := neg_sub _ _
  refine ⟨p, c, ?_, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact transitionDriver_spec (hΦD t ht) (hΦM t ht) (hΦ₀ t ht) (hΦDer t ht) (ha t ht)
  · have hc := tendsto_exp_transition_deficit_ratio.comp hδne
    have hc' : Tendsto (fun t : ℝ ↦ (1 - a t) / δ t) (𝓝[>] u) (𝓝 1) := by
      change Tendsto (fun t ↦ (1 - Real.exp (-(δ t))) / δ t) (𝓝[>] u) (𝓝 1) at hc
      simpa only [hδa, a] using hc
    simpa only [c, Complex.ofReal_one] using tendsto_ofReal_iff.mpr hc'
  · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact unitDisk_isOpen).mpr ?_
    intro K hKD hK
    by_cases hne : K.Nonempty
    · obtain ⟨z₀, hz₀, hMax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
      let r := ‖z₀‖
      let B := Metric.closedBall (0 : ℂ) r
      let C := r * (1 + r) / (1 - r)
      have hr := mem_unitDisk.mp (hKD hz₀)
      have hC : 0 ≤ C := by dsimp only [C]; positivity
      have hKB : K ⊆ B := fun z hz ↦ by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hMax hz
      have hBD : B ⊆ unitDisk := fun z hz ↦ by
        have hzr : ‖z‖ ≤ r := by simpa only [B, Metric.mem_closedBall, dist_zero_right] using hz
        exact mem_unitDisk.mpr (hzr.trans_lt hr)
      have hSmall : ∀ᶠ t in 𝓝[>] u, MapsTo (Φ t) B B ∧ ∀ z ∈ B, ‖Φ t z - z‖ ≤ C * δ t := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have hmap : MapsTo (Φ t) unitDisk (Metric.closedBall 0 1) :=
          fun z hz ↦ Metric.ball_subset_closedBall (hΦM t ht hz)
        have hsz (z : ℂ) (hz : z ∈ B) : ‖Φ t z‖ ≤ ‖z‖ :=
          Complex.norm_le_norm_of_mapsTo_ball (hΦD t ht) hmap (hΦ₀ t ht) (mem_unitDisk.mp (hBD hz))
        refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
        · rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
          exact (hsz z (by rwa [Metric.mem_closedBall, dist_zero_right])).trans hz
        · have hzr : ‖z‖ ≤ r := by simpa only [B, Metric.mem_closedBall, dist_zero_right] using hz
          have hφ := norm_sub_id_of_disk_transition (hΦD t ht) (hΦM t ht) (hΦ₀ t ht)
            (Real.exp_pos _).le (ha t ht) (hΦDer t ht) (hBD hz)
          have hRatio : ‖z‖ * (1 + ‖z‖) / (1 - ‖z‖) ≤ C := by
            have hpoly : ‖z‖ * (1 + ‖z‖) ≤ r * (1 + r) :=
              mul_le_mul hzr (by linarith only [hzr]) (by positivity) (norm_nonneg _)
            exact (div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hr)
              (by linarith only [hzr])).trans (div_le_div_of_nonneg_right hpoly (sub_nonneg.mpr hr.le))
          have hδa' : 1 - a t ≤ δ t := by
            change 1 - Real.exp (u - t) ≤ δ t
            rw [← hδa t]
            exact (exp_transition_deficit_bounds (sub_nonneg.mpr ht.le)).2
          exact hφ.trans (by
            rw [mul_comm C]
            have hzlt := mem_unitDisk.mp (hBD hz)
            exact mul_le_mul hδa' hRatio
              (div_nonneg (by positivity) (sub_nonneg.mpr hzlt.le)) (sub_nonneg.mpr ht.le))
      have hF := tendstoLocallyUniformlyOn_nested_chain_right hu hd hi h₀ h₁ hsub
      have hDt : ∀ᶠ t in 𝓝[>] u, DifferentiableOn ℂ (F t) unitDisk := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact hd t (hu.trans ht.le)
      have hU := tendstoUniformlyOn_transition_linearization_error
        (K := B) (isCompact_closedBall (0 : ℂ) r) (convex_closedBall 0 r) hBD hC (hd u hu) hDt hF hδ hδ₀ hSmall
      refine (hU.mono hKB).congr ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      intro z hz
      have hzD := hKD hz
      have hden : (1 - (a t : ℂ)) ≠ 0 := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
        exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr (ha t ht)).ne'
      have hds := sub_smul_dslope (Φ t) (0 : ℂ) z
      rw [sub_zero, smul_eq_mul, hΦ₀ t ht, sub_zero] at hds
      have hpz : ((1 - a t : ℝ) : ℂ) * p t z = 1 - dslope (Φ t) 0 z := by
        change ((1 - a t : ℝ) : ℂ) * transitionDriver (Φ t) (a t) z = _
        rw [transitionDriver, Complex.ofReal_sub, Complex.ofReal_one, mul_comm,
          div_mul_cancel₀ _ hden]
      have hprod : c t * (p t z * (z * deriv (F u) z)) =
          deriv (F u) z * (z - Φ t z) / (δ t : ℂ) := by
        change (((1 - a t) / δ t : ℝ) : ℂ) * (p t z * (z * deriv (F u) z)) = _
        rw [Complex.ofReal_div]
        calc
          _ = (((1 - a t : ℝ) : ℂ) * p t z) * (z * deriv (F u) z) / (δ t : ℂ) := by ring
          _ = _ := by rw [hpz, ← hds]; ring
      change (F t z - F t (Φ t z) - deriv (F u) z * (z - Φ t z)) / (δ t : ℂ) =
        slope (fun s ↦ F s z) u t - c t * (p t z * (z * deriv (F u) z))
      have hteq : F t (Φ t z) = F u z := hΦE t ht hzD
      rw [hteq, hprod, slope_def_module, Complex.real_smul, Complex.ofReal_inv]
      change _ = (δ t : ℂ)⁻¹ * (F t z - F u z) - deriv (F u) z * (z - Φ t z) / (δ t : ℂ)
      ring
    · rw [not_nonempty_iff_eq_empty.mp hne]
      exact tendstoUniformlyOn_empty

end Zalcman
