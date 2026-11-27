/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.RiemannRadius
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Conformal-radius time for a nested family

Riemann maps of a proper simply connected exhaustion can be parametrized by
the logarithm of their conformal radius when both one-sided domain limits agree.
-/

@[expose] public section

namespace Zalcman

open Set Filter
open scoped Topology

private theorem continuousOn_conformal_radius {U : ℝ → Set ℂ}
    (hmonoU : MonotoneOn U (Ici 0))
    (hleftKernel : ∀ {u : ℝ} {s : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, s n < u) →
      Tendsto s atTop (𝓝 u) → (⋃ n, U (s n)) = U u)
    (hrightKernel : ∀ {u : ℝ} {s : ℕ → ℝ}, 0 ≤ u → (∀ n, u < s n) →
      Tendsto s atTop (𝓝 u) → interior (⋂ n, U (s n)) = U u)
    {F : ℝ → ℂ → ℂ} {r : ℝ → ℝ}
    (hF : ∀ t ∈ Ici 0, DifferentiableOn ℂ (F t) unitDisk)
    (hFi : ∀ t ∈ Ici 0, InjOn (F t) unitDisk) (hF₀ : ∀ t ∈ Ici 0, F t 0 = 0)
    (hr : ∀ t ∈ Ici 0, 0 < r t) (hFr : ∀ t ∈ Ici 0, deriv (F t) 0 = (r t : ℂ))
    (himage : ∀ t ∈ Ici 0, F t '' unitDisk = U t) : ContinuousOn r (Ici 0) := by
  have hmono : MonotoneOn r (Ici 0) := by
    intro s hs t ht hst
    apply conformal_radius_le_of_image_subset (hF s hs) (hF t ht) (hFi t ht) (hF₀ s hs) (hF₀ t ht)
      (hr s hs).le (hr t ht) (hFr s hs) (hFr t ht)
    rw [himage s hs, himage t ht]
    exact hmonoU hs ht hst
  intro u hu
  refine Metric.continuousWithinAt_iff.mpr fun ε hε ↦ ?_
  let d := fun n : ℕ ↦ 1 / ((n : ℝ) + 1)
  have hdpos (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hdle (n : ℕ) : d n ≤ 1 := by
    have hn : 0 ≤ (n : ℝ) := show 0 ≤ (n : ℝ) from Nat.cast_nonneg n
    dsimp [d]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hdanti : Antitone d := by
    intro i j hij
    exact one_div_le_one_div_of_le (by positivity) (add_le_add_left (Nat.cast_le.mpr hij) 1)
  have hdt : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let q := fun n ↦ u + d n
  have hqgt (n : ℕ) : u < q n := lt_add_of_pos_right _ (hdpos n)
  have hq0 (n : ℕ) : q n ∈ Ici (0 : ℝ) := (show 0 ≤ u from hu).trans (hqgt n).le
  have hqt : Tendsto q atTop (𝓝 u) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add hdt : Tendsto (fun n ↦ u + d n) atTop (𝓝 (u + 0)))
  have hqanti : Antitone q := fun i j hij ↦ add_le_add_right (hdanti hij) u
  have hright := tendsto_conformal_radius_of_interior_iInter (F := F ∘ q) (G := F u)
    (r := r ∘ q) (R := r u) (fun n ↦ hF _ (hq0 n)) (fun n ↦ hFi _ (hq0 n))
    (fun n ↦ hF₀ _ (hq0 n)) (fun n ↦ hr _ (hq0 n)) (fun n ↦ hFr _ (hq0 n))
    (hF u hu) (hFi u hu) (hF₀ u hu) (hr u hu) (hFr u hu)
    (by
      intro i j hij
      change F (q j) '' unitDisk ⊆ F (q i) '' unitDisk
      rw [himage _ (hq0 j), himage _ (hq0 i)]
      exact hmonoU (hq0 j) (hq0 i) (hqanti hij))
    (by
      simp only [Function.comp_apply, himage _ (hq0 _), himage u hu]
      exact hrightKernel hu hqgt hqt)
  obtain ⟨nR, hnR⟩ := (hright.1.eventually_lt_const (lt_add_of_pos_right (r u) hε)).exists
  have hUpper : r (q nR) < r u + ε := hnR
  have hLower : ∃ s ∈ Ici (0 : ℝ), ∃ δ > 0, r u - ε < r s ∧
      ∀ v ∈ Ici (0 : ℝ), dist v u < δ → s ≤ v := by
    by_cases hzero : u = 0
    · refine ⟨u, hu, 1, zero_lt_one, sub_lt_self _ hε, ?_⟩
      intro v hv _
      rwa [hzero]
    · have huPos : 0 < u := lt_of_le_of_ne hu (Ne.symm hzero)
      let p := fun n ↦ u * (1 - d n)
      have hp0 (n : ℕ) : p n ∈ Ici (0 : ℝ) := mul_nonneg huPos.le (sub_nonneg.mpr (hdle n))
      have hplt (n : ℕ) : p n < u := calc
        p n < u * 1 := mul_lt_mul_of_pos_left (sub_lt_self 1 (hdpos n)) huPos
        _ = u := mul_one u
      have hpt : Tendsto p atTop (𝓝 u) := by
        simpa only [sub_zero, mul_one] using
          (tendsto_const_nhds.mul (tendsto_const_nhds.sub hdt) :
            Tendsto (fun n ↦ u * (1 - d n)) atTop (𝓝 (u * (1 - 0))))
      have hpmono : Monotone p := fun i j hij ↦
        mul_le_mul_of_nonneg_left (sub_le_sub_left (hdanti hij) 1) huPos.le
      have hleft := tendsto_conformal_radius_of_iUnion (F := F ∘ p) (G := F u)
        (r := r ∘ p) (R := r u) (fun n ↦ hF _ (hp0 n)) (fun n ↦ hFi _ (hp0 n))
        (fun n ↦ hF₀ _ (hp0 n)) (fun n ↦ hr _ (hp0 n)) (fun n ↦ hFr _ (hp0 n))
        (hF u hu) (hFi u hu) (hF₀ u hu) (hr u hu) (hFr u hu)
        (by
          intro i j hij
          change F (p i) '' unitDisk ⊆ F (p j) '' unitDisk
          rw [himage _ (hp0 i), himage _ (hp0 j)]
          exact hmonoU (hp0 i) (hp0 j) (hpmono hij))
        (by
          simp only [Function.comp_apply, himage _ (hp0 _), himage u hu]
          exact hleftKernel hp0 hplt hpt)
      obtain ⟨nL, hnL⟩ := (hleft.eventually_const_lt (sub_lt_self (r u) hε)).exists
      refine ⟨p nL, hp0 nL, u - p nL, sub_pos.mpr (hplt nL), hnL, ?_⟩
      intro v _ hvd
      rw [Real.dist_eq, abs_lt] at hvd
      linarith only [hvd.1]
  obtain ⟨s, hs, δL, hδL, hsR, hsV⟩ := hLower
  refine ⟨min δL (q nR - u), lt_min hδL (sub_pos.mpr (hqgt nR)), ?_⟩
  intro v hv hvd
  have hsv := hsV v hv (hvd.trans_le (min_le_left _ _))
  have hvq : v ≤ q nR := by
    have hvd' := hvd.trans_le (min_le_right δL (q nR - u))
    rw [Real.dist_eq, abs_lt] at hvd'
    linarith only [hvd'.2]
  have hdeep := hsR.trans_le (hmono hs hv hsv)
  have hhigh := (hmono hv (hq0 nR) hvq).trans_lt hUpper
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith only [hdeep, hhigh]

/-- Normalized Riemann maps of a nested domain family, parametrized by conformal radius. -/
theorem exists_domain_chain_conformal_radius {U : ℝ → Set ℂ}
    (hopen : ∀ t ∈ Ici 0, IsOpen (U t)) (hproper : ∀ t ∈ Ici 0, U t ≠ univ)
    (hsc : ∀ t ∈ Ici 0, IsSimplyConnected (U t)) (hzero : 0 ∈ U 0)
    (hstrict : StrictMonoOn U (Ici 0))
    (hleftKernel : ∀ {u : ℝ} {s : ℕ → ℝ}, (∀ n, 0 ≤ s n) → (∀ n, s n < u) →
      Tendsto s atTop (𝓝 u) → (⋃ n, U (s n)) = U u)
    (hrightKernel : ∀ {u : ℝ} {s : ℕ → ℝ}, 0 ≤ u → (∀ n, u < s n) →
      Tendsto s atTop (𝓝 u) → interior (⋂ n, U (s n)) = U u)
    (hexhaust : (⋃ n : ℕ, U n) = univ) :
    ∃ (F : ℝ → ℂ → ℂ) (τ : ℝ → ℝ) (r₀ : ℝ), 0 < r₀ ∧ τ 0 = 0 ∧
      Set.MapsTo τ (Ici 0) (Ici 0) ∧ StrictMonoOn τ (Ici 0) ∧
      ∀ t ∈ Ici 0, DifferentiableOn ℂ (F t) unitDisk ∧
        BijOn (F t) unitDisk (U (τ t)) ∧ F t 0 = 0 ∧
        deriv (F t) 0 = ((r₀ * Real.exp t : ℝ) : ℂ) := by
  classical
  have hex (t : ℝ) (ht : t ∈ Ici 0) := exists_disk_map_with_positive_derivative
    (hopen t ht) (hproper t ht) (hsc t ht)
    (hstrict.monotoneOn self_mem_Ici ht ht hzero)
  choose F₀ hF₀ hB₀ hz₀ R₀ hpos₀ hder₀ using hex
  let F (t : ℝ) : ℂ → ℂ := if ht : t ∈ Ici 0 then F₀ t ht else 0
  let R (t : ℝ) : ℝ := if ht : t ∈ Ici 0 then R₀ t ht else 0
  have hF (t) (ht : t ∈ Ici 0) : DifferentiableOn ℂ (F t) unitDisk := by simpa only [F, dite_eq_left ht] using hF₀ t ht
  have hB (t) (ht : t ∈ Ici 0) : BijOn (F t) unitDisk (U t) := by
    simpa only [F, dite_eq_left ht] using hB₀ t ht
  have hz (t) (ht : t ∈ Ici 0) : F t 0 = 0 := by simpa only [F, dite_eq_left ht] using hz₀ t ht
  have hpos (t) (ht : t ∈ Ici 0) : 0 < R t := by simpa only [R, dite_eq_left ht] using hpos₀ t ht
  have hder (t) (ht : t ∈ Ici 0) : deriv (F t) 0 = (R t : ℂ) := by simpa only [F, R, dite_eq_left ht] using hder₀ t ht
  have hI (t) (ht : t ∈ Ici 0) : InjOn (F t) unitDisk := (hB t ht).injOn
  have hU (t) (ht : t ∈ Ici 0) : F t '' unitDisk = U t := (hB t ht).image_eq
  have hcont := continuousOn_conformal_radius hstrict.monotoneOn hleftKernel hrightKernel
    hF hI hz hpos hder hU
  have hsmono : StrictMonoOn R (Ici 0) := by
    intro s hs t ht hst
    apply conformal_radius_lt_of_image_ssubset (hF s hs) (hF t ht) (hI t ht) (hz s hs) (hz t ht)
      (hpos s hs).le (hpos t ht) (hder s hs) (hder t ht)
    rw [hU s hs, hU t ht]
    exact hstrict hs ht hst
  have hn₀ (n : ℕ) : (n : ℝ) ∈ Ici (0 : ℝ) := show 0 ≤ (n : ℝ) from Nat.cast_nonneg n
  have hdiv := tendsto_conformal_radius_atTop_of_iUnion_univ
    (F := fun n ↦ F (n : ℝ)) (r := fun n ↦ R (n : ℝ)) (fun n ↦ hF _ (hn₀ n))
    (fun n ↦ hI _ (hn₀ n)) (fun n ↦ hz _ (hn₀ n)) (fun n ↦ hpos _ (hn₀ n))
    (fun n ↦ hder _ (hn₀ n))
    (by
      intro i j hij
      change F (i : ℝ) '' unitDisk ⊆ F (j : ℝ) '' unitDisk
      rw [hU _ (hn₀ i), hU _ (hn₀ j)]
      exact hstrict.monotoneOn (hn₀ i) (hn₀ j) (Nat.cast_le.mpr hij))
    (by
      simp only [hU _ (hn₀ _)]
      exact hexhaust)
  have hp (t : ℝ) (ht : t ∈ Ici 0) : ∃ u ∈ Ici (0 : ℝ), R u = R 0 * Real.exp t := by
    obtain ⟨n, hn⟩ := (hdiv.eventually_ge_atTop (R 0 * Real.exp t)).exists
    have hleft : R 0 ≤ R 0 * Real.exp t := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr ht) (hpos 0 self_mem_Ici).le
    have hmem : R 0 * Real.exp t ∈ Icc (R 0) (R (n : ℝ)) := ⟨hleft, hn⟩
    obtain ⟨u, hu, he⟩ := intermediate_value_Icc (Nat.cast_nonneg n)
      (hcont.mono (fun _ hu ↦ hu.1)) hmem
    exact ⟨u, hu.1, he⟩
  choose τ₀ hτ₀ hτr₀ using hp
  let τ (t : ℝ) := if ht : t ∈ Ici 0 then τ₀ t ht else 0
  have hτ (t) (ht : t ∈ Ici 0) : τ t ∈ Ici 0 := by simpa only [τ, dite_eq_left ht] using hτ₀ t ht
  have hτr (t) (ht : t ∈ Ici 0) : R (τ t) = R 0 * Real.exp t := by simpa only [τ, dite_eq_left ht] using hτr₀ t ht
  have hR₀ : 0 < R 0 := hpos 0 self_mem_Ici
  have hτzero : τ 0 = 0 := by
    apply hsmono.injOn (hτ 0 self_mem_Ici) self_mem_Ici
    simpa only [Real.exp_zero, mul_one] using hτr 0 self_mem_Ici
  have hτmono : StrictMonoOn τ (Ici 0) := by
    intro s hs t ht hst
    have hRst : R (τ s) < R (τ t) := by
      rw [hτr s hs, hτr t ht]
      exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hst) hR₀
    exact lt_of_not_ge fun he ↦ hRst.not_ge (hsmono.monotoneOn (hτ t ht) (hτ s hs) he)
  refine ⟨F ∘ τ, τ, R 0, hR₀, hτzero, fun t ht ↦ hτ t ht, hτmono, ?_⟩
  intro t ht
  refine ⟨hF _ (hτ t ht), hB _ (hτ t ht), hz _ (hτ t ht), ?_⟩
  change deriv (F (τ t)) 0 = _
  rw [hder _ (hτ t ht), hτr t ht]

end Zalcman
