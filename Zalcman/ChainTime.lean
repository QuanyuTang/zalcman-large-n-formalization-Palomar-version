/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.ChainIncrement
public import Zalcman.RiemannTransition
public import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lipschitz time dependence of normalized nested disk maps

The transition estimate is uniform on closed subdisks and gives a Lipschitz
constant in time on every finite interval.
-/

public section

namespace Zalcman

open Filter Set
open scoped NNReal Topology

/-- The exponential transition deficit is at most the positive time increment. -/
theorem exp_transition_deficit_bounds {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ 1 - Real.exp (-h) ∧ 1 - Real.exp (-h) ≤ h := by
  have hle : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hh)
  exact ⟨sub_nonneg.mpr hle, by linarith only [Real.add_one_le_exp (-h)]⟩

/-- Dividing the transition deficit by the time increment has limit one. -/
theorem tendsto_exp_transition_deficit_ratio :
    Tendsto (fun h : ℝ ↦ (1 - Real.exp (-h)) / h) (𝓝[≠] 0) (𝓝 1) := by
  have hn : HasDerivAt (fun h : ℝ ↦ -h) (-1) 0 := (hasDerivAt_id (0 : ℝ)).neg
  have he : HasDerivAt (fun h : ℝ ↦ Real.exp (-h)) (-1) 0 := by
    simpa only [neg_zero, Real.exp_zero, one_mul] using hn.exp
  have hdiff : HasDerivAt (fun h : ℝ ↦ 1 - Real.exp (-h)) 1 0 := by
    simpa only [zero_sub, neg_neg] using (hasDerivAt_const 0 (1 : ℝ)).fun_sub he
  simpa only [slope_fun_def_field, neg_zero, Real.exp_zero, sub_self, sub_zero] using
    hdiff.tendsto_slope

private theorem exp_normalized_map {f : ℂ → ℂ} {t : ℝ}
    (hd : DifferentiableOn ℂ f unitDisk) (hi : InjOn f unitDisk) (h₀ : f 0 = 0)
    (h₁ : deriv f 0 = (Real.exp t : ℂ)) :
    NormalizedUnivalent (fun z ↦ (Real.exp t : ℂ)⁻¹ * f z) := by
  have hn : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)
  refine ⟨hd.const_mul _, fun _ hz _ hw he ↦ hi hz hw (mul_left_cancel₀ (inv_ne_zero hn) he), ?_, ?_⟩
  · rw [h₀, mul_zero]
  · rw [deriv_const_mul_field, h₁, inv_mul_cancel₀ hn]

/-- A uniform derivative oscillation bound on a segment controls the error
of the indicated linear approximation at the endpoints. -/
theorem norm_sub_linearization_le_of_deriv_oscillation {f : ℂ → ℂ} {x y d : ℂ} {ε : ℝ}
    (hf : ∀ z ∈ segment ℝ x y, DifferentiableAt ℂ f z)
    (hε : ∀ z ∈ segment ℝ x y, ‖deriv f z - d‖ ≤ ε) :
    ‖f y - f x - d * (y - x)‖ ≤ ε * ‖y - x‖ := by
  have hder (z : ℂ) (hz : z ∈ segment ℝ x y) : HasDerivWithinAt (fun w ↦ f w - d * w)
      (deriv f z - d) (segment ℝ x y) z :=
    ((hf z hz).hasDerivAt.fun_sub (hasDerivAt_const_mul d)).hasDerivWithinAt
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hε (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  calc
    _ = ‖(f y - d * y) - (f x - d * x)‖ := by congr 1; ring
    _ ≤ _ := hmv

/-- Negligibility of the linearization remainder of small disk transitions on
a fixed compact convex subdisk. -/
theorem tendstoUniformlyOn_transition_linearization_error {ι : Type*} {l : Filter ι}
    {F T : ι → ℂ → ℂ} {f : ℂ → ℂ} {δ : ι → ℝ} {K : Set ℂ} {C : ℝ}
    (hK : IsCompact K) (hc : Convex ℝ K) (hKD : K ⊆ unitDisk) (hC : 0 ≤ C)
    (hf : DifferentiableOn ℂ f unitDisk)
    (hd : ∀ᶠ i in l, DifferentiableOn ℂ (F i) unitDisk)
    (hF : TendstoLocallyUniformlyOn F f l unitDisk)
    (hδ : Tendsto δ l (𝓝 0)) (hδ₀ : ∀ᶠ i in l, 0 < δ i)
    (hT : ∀ᶠ i in l, MapsTo (T i) K K ∧ ∀ z ∈ K, ‖T i z - z‖ ≤ C * δ i) :
    TendstoUniformlyOn
      (fun i z ↦ (F i z - F i (T i z) - deriv f z * (z - T i z)) / (δ i : ℂ))
      (fun _ ↦ 0) l K := by
  have hopen : IsOpen unitDisk := Metric.isOpen_ball
  have hDU := (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).mp
    (hF.deriv hd hopen) K hKD hK
  have hU := hK.uniformContinuousOn_of_continuous ((hf.deriv hopen).continuousOn.mono hKD)
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
  let η := ε / (4 * (C + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨γ, hγ, hγU⟩ := Metric.uniformContinuousOn_iff.mp hU η hη
  have hdSmall : ∀ᶠ i in l, δ i < γ / (C + 1) := hδ.eventually_lt_const (div_pos hγ (by positivity))
  have hηC : 2 * η * C < ε := by
    calc
      _ ≤ 2 * η * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ε / 2 := by
        dsimp only [η]
        field_simp [show C + 1 ≠ 0 by positivity]
        ring
      _ < ε := by linarith
  filter_upwards [hd, hδ₀, hT, hdSmall, Metric.tendstoUniformlyOn_iff.mp hDU η hη]
    with i hdi hδi hTi hsmall hDsmall
  intro z hz
  have hTz : T i z ∈ K := hTi.1 hz
  have hNear : ‖T i z - z‖ ≤ C * δ i := hTi.2 z hz
  have hγ' : C * δ i < γ := by
    have hmul := (lt_div_iff₀ (by positivity : 0 < C + 1)).mp hsmall
    linarith only [show δ i * C + δ i < γ by simpa only [mul_add, mul_one] using hmul,
      mul_comm (δ i) C, hδi]
  have hSeg : segment ℝ (T i z) z ⊆ K := hc.segment_subset hTz hz
  have hSegDiff (w : ℂ) (hw : w ∈ segment ℝ (T i z) z) : DifferentiableAt ℂ (F i) w :=
    hdi.differentiableAt (hopen.mem_nhds (hKD (hSeg hw)))
  have hOsc (w : ℂ) (hw : w ∈ segment ℝ (T i z) z) : ‖deriv (F i) w - deriv f z‖ ≤ 2 * η := by
    have hwK : w ∈ K := hSeg hw
    have hwZ : w ∈ segment ℝ z (T i z) := by rwa [segment_symm]
    have hdist : dist w z < γ := by
      rw [dist_eq_norm]
      exact (norm_sub_le_of_mem_segment hwZ).trans_lt (hNear.trans_lt hγ')
    have h1 : dist (deriv (F i) w) (deriv f w) < η := by
      rw [dist_comm]
      exact hDsmall w hwK
    have h2 := hγU w hwK z hz hdist
    rw [← dist_eq_norm, two_mul]
    exact (dist_triangle _ _ _).trans (add_lt_add h1 h2).le
  have herr := norm_sub_linearization_le_of_deriv_oscillation hSegDiff hOsc
  change dist (0 : ℂ) ((F i z - F i (T i z) - deriv f z * (z - T i z)) / (δ i : ℂ)) < ε
  rw [dist_zero_left, norm_div, Complex.norm_of_nonneg hδi.le]
  refine lt_of_le_of_lt ((div_le_iff₀ hδi).mpr ?_) hηC
  calc
    _ ≤ 2 * η * ‖z - T i z‖ := herr
    _ ≤ 2 * η * (C * δ i) := by
      rw [norm_sub_rev]
      exact mul_le_mul_of_nonneg_left hNear (by positivity)
    _ = (2 * η * C) * δ i := by ring

/-- Nested holomorphic disk maps of conformal radius `exp t` are uniformly
Lipschitz in time on each compact subdisk and each bounded time interval. -/
theorem exists_lipschitzOnWith_nested_chain {F : ℝ → ℂ → ℂ} {T r : ℝ}
    (hr₀ : 0 ≤ r) (hr : r < 1)
    (hd : ∀ t ∈ Ici 0, DifferentiableOn ℂ (F t) unitDisk)
    (hi : ∀ t ∈ Ici 0, InjOn (F t) unitDisk) (h₀ : ∀ t ∈ Ici 0, F t 0 = 0)
    (h₁ : ∀ t ∈ Ici 0, deriv (F t) 0 = (Real.exp t : ℂ))
    (hsub : ∀ s ∈ Ici 0, ∀ t ∈ Ici 0, s ≤ t → F s '' unitDisk ⊆ F t '' unitDisk) :
    ∃ K : ℝ≥0, ∀ z : ℂ, ‖z‖ ≤ r → LipschitzOnWith K (fun u ↦ F u z) (Icc 0 T) := by
  let C := 2 / (1 - r) ^ 3 * (r * (1 + r) / (1 - r))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let K : ℝ≥0 := ⟨C * Real.exp T, mul_nonneg hC (Real.exp_pos T).le⟩
  let L : ℝ≥0 := ⟨Real.exp T, (Real.exp_pos T).le⟩
  have hLipExp : LipschitzOnWith L Real.exp (Icc (0 : ℝ) T) := by
    refine (convex_Icc _ _).lipschitzOnWith_of_nnnorm_deriv_le
      (fun _ _ ↦ Real.differentiable_exp.differentiableAt) ?_
    intro t ht
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.deriv_exp]
    change ‖Real.exp t‖ ≤ Real.exp T
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos t).le]
    exact Real.exp_le_exp.mpr ht.2
  refine ⟨K, fun z hz ↦ LipschitzOnWith.of_dist_le_mul fun s hs t ht ↦ ?_⟩
  have hordered (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s < t) :
      dist (F t z) (F s z) ≤ (K : ℝ) * dist t s := by
    obtain ⟨phi, hphi, hmap, hzero, heq, hder⟩ := exists_normalized_disk_transition
      (hd s hs.1) (hd t ht.1) (hi t ht.1) (h₀ s hs.1) (h₀ t ht.1)
      (hsub s hs.1 t ht.1 hst.le)
    have hder' : deriv phi 0 = (Real.exp (s - t) : ℂ) := by
      rw [hder, h₁ s hs.1, h₁ t ht.1, Real.exp_sub, Complex.ofReal_div]
    let f := fun w ↦ (Real.exp s : ℂ)⁻¹ * F s w
    let g := fun w ↦ (Real.exp t : ℂ)⁻¹ * F t w
    have hg : NormalizedUnivalent g := exp_normalized_map (hd t ht.1) (hi t ht.1) (h₀ t ht.1) (h₁ t ht.1)
    have hEs : (Real.exp s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero s)
    have hEt : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)
    have hnormEq : Set.EqOn (fun w ↦ (Real.exp s : ℂ) * f w)
        (fun w ↦ (Real.exp t : ℂ) * g (phi w)) unitDisk := by
      intro w hw
      simpa only [f, g, ← mul_assoc, mul_inv_cancel₀ hEs, mul_inv_cancel₀ hEt, one_mul] using
        (heq hw).symm
    have hinc := norm_radial_chain_increment_le hg hst hphi hmap hzero hder' hnormEq hr hz
    have hinc' : dist (F t z) (F s z) ≤ C * (Real.exp t - Real.exp s) := by
      simpa only [C, dist_eq_norm, f, g, ← mul_assoc, mul_inv_cancel₀ hEs, mul_inv_cancel₀ hEt, one_mul] using hinc
    have htime := hLipExp.dist_le_mul t ht s hs
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hst.le))] at htime
    have htime' : Real.exp t - Real.exp s ≤ Real.exp T * dist t s := htime
    change dist (F t z) (F s z) ≤ (C * Real.exp T) * dist t s
    rw [mul_assoc]
    exact hinc'.trans (mul_le_mul_of_nonneg_left htime' hC)
  rcases lt_trichotomy s t with hst | rfl | hts
  · simpa only [dist_comm (F t z) (F s z), dist_comm t s] using hordered s t hs ht hst
  · simp
  · exact hordered t s ht hs hts

/-- Nested maps with the exponential conformal-radius parametrization depend
locally uniformly continuously on time from the right. -/
theorem tendstoLocallyUniformlyOn_nested_chain_right {F : ℝ → ℂ → ℂ} {u : ℝ} (hu : 0 ≤ u)
    (hd : ∀ t ∈ Ici 0, DifferentiableOn ℂ (F t) unitDisk)
    (hi : ∀ t ∈ Ici 0, InjOn (F t) unitDisk) (h₀ : ∀ t ∈ Ici 0, F t 0 = 0)
    (h₁ : ∀ t ∈ Ici 0, deriv (F t) 0 = (Real.exp t : ℂ))
    (hsub : ∀ s ∈ Ici 0, ∀ t ∈ Ici 0, s ≤ t → F s '' unitDisk ⊆ F t '' unitDisk) :
    TendstoLocallyUniformlyOn F (F u) (𝓝[>] u) unitDisk := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball).mpr ?_
  intro A hAD hA
  by_cases hAne : A.Nonempty
  · obtain ⟨x, hxA, hxMax⟩ := hA.exists_isMaxOn hAne continuous_norm.continuousOn
    obtain ⟨K, hK⟩ := exists_lipschitzOnWith_nested_chain (T := u + 1) (norm_nonneg x)
      (mem_unitDisk.mp (hAD hxA)) hd hi h₀ h₁ hsub
    have huT : u ∈ Icc (0 : ℝ) (u + 1) := ⟨hu, le_add_of_nonneg_right zero_le_one⟩
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
    let δ := min 1 (ε / ((K : ℝ) + 1))
    have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε (by positivity))
    have hNear : ∀ᶠ t in 𝓝[>] u, dist t u < δ :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds u hδ)
    filter_upwards [self_mem_nhdsWithin, hNear] with t htu ht
    intro z hz
    have hut : u < t := htu
    have htT : t ∈ Icc (0 : ℝ) (u + 1) := by
      refine ⟨hu.trans hut.le, ?_⟩
      have hdist := ht.trans_le (min_le_left (1 : ℝ) (ε / ((K : ℝ) + 1)))
      rw [Real.dist_eq, abs_lt] at hdist
      linarith only [hdist.2]
    have hL := (hK z (hxMax hz)).dist_le_mul u huT t htT
    rw [dist_comm u t] at hL
    have ht' : dist t u < ε / ((K : ℝ) + 1) := ht.trans_le (min_le_right _ _)
    have hKle : (K : ℝ) ≤ (K : ℝ) + 1 := by linarith
    have htd : ((K : ℝ) + 1) * dist t u < ε := by
      rw [mul_comm]
      exact (lt_div_iff₀ (by positivity)).mp ht'
    exact hL.trans_lt ((mul_le_mul_of_nonneg_right hKle dist_nonneg).trans_lt htd)
  · rw [not_nonempty_iff_eq_empty.mp hAne]
    exact tendstoUniformlyOn_empty

end Zalcman
