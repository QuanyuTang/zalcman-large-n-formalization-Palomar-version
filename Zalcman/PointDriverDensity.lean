/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.AmbientChainGeometry
public import Zalcman.ControlledTriangularStability
public import Zalcman.DriverChattering
public import Zalcman.FiniteDriverContinuation
public import Zalcman.GeneralizedChainMoments
public import Zalcman.NormalCoefficientLimit
public import Zalcman.TerminalKoebeChain
import Mathlib.Tactic.Positivity

/-!
# Density of chains with finite unit drivers

First prescribe the terminal map. Approximate the generalized time-dependent
moments by finite unit phases and compare the two finite triangular coefficient
systems with their common terminal values.
-/

public section

namespace Zalcman

open Filter Finset MeasureTheory Set
open scoped Topology

private theorem exists_finite_driver_terminal_approximation
    {F : ℝ → ℂ → ℂ} {T : ℝ} (hT : 0 < T)
    (hF : ∀ t ∈ Set.Ici 0, ExponentialDiskMap t (F t))
    (hNest : ∀ s ∈ Set.Ici 0, ∀ t ∈ Set.Ici 0, s ≤ t → F s '' unitDisk ⊆ F t '' unitDisk)
    (hTerm : EqOn (F T) (fun z ↦ (Real.exp T : ℂ) * koebe z) unitDisk)
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : FiniteKoebeDriverChain, ∀ n ≤ M,
      ‖coeff (P.chain.maps 0) n - coeff (F 0) n‖ < ε := by
  obtain ⟨p, hpMeas, hpHull, hAac, hAode⟩ := exists_measurable_hull_moments_of_nested_chain hT.le
    (fun t ht ↦ (hF t ht).holomorphic) (fun t ht ↦ (hF t ht).injective)
    (fun t ht ↦ (hF t ht).map_zero) (fun t ht ↦ (hF t ht).deriv_zero) hNest
  have hpBound (j : ℕ) : ∀ᵐ u ∂volume.restrict (Set.Ioc (0 : ℝ) T), ‖p j u‖ ≤ 1 := by
    refine (hpHull (j + 1)).mono fun u hu ↦ ?_
    exact (norm_le_pi_norm (fun i : Fin (j + 1) ↦ p i u) ⟨j, Nat.lt_succ_self j⟩).trans
      (norm_le_one_of_mem_closedUnitMomentHull hu)
  obtain ⟨C, hC, hStable⟩ := exists_coefficient_stability_constant M hT.le hAac hpMeas hpBound hAode
  let δ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  let m (u : ℝ) (j : Fin M) := p j u
  have hm : Measurable m := Measurable.of_eval (f := m) (fun j ↦ hpMeas j)
  obtain ⟨N, a, controls, ha, ha₀, haN, hControls, hκMeas, hκUnit, hPrimitive⟩ :=
    exists_piecewise_unit_primitive_approximation hT hδ hm (hpHull M)
  let κ := glueIntervalControls N a controls
  let q (j : ℕ) (u : ℝ) := κ u ^ (j + 1)
  have hReal {i : ℕ} (hi : i < N) (H : ℂ → ℂ) (hH : ExponentialDiskMap (a (i + 1)) H) :
      Nonempty (FiniteDriverChain (a i) (a (i + 1)) (controls i) H) := by
    obtain ⟨r, s, ζ, hs, hs₀, hsr, hζ, he⟩ := hControls i hi
    rw [he, ← hs₀, ← hsr]
    exact exists_finiteDriverChain_of_intervalControl hs hζ (hsr.symm ▸ hH)
  let H (z : ℂ) := (Real.exp T : ℂ) * koebe z
  have hH : ExponentialDiskMap (a N) H := by
    rw [haN]
    exact .of_normalizedUnivalent koebe_normalizedUnivalent T
  obtain ⟨W⟩ : Nonempty (FiniteDriverChain 0 T κ H) := by
    have e := exists_finiteDriverChain_of_partition ha (fun i hi H hH ↦ hReal (i := i) hi H hH) hH
    change Nonempty (FiniteDriverChain (a 0) (a N) κ H) at e
    rw [ha₀, haN] at e
    exact e
  let P : FiniteKoebeDriverChain := ⟨T, hT, κ, hκMeas, hκUnit, W⟩
  let G := W.koebeContinuation
  let B := normalizedChainCoeff G
  have hG (t : ℝ) : ExponentialDiskMap t (G t) := W.koebeContinuation_map t
  have hBac (n : ℕ) : AbsolutelyContinuousOnInterval (B n) 0 T := by
    have hCac := (nested_chain_coefficients_time_regular hT.le
      (fun t _ ↦ (hG t).holomorphic) (fun t _ ↦ (hG t).injective)
      (fun t _ ↦ (hG t).map_zero) (fun t _ ↦ (hG t).deriv_zero)
      (fun _ hs _ ht hst ↦ W.koebeContinuation_nested hT.le hs ht hst)).1 (n + 1)
    have hReal : ContDiff ℝ 1 (fun u : ℝ ↦ Real.exp (-u)) := by fun_prop
    have hRealAC : AbsolutelyContinuousOnInterval (fun u : ℝ ↦ Real.exp (-u)) 0 T :=
      hReal.contDiffOn.absolutelyContinuousOnInterval
    simpa only [B, normalizedChainCoeff, Complex.real_smul] using! hRealAC.fun_smul hCac
  have hBode : ∀ᵐ u : ℝ ∂volume, u ∈ Set.Ioo 0 T → ∀ n,
      HasDerivAt (B n) ((n : ℂ) * B n u +
        2 * ∑ j ∈ range n, ((j : ℂ) + 1) * B j u * q (n - 1 - j) u) u := by
    filter_upwards [W.koebeContinuation_velocity] with u hu hut
    obtain ⟨hκ, hSlope⟩ := hu hut
    intro n
    have h := hasDerivAt_radialTaylorCoeff_exp_normalization hκ.le (fun t ↦ (hG t).holomorphic) hSlope n
    have hidx (j : ℕ) (hj : j ∈ range n) : n - 1 - j + 1 = n - j := by
      have := mem_range.mp hj
      omega
    have hsum :
        (∑ j ∈ range n, ((j : ℂ) + 1) * B j u * q (n - 1 - j) u) =
          ∑ j ∈ range n, ((j : ℂ) + 1) * B j u * κ u ^ (n - j) := by
      apply sum_congr rfl
      intro j hj
      rw [show q (n - 1 - j) u = κ u ^ (n - 1 - j + 1) from rfl, hidx j hj]
    have hFun : B n = fun t : ℝ ↦ (Real.exp (-t) : ℂ) * coeff (G t) (n + 1) := by
      funext t
      simp only [B, normalizedChainCoeff]
    rw [hFun, hsum]
    simpa only [B, normalizedChainCoeff, coeff_const_mul] using h
  have hEnd (n : ℕ) : normalizedChainCoeff F n T = B n T := by
    simp only [B, normalizedChainCoeff]
    congr 1
    apply coeff_congr_on_unitDisk
    have hEq : G T = W.maps T := W.koebeContinuation_eq ⟨hT.le, le_rfl⟩
    rw [hEq]
    exact hTerm.trans W.terminal.symm
  have hqMeas (j : ℕ) : Measurable (q j) := hκMeas.pow_const _
  have hqBound (j : ℕ) : ∀ᵐ u ∂volume.restrict (Set.Ioc (0 : ℝ) T), ‖q j u‖ ≤ 1 := by
    refine .of_forall fun u ↦ ?_
    change ‖κ u ^ (j + 1)‖ ≤ 1
    rw [norm_pow, show ‖κ u‖ = 1 from hκUnit u, one_pow]
  have hmI : IntervalIntegrable m volume 0 T :=
    intervalIntegrable_of_measurable_bounded_moments hT.le hm
      ((hpHull M).mono fun _ ↦ norm_le_one_of_mem_closedUnitMomentHull)
  have hqI : IntervalIntegrable (fun u ↦ unitMomentCurve M (κ u)) volume 0 T :=
    intervalIntegrable_unitMoments hT.le hκMeas hκUnit
  have hClose (j : ℕ) (hj : j < M) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) T) :
      ‖∫ v in 0..u, (p j v - q j v)‖ ≤ δ := by
    have hFull := hqI.sub hmI
    have hPart : IntervalIntegrable (fun v ↦ unitMomentCurve M (κ v) - m v) volume 0 u :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hu.1).mpr
        (hFull.1.mono_set (fun _ hv ↦ ⟨hv.1, hv.2.trans hu.2⟩))
    simp_rw [← neg_sub (q j _)]
    rw [intervalIntegral.integral_neg, norm_neg]
    have h := (norm_moment_coordinate_intervalIntegral_le hPart ⟨j, hj⟩).trans (hPrimitive u hu).le
    simpa only [unitMomentCurve, m, q, Pi.sub_apply] using h
  have hEstimate := hStable (B := B) (q := q) hδ.le hBac hqMeas hqBound hBode
    (fun n _ ↦ hEnd n) hClose
  have hδC : C * δ < ε := by
    have h := (div_lt_iff₀ (show 0 < C + 1 by positivity)).2 (show C * ε < ε * (C + 1) by
      nlinarith only [hε])
    simpa only [δ, mul_div_assoc] using h
  refine ⟨P, fun n hn ↦ ?_⟩
  cases n with
  | zero =>
    simp only [coeff_zero, P.normalized_initial.map_zero, (hF 0 le_rfl).map_zero, sub_self, norm_zero]
    exact hε
  | succ n =>
    have hG₀ : G 0 = W.maps 0 := W.koebeContinuation_eq ⟨le_rfl, hT.le⟩
    have h := (hEstimate n (by omega)).trans_lt hδC
    simpa only [B, normalizedChainCoeff, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul,
      hG₀, P, norm_sub_rev] using h

private theorem eventually_coeff_close_of_locallyUniform {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (h : TendstoLocallyUniformlyOn F f l unitDisk)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) unitDisk) (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ n ≤ M, ‖coeff (F i) n - coeff f n‖ < ε := by
  have hFinite : ∀ᶠ i in l, ∀ n ∈ range (M + 1), ‖coeff (F i) n - coeff f n‖ < ε :=
    (range (M + 1)).eventually_all.mpr fun n _ ↦ by
      filter_upwards [(tendsto_coeff h hF n).eventually (Metric.ball_mem_nhds _ hε)] with i hi
      simpa only [Metric.mem_ball, dist_eq_norm] using hi
  exact hFinite.mono fun i hi n hn ↦ hi n (mem_range.mpr (Nat.lt_succ_of_le hn))

/-- Every normalized univalent map is a locally uniform limit of initial
maps of finite point-driver chains terminating at Koebe. -/
theorem exists_locallyUniform_finiteKoebeDriverChain
    {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    ∃ P : ℕ → FiniteKoebeDriverChain,
      TendstoLocallyUniformlyOn (fun n ↦ (P n).chain.maps 0) f atTop unitDisk := by
  classical
  obtain ⟨F, hFconv, hFmap, hFnest⟩ := exists_nested_chain_approximation hf
  have hF (i : ℕ) (t : ℝ) (ht : t ∈ Set.Ici 0) : ExponentialDiskMap t (F i t) := by
    obtain ⟨hd, hi, h₀, h₁⟩ := hFmap i t ht
    exact ⟨hd, hi, h₀, h₁⟩
  have hExact (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
      ∃ P : FiniteKoebeDriverChain, ∀ n ≤ M,
        ‖coeff (P.chain.maps 0) n - coeff f n‖ < ε := by
    have hthird : 0 < ε / 3 := by positivity
    obtain ⟨i, hi⟩ := (eventually_coeff_close_of_locallyUniform hFconv
      (.of_forall fun i ↦ (hF i 0 le_rfl).holomorphic) M hthird).exists
    obtain ⟨G, hGconv, hG⟩ := exists_terminalKoebe_nested_chain_approximation (hF i) (hFnest i)
    have hPos : ∀ᶠ T : ℝ in atTop, 0 < T := eventually_gt_atTop _
    have hGdiff : ∀ᶠ T in atTop, DifferentiableOn ℂ (G T 0) unitDisk :=
      hPos.mono fun T hT ↦ ((hG T hT).1 0 le_rfl).holomorphic
    obtain ⟨T, hT, hClose⟩ := (hPos.and
      (eventually_coeff_close_of_locallyUniform hGconv hGdiff M hthird)).exists
    obtain ⟨hGmap, hGnest, hGterm⟩ := hG T hT
    obtain ⟨P, hP⟩ := exists_finite_driver_terminal_approximation hT hGmap hGnest hGterm M hthird
    refine ⟨P, fun n hn ↦ ?_⟩
    calc
      _ ≤ ‖coeff (P.chain.maps 0) n - coeff (G T 0) n‖ +
          (‖coeff (G T 0) n - coeff (F i 0) n‖ + ‖coeff (F i 0) n - coeff f n‖) := by
        simp only [← dist_eq_norm]
        exact (dist_triangle _ (coeff (G T 0) n) _).trans
          (add_le_add (le_refl _) (dist_triangle _ (coeff (F i 0) n) _))
      _ < ε := by linarith only [hP n hn, hClose n hn, hi n hn]
  let ε (M : ℕ) : ℝ := 1 / ((M : ℝ) + 1)
  choose P hP using fun M ↦ hExact M (ε := ε M) (by dsimp only [ε]; positivity)
  refine ⟨P, tendstoLocallyUniformlyOn_of_tendsto_coeff (fun n ↦ (P n).normalized_initial) hf ?_⟩
  intro n
  refine Metric.tendsto_nhds.mpr fun d hd ↦ ?_
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop n, hεlim.eventually_lt_const hd] with M hn hM
  simpa only [dist_eq_norm] using (hP M n hn).trans hM

/-- The finite driver approximants supply the certificates for the Milin energy identity. -/
theorem exists_locallyUniform_koebeTerminatingLogarithmicChain
    {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    ∃ P : ℕ → KoebeTerminatingLogarithmicChain,
      TendstoLocallyUniformlyOn (fun n ↦ (P n).maps 0) f atTop unitDisk := by
  obtain ⟨Q, hQ⟩ := exists_locallyUniform_finiteKoebeDriverChain hf
  choose P hP using fun n ↦
    (Q n).chain.exists_koebeTerminatingLogarithmicChain (Q n).duration_pos.le
  exact ⟨P, hQ.congr (fun n z _ ↦ congrFun (hP n).symm z)⟩

/-- A common nonnegative triangular representation exists for every normalized
univalent function. -/
theorem exists_nonnegative_milin_representation {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    ∃ ρ : ℕ → ℝ, ρ 0 = 0 ∧ (∀ j, 0 ≤ ρ j) ∧ ∀ M,
      (∑ j ∈ range (M + 1), connectionCoefficient M j * ρ j) =
        (milinCoefficients hf).milinSum (M + 1) := by
  obtain ⟨P, hP⟩ := exists_locallyUniform_koebeTerminatingLogarithmicChain hf
  exact exists_nonnegative_milin_representation_of_locallyUniform_chain_limits P hf hP

end Zalcman
