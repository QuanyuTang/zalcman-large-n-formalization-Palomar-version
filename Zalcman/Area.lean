/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Basic
public import Zalcman.Upstream.Brennan.Distortion
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-!
# Consequences of the area theorem for the first coefficients

The integral form of the area theorem supplies the two low-order bounds and the
rigidity of the second Taylor coefficient.
-/

namespace Zalcman

open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ComplexConjugate
open OAI.Brennan (disk Schlicht)

private lemma NormalizedUnivalent.schlicht {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    Schlicht f := ⟨⟨hf.holomorphic, hf.injective⟩, hf.map_zero, hf.deriv_zero⟩

/-- A univalent holomorphic function has no critical points in the disk. -/
theorem NormalizedUnivalent.deriv_ne_zero {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {z : ℂ} (hz : z ∈ unitDisk) : deriv f z ≠ 0 :=
  OAI.Brennan.univalent_deriv_ne_zero Metric.isOpen_ball hf.schlicht.1 hz

/-- The sharp bounds for the norm of the first derivative on the unit disk. -/
theorem NormalizedUnivalent.distortion_bounds {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {z : ℂ} (hz : z ∈ unitDisk) :
    (1 - ‖z‖) / (1 + ‖z‖) ^ 3 ≤ ‖deriv f z‖ ∧
      ‖deriv f z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) ^ 3 :=
  OAI.Brennan.schlicht_deriv_bounds hf.schlicht hz

private lemma volumeReal_closedBall (r : ℝ) (hr : 0 ≤ r) :
    volume.real (Metric.closedBall (0 : ℂ) r) = r ^ 2 * Real.pi := by
  rw [measureReal_def, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.coe_toReal]
  rfl

private lemma area_eq_const_deriv {h H : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h disk)
    (hH : OAI.Brennan.UnivalentOn H (disk \ {0}))
    (hdef : ∀ z ∈ disk, z ≠ 0 → H z = z⁻¹ + h z)
    (heq : ‖deriv h 0‖ = 1) :
    EqOn (deriv h) (fun _ ↦ deriv h 0) disk := by
  let g : ℂ → ℝ := fun z ↦ ‖deriv h z - deriv h 0‖ ^ 2
  have hd := hh.deriv Metric.isOpen_ball
  have hbound (r : ℝ) (hr : 0 < r) (hr₁ : r < 1) :
      ∫ z in Metric.closedBall (0 : ℂ) r, g z ≤
        r ^ 2 * Real.pi * ((r ^ 2)⁻¹ ^ 2 - 1) := by
    let K := Metric.closedBall (0 : ℂ) r
    have hdc : ContinuousOn (deriv h) K :=
      hd.continuousOn.mono (Metric.closedBall_subset_ball hr₁)
    have hdi : IntegrableOn (deriv h) K volume :=
      hdc.integrableOn_compact (isCompact_closedBall 0 r)
    have hddi : IntegrableOn (fun z ↦ ‖deriv h z‖ ^ 2) K volume :=
      (hdc.norm.pow 2).integrableOn_compact (isCompact_closedBall 0 r)
    have hconst : IntegrableOn (fun _ : ℂ ↦ (1 : ℝ)) K :=
      integrableOn_const (isCompact_closedBall 0 r).measure_ne_top
    have hinner : IntegrableOn (fun z ↦ 2 * inner ℝ (deriv h 0) (deriv h z)) K :=
      (hdi.const_inner (deriv h 0)).const_mul 2
    have hg : g = fun z ↦ ‖deriv h z‖ ^ 2 - 2 * inner ℝ (deriv h 0) (deriv h z) + 1 := by
      funext z
      change ‖deriv h z - deriv h 0‖ ^ 2 = _
      rw [norm_sub_sq_real, real_inner_comm, heq, one_pow]
    have hformula : ∫ z in K, g z = (∫ z in K, ‖deriv h z‖ ^ 2) - volume.real K := by
      rw [hg]
      let j : ℂ → ℝ := fun z ↦ ‖deriv h z‖ ^ 2 - 2 * inner ℝ (deriv h 0) (deriv h z)
      have hsub : IntegrableOn j K volume := hddi.sub hinner
      have hji : (∫ z in K, j z) = (∫ z in K, ‖deriv h z‖ ^ 2) -
          (∫ z in K, 2 * inner ℝ (deriv h 0) (deriv h z)) := integral_sub hddi hinner
      calc
        _ = (∫ z in K, j z) + (∫ _ : ℂ in K, (1 : ℝ)) := integral_add hsub hconst
        _ = _ := by
          rw [hji, integral_const_mul, integral_inner hdi, setIntegral_const,
            OAI.Brennan.integral_closedBall_holomorphic hd hr hr₁, real_inner_smul_right,
            real_inner_self_eq_norm_sq, heq, one_pow]
          simp
          ring
    have harea := OAI.Brennan.meromorphic_univalent_area hh hH.1 hdef
      (fun z hz ↦ OAI.Brennan.univalent_deriv_ne_zero
        (Metric.isOpen_ball.sdiff isClosed_singleton) hH hz) hH.2 hr hr₁
    change ∫ z in K, g z ≤ _
    rw [hformula, mul_sub, mul_one, ← volumeReal_closedBall r hr.le]
    exact sub_le_sub_right harea _
  intro z hz
  obtain ⟨r, hzr, hr₁⟩ := exists_between (mem_unitDisk.mp hz)
  have hr : 0 < r := (norm_nonneg z).trans_lt hzr
  have hgcont : ContinuousOn g disk := (hd.continuousOn.sub continuousOn_const).norm.pow 2
  have hgpos : ∀ w, 0 ≤ g w := fun _ ↦ sq_nonneg _
  have hint (R : ℝ) (hR : R < 1) : IntegrableOn g (Metric.closedBall (0 : ℂ) R) :=
    (hgcont.mono (Metric.closedBall_subset_ball hR)).integrableOn_compact
      (isCompact_closedBall 0 R)
  have hzero : (∫ w in Metric.closedBall (0 : ℂ) r, g w) = 0 := by
    apply le_antisymm _ (integral_nonneg hgpos)
    have hlim : Tendsto (fun R : ℝ ↦ R ^ 2 * Real.pi * ((R ^ 2)⁻¹ ^ 2 - 1))
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      have hcont : ContinuousAt (fun R : ℝ ↦ R ^ 2 * Real.pi * ((R ^ 2)⁻¹ ^ 2 - 1)) 1 := by
        exact ((continuousAt_id.pow 2).mul continuousAt_const).mul
          ((((continuousAt_id.pow 2).inv₀ (by norm_num)).pow 2).sub continuousAt_const)
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hr₁)] with R hR₁ hrR
    exact (setIntegral_mono_set (hint R hR₁) (Eventually.of_forall hgpos)
      (Filter.Eventually.of_forall fun _ hw ↦ Metric.closedBall_subset_closedBall hrR.le hw)).trans
      (hbound R (hr.trans hrR) hR₁)
  have hzeroBall : (∫ w in Metric.ball (0 : ℂ) r, g w) = 0 :=
    (setIntegral_congr_set (OAI.Brennan.ball_closedBall_ae_eq r)).trans hzero
  have hb : Metric.ball (0 : ℂ) r ⊆ disk :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_ball hr₁)
  have hintr : IntegrableOn g (Metric.ball (0 : ℂ) r) :=
    (hint r hr₁).mono_set Metric.ball_subset_closedBall
  have hae := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hgpos) hintr).mp hzeroBall
  have hgzero : EqOn g (fun _ ↦ 0) (Metric.ball (0 : ℂ) r) :=
    Measure.eqOn_open_of_ae_eq hae Metric.isOpen_ball (hgcont.mono hb) continuousOn_const
  simpa [g, sub_eq_zero] using hgzero (by simpa [Metric.mem_ball, dist_zero_right] using hzr)

/-- The second Taylor coefficient bound obtained from the odd square-root transform. -/
theorem norm_coeff_two_le {f : ℂ → ℂ} (hf : NormalizedUnivalent f) : ‖coeff f 2‖ ≤ 2 := by
  have h := OAI.Brennan.schlicht_second_deriv_bound hf.schlicht
  norm_num [coeff, iteratedDeriv_succ, norm_mul] at ⊢
  linarith

/-- A lower growth estimate sufficient for the slit-chain approximation. -/
theorem lower_growth {f : ℂ → ℂ} (hf : NormalizedUnivalent f) {z : ℂ}
    (hz : z ∈ unitDisk) : ‖z‖ / 4 ≤ ‖f z‖ :=
  OAI.Brennan.schlicht_lower_growth hf.schlicht hz

/-- The upper half of the growth theorem. -/
theorem upper_growth {f : ℂ → ℂ} (hf : NormalizedUnivalent f) {z : ℂ}
    (hz : z ∈ unitDisk) : ‖f z‖ ≤ ‖z‖ / (1 - ‖z‖) ^ 2 := by
  by_cases hzero : z = 0
  · simp [hzero, hf.map_zero]
  let r : ℝ := ‖z‖
  have hr : 0 < r := norm_pos_iff.mpr hzero
  have hr₁ : r < 1 := mem_unitDisk.mp hz
  let ζ := z / (r : ℂ)
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hζ : ‖ζ‖ = 1 := by
    dsimp only [ζ]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      show ‖z‖ = r from rfl, div_self hr.ne']
  have hrζ : (r : ℂ) * ζ = z := by
    dsimp [ζ]
    field_simp
  have hpath (t : ℝ) (ht : t ∈ Icc 0 r) : (t : ℂ) * ζ ∈ unitDisk := by
    rw [mem_unitDisk, norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact ht.2.trans_lt hr₁
  let D : ℝ → ℂ := fun t ↦ deriv f ((t : ℂ) * ζ) * ζ
  let M : ℝ → ℝ := fun t ↦ (1 + t) / (1 - t) ^ 3
  have hD (t : ℝ) (ht : t ∈ Icc 0 r) :
      HasDerivAt (fun s : ℝ ↦ f ((s : ℂ) * ζ)) (D t) t := by
    have hd := (hf.holomorphic _ (hpath t ht)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (hpath t ht))
    have hin : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * ζ) ζ t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const ζ
    have hout := hd.hasDerivAt.scomp t hin
    change HasDerivAt (fun s : ℝ ↦ f ((s : ℂ) * ζ)) (ζ * deriv f ((t : ℂ) * ζ)) t at hout
    simpa only [D, mul_comm] using hout
  have hDcont : ContinuousOn D (Icc 0 r) := by
    apply ((hf.holomorphic.deriv Metric.isOpen_ball).continuousOn.comp
      (show Continuous (fun t : ℝ ↦ (t : ℂ) * ζ) by fun_prop).continuousOn hpath).mul
    exact continuousOn_const
  have hMcont : ContinuousOn M (Icc 0 r) := by
    apply (continuousOn_const.add continuousOn_id).div
      ((continuousOn_const.sub continuousOn_id).pow 3)
    intro t ht
    apply pow_ne_zero 3
    change 1 - t ≠ 0
    linarith [ht.2]
  have hI : IntervalIntegrable D volume 0 r := hDcont.intervalIntegrable_of_Icc hr.le
  have hIM : IntervalIntegrable M volume 0 r := hMcont.intervalIntegrable_of_Icc hr.le
  have hfint : (∫ t in (0 : ℝ)..r, D t) = f z := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ hD t (by simpa [uIcc_of_le hr.le] using ht)) hI]
    simp [hrζ, hf.map_zero]
  have hMint : (∫ t in (0 : ℝ)..r, M t) = r / (1 - r) ^ 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ ↦ t / (1 - t) ^ 2) ?_ hIM]
    · simp
    intro t ht
    rw [uIcc_of_le hr.le] at ht
    have ht₁ : 1 - t ≠ 0 := by linarith [ht.2]
    let v : ℝ := (1 * (1 - t) ^ 2 - t * (2 * (1 - t) ^ (2 - 1 : ℕ) * (0 - 1))) /
      ((1 - t) ^ 2) ^ 2
    have htD : HasDerivAt (fun s : ℝ ↦ s / (1 - s) ^ 2) v t := (hasDerivAt_id t).div
      (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).pow 2) (pow_ne_zero 2 ht₁)
    have heq : v = M t := by
      dsimp [v, M]
      field_simp [ht₁]
      ring
    exact heq ▸ htD
  rw [← hfint, ← hMint]
  apply (intervalIntegral.norm_integral_le_integral_norm hr.le).trans
  apply intervalIntegral.integral_mono_on hr.le hI.norm hIM
  intro t ht
  have h := (hf.distortion_bounds (hpath t ht)).2
  simpa [D, M, norm_mul, hζ, Real.norm_eq_abs, abs_of_nonneg ht.1] using h

private lemma coeff_dslope {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisk) (n : ℕ) :
    coeff f (n + 1) = coeff (dslope f 0) n := by
  let F := dslope f 0
  let K : ℂ → ℂ := fun z ↦ z * F z
  have hF : DifferentiableOn ℂ F unitDisk :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds zero_mem_unitDisk)).mpr hf
  have hF0 : AnalyticAt ℂ F 0 := hF.analyticOnNhd Metric.isOpen_ball _ zero_mem_unitDisk
  have hfK : f = fun z ↦ f 0 + K z := by
    funext z
    dsimp [K, F]
    rw [OAI.Brennan.dslope_factor]; ring
  have hD₀ : iteratedDeriv (n + 1) f 0 = iteratedDeriv (n + 1) K 0 := by
    simp only [iteratedDeriv_succ']
    have hd : deriv f = deriv K := calc
      _ = deriv (fun z ↦ f 0 + K z) := congrArg deriv hfK
      _ = _ := deriv_const_add' (f 0)
    rw [hd]
  have hD : iteratedDeriv (n + 1) f 0 = (↑(n + 1) : ℂ) * iteratedDeriv n F 0 := by
    rw [hD₀]
    change iteratedDeriv (n + 1) (fun z ↦ id z * F z) 0 = _
    rw [iteratedDeriv_fun_mul (contDiffAt_id (𝕜 := ℂ)) hF0.contDiffAt,
      Finset.sum_eq_single 1]
    · simp
    · intro i _ hi
      have hz : iteratedDeriv i id (0 : ℂ) = 0 := by
        simp [iteratedDeriv_id, hi]
      simp [hz]
    · intro h
      exfalso
      exact h (Finset.mem_range.mpr (by omega))
  rw [coeff, coeff, hD, Nat.factorial_succ, Nat.cast_mul]
  field_simp
  rfl

/-- The `n = 2` Zalcman inequality, from the first exterior Laurent coefficient. -/
theorem norm_coeff_two_sq_sub_coeff_three_le {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    ‖coeff f 2 ^ 2 - coeff f 3‖ ≤ 1 := by
  let F := dslope f 0
  let Q := dslope F 0
  let h : ℂ → ℂ := fun z ↦ -Q z / F z
  let H : ℂ → ℂ := fun z ↦ (f z)⁻¹
  have hF0 : F 0 = 1 := by simp [F, hf.deriv_zero]
  have hn := Metric.isOpen_ball.mem_nhds zero_mem_unitDisk
  have hF : DifferentiableOn ℂ F unitDisk := (Complex.differentiableOn_dslope hn).mpr hf.holomorphic
  have hQ : DifferentiableOn ℂ Q unitDisk := (Complex.differentiableOn_dslope hn).mpr hF
  have hfn (z : ℂ) (hz : z ∈ unitDisk) (hzero : z ≠ 0) : f z ≠ 0 := by
    intro hz0
    exact hzero (hf.injective hz zero_mem_unitDisk (hz0.trans hf.map_zero.symm))
  have hfact (z : ℂ) : z * F z = f z := by
    simpa [F, hf.map_zero] using OAI.Brennan.dslope_factor f z
  have hFn (z : ℂ) (hz : z ∈ unitDisk) : F z ≠ 0 := by
    intro hFz
    by_cases hzero : z = 0
    · simp [hzero, hF0] at hFz
    · exact hfn z hz hzero (by simpa [hFz] using (hfact z).symm)
  have hd : DifferentiableOn ℂ h unitDisk := hQ.neg.div hF hFn
  have hHu : OAI.Brennan.UnivalentOn H (unitDisk \ {0}) := by
    refine ⟨(hf.holomorphic.mono sdiff_subset).inv (fun z hz ↦ hfn z hz.1 hz.2), ?_⟩
    intro z hz w hw heq
    exact hf.injective hz.1 hw.1 (inv_inj.mp heq)
  have hdef (z : ℂ) (hz : z ∈ unitDisk) (hzero : z ≠ 0) : H z = z⁻¹ + h z := by
    have hQfact : z * Q z = F z - 1 := by
      simpa [Q, hF0] using OAI.Brennan.dslope_factor F z
    dsimp only [H, h]
    rw [← hfact z]
    field_simp [hzero, hFn z hz]
    linear_combination hQfact
  have he := OAI.Brennan.meromorphic_univalent_coefficient hd hHu.1 hdef
    (fun _ hz ↦ OAI.Brennan.univalent_deriv_ne_zero (Metric.isOpen_ball.sdiff isClosed_singleton)
      hHu hz) hHu.2
  have h₂ : coeff f 2 = deriv F 0 := by
    simpa [F] using coeff_dslope hf.holomorphic 1
  have h₃ : coeff f 3 = deriv Q 0 := by
    calc
      coeff f 3 = coeff F 2 := coeff_dslope hf.holomorphic 2
      _ = deriv Q 0 := by simpa [Q] using coeff_dslope hF 1
  have hder := (((hQ.differentiableAt hn).hasDerivAt).neg.div
    (hF.differentiableAt hn).hasDerivAt (hFn _ zero_mem_unitDisk)).deriv
  change deriv h 0 = _ at hder
  rw [hder] at he
  have hQ0 : Q 0 = deriv F 0 := dslope_same F 0
  rw [h₂, h₃]
  convert he using 2
  simp [hF0, hQ0]
  ring

/-- Equality in the second coefficient bound forces a rotation of the Koebe function. -/
theorem isKoebeRotation_of_norm_coeff_two_eq {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    (heq : ‖coeff f 2‖ = 2) : IsKoebeRotation f := by
  obtain ⟨q, g, h, H, _hqd, _hq₀, hqn, hqs, hg, _hgu, _hg₀, hh, hder, hdef, hHu, hff, hHg⟩ :=
    OAI.Brennan.exists_odd_transform hf.schlicht
  let lam : ℂ := deriv q 0
  have hlam : ‖lam‖ = 1 := by
    norm_num [coeff, iteratedDeriv_succ, hff, norm_mul, lam] at heq ⊢
    linarith
  have hnorm : ‖deriv h 0‖ = 1 := by simpa [hder, lam] using hlam
  have hderEq := area_eq_const_deriv hh hHu hdef hnorm
  have hlin : EqOn h (fun z ↦ h 0 - lam * z) unitDisk := by
    apply Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball (0 : ℂ) 1).isPreconnected hh
      (by fun_prop) _ zero_mem_unitDisk (by simp)
    intro z hz
    rw [hderEq hz, hder]
    simp [lam]
  have HH (z : ℂ) : H z = (z * q (z ^ 2))⁻¹ := by
    rw [hHg, hg]
  have h₀ : h 0 = 0 := by
    let a : ℂ := 1 / 2
    have ha : a ∈ unitDisk := by norm_num [a, mem_unitDisk, norm_div]
    have ha₀ : a ≠ 0 := by norm_num [a]
    have hneg : -a ∈ unitDisk := by simpa [mem_unitDisk] using ha
    have hop : H (-a) = -H a := by
      rw [HH (-a), HH a]
      simp
    have hplus := hdef a ha ha₀
    have hminus := hdef (-a) hneg (neg_ne_zero.mpr ha₀)
    rw [hlin ha] at hplus
    rw [hlin hneg, hop, inv_neg] at hminus
    linear_combination -(hplus + hminus) / 2
  refine ⟨lam, hlam, ?_⟩
  intro w hw
  have hconj : conj lam * lam = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hlam]
    norm_num
  have hrot : rotate lam koebe w = w / (1 - lam * w) ^ 2 := by
    rw [rotate, koebe, ← mul_div_assoc, ← mul_assoc, hconj, one_mul]
  rw [hrot]
  by_cases hw₀ : w = 0
  · simp [hw₀, hf.map_zero]
  let z := w ^ ((2 : ℂ)⁻¹)
  have hzsq : z ^ 2 = w := Complex.cpow_nat_inv_pow w (n := 2) (by decide)
  have hz₀ : z ≠ 0 := by
    intro he
    exact hw₀ (by simpa [he] using hzsq.symm)
  have hz : z ∈ unitDisk := by
    rw [mem_unitDisk]
    have hn := mem_unitDisk.mp hw
    rw [← hzsq, norm_pow] at hn
    nlinarith [norm_nonneg z]
  have e := hdef z hz hz₀
  rw [HH z, hlin hz, h₀, hzsq] at e
  simp only [zero_sub] at e
  have hq : (q w)⁻¹ = 1 - lam * w := by
    have hmul := congrArg (z * ·) e
    have hinv : (z * q w)⁻¹ = z⁻¹ * (q w)⁻¹ := by field_simp [hz₀, hqn w hw]
    rw [hinv, ← mul_assoc, mul_inv_cancel₀ hz₀, one_mul,
      mul_add, mul_inv_cancel₀ hz₀] at hmul
    rw [hmul, ← hzsq]
    ring
  have hfq := OAI.Brennan.dslope_factor f w
  rw [hf.map_zero, sub_zero, ← hqs w hw] at hfq
  have hq' : q w = (1 - lam * w)⁻¹ := by rw [← hq, inv_inv]
  rw [← hfq, hq', inv_pow, div_eq_mul_inv]

end Zalcman
