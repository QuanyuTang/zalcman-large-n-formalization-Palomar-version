/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.AmbientPerturbation
public import Zalcman.Upstream.Brennan.Distortion
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Ambient extension of an analytic disk embedding

Dilations connect the embedding to the identity through holomorphic charts.
Compactness makes a cutoff deformation small uniformly along this path.
A finite composition of the resulting plane homeomorphisms gives the extension.
-/

@[expose] public section

namespace Zalcman

open Set Filter
open scoped Topology NNReal

private theorem exists_uniform_ambient_step {F : ℝ → ℂ → ℂ} {R r : ℝ}
    (hr : 1 < r) (hR : r < R)
    (hF : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (F s) (Metric.ball 0 R))
    (hi : ∀ s ∈ Icc (0 : ℝ) 1, InjOn (F s) (Metric.ball 0 R))
    (hn : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ Metric.ball (0 : ℂ) R, deriv (F s) z ≠ 0)
    (hv : ContinuousOn (fun q : ℝ × ℂ ↦ F q.1 q.2) (Icc 0 1 ×ˢ Metric.closedBall 0 r))
    (hD : ContinuousOn (fun q : ℝ × ℂ ↦ deriv (F q.1) q.2)
      (Icc 0 1 ×ˢ Metric.closedBall 0 r)) :
    ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist t s < δ →
      ∃ e : ℂ ≃ₜ ℂ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, e (F s z) = F t z := by
  let I := Icc (0 : ℝ) 1
  let K := Metric.closedBall (0 : ℂ) r
  let U := Metric.ball (0 : ℂ) R
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKU : K ⊆ U := Metric.closedBall_subset_ball hR
  have h0I : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
  have h0K : (0 : ℂ) ∈ K := Metric.mem_closedBall_self (zero_le_one.trans hr.le)
  have hIK : IsCompact (I ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨p, hp, hpMin⟩ := hIK.exists_isMinOn ⟨(0, 0), h0I, h0K⟩ hD.norm
  let m := ‖deriv (F p.1) p.2‖
  have hm : 0 < m := norm_pos_iff.mpr (hn p.1 hp.1 p.2 (hKU hp.2))
  let χ : ContDiffBump (0 : ℂ) := ⟨1, r, zero_lt_one, hr⟩
  have hχ : ContDiff ℝ 1 (χ : ℂ → ℝ) := χ.contDiff
  have hcχ : Continuous (fun z ↦ ‖fderiv ℝ (χ : ℂ → ℝ) z‖) :=
    (hχ.continuous_fderiv (by norm_num)).norm
  obtain ⟨z₀, _, hzmax⟩ := hK.exists_isMaxOn ⟨0, h0K⟩ hcχ.continuousOn
  let M := ‖fderiv ℝ (χ : ℂ → ℝ) z₀‖
  have hM : 0 ≤ M := norm_nonneg _
  let ε := m / (4 * (M + 1))
  have hε : 0 < ε := div_pos hm (by positivity)
  obtain ⟨δv, hδv, hvB⟩ := (Metric.uniformContinuousOn_iff.mp
    (hIK.uniformContinuousOn_of_continuous hv)) ε hε
  obtain ⟨δd, hδd, hdB⟩ := (Metric.uniformContinuousOn_iff.mp
    (hIK.uniformContinuousOn_of_continuous hD)) ε hε
  refine ⟨min δv δd, lt_min hδv hδd, fun s hs t ht hst ↦ ?_⟩
  let D := fun z ↦ F t z - F s z
  let d := fun z ↦ χ z • D z
  have hχd : Differentiable ℝ (χ : ℂ → ℝ) := hχ.differentiable (by norm_num)
  have hD' {z : ℂ} (hz : z ∈ U) : HasDerivAt D (deriv (F t) z - deriv (F s) z) z :=
    (((hF t ht).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt).fun_sub
      ((hF s hs).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt
  have hd (z : ℂ) (hz : z ∈ U) : HasFDerivAt d
      (χ z • (ContinuousLinearMap.toSpanSingleton ℂ
          (deriv (F t) z - deriv (F s) z)).restrictScalars ℝ +
        (fderiv ℝ (χ : ℂ → ℝ) z).smulRight (D z)) z :=
    (hχd z).hasFDerivAt.smul ((hD' hz).hasFDerivAt.restrictScalars ℝ)
  have hdiff : DifferentiableOn ℝ d U := fun z hz ↦ (hd z hz).differentiableAt.differentiableWithinAt
  have hzero {z : ℂ} (hz : z ∉ K) : d z = 0 := by
    have hz' : r ≤ dist z (0 : ℂ) := le_of_lt (lt_of_not_ge fun he ↦ hz (Metric.mem_closedBall.mpr he))
    have hχz : χ z = 0 := χ.zero_of_le_dist hz'
    simp [d, hχz]
  let c : ℝ≥0 := 1 / 2
  have hc : c < 1 := by norm_num [c]
  have hsmall (z : ℂ) (hz : z ∈ U) : ‖fderiv ℝ d z‖ ≤ (c : ℝ) * ‖deriv (F s) z‖ := by
    by_cases hzK : z ∈ K
    · have hbV : ‖D z‖ < ε := by
        simpa only [D, dist_eq_norm] using
          hvB (t, z) ⟨ht, hzK⟩ (s, z) ⟨hs, hzK⟩
            (by rw [dist_prod_same_right]; exact hst.trans_le (min_le_left _ _))
      have hbD : ‖deriv (F t) z - deriv (F s) z‖ < ε := by
        simpa only [dist_eq_norm] using
          hdB (t, z) ⟨ht, hzK⟩ (s, z) ⟨hs, hzK⟩
            (by rw [dist_prod_same_right]; exact hst.trans_le (min_le_right _ _))
      have hbχ : ‖fderiv ℝ (χ : ℂ → ℝ) z‖ ≤ M := hzmax hzK
      have hbχv : ‖χ z‖ ≤ 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg χ.nonneg] using χ.le_one (x := z)
      have hbMin : m ≤ ‖deriv (F s) z‖ := hpMin (show (s, z) ∈ I ×ˢ K from ⟨hs, hzK⟩)
      have hεM : (M + 1) * ε = m / 4 := by
        dsimp only [ε]
        field_simp [show M + 1 ≠ 0 by positivity] <;> ring
      rw [(hd z hz).fderiv]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply,
        ContinuousLinearMap.norm_restrictScalars, ContinuousLinearMap.norm_toSpanSingleton]
      have h1 := mul_le_mul hbχv hbD.le (norm_nonneg _) zero_le_one
      have h2 := mul_le_mul hbχ hbV.le (norm_nonneg _) hM
      rw [show (c : ℝ) = 1 / 2 by norm_num [c]]
      nlinarith only [h1, h2, hεM, hm, hbMin]
    · have hzloc : d =ᶠ[𝓝 z] (0 : ℂ → ℂ) := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with w hw
        exact hzero hw
      rw [hzloc.fderiv_eq, fderiv_zero, Pi.zero_apply, norm_zero]
      positivity
  obtain ⟨e, he, _⟩ := exists_homeomorph_of_holomorphic_displacement Metric.isOpen_ball
    hK hKU hc (hF s hs) (hi s hs) (hn s hs) hdiff (fun _ hz ↦ hzero hz.2) hsmall
  refine ⟨e, fun z hz ↦ ?_⟩
  have hzU : z ∈ U := hKU (Metric.closedBall_subset_closedBall hr.le hz)
  have hχz : χ z = 1 := χ.one_of_mem_closedBall hz
  rw [he z hzU]
  simp only [d, D, hχz, one_smul]
  abel

/-- A normalized holomorphic embedding of a neighborhood of the closed unit disk
extends on that closed disk to a homeomorphism of the plane. -/
theorem exists_plane_homeomorph_extends_analytic_disk {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) (hi : InjOn f (Metric.ball 0 R))
    (h₀ : f 0 = 0) (h₁ : deriv f 0 = 1) :
    ∃ e : ℂ ≃ₜ ℂ, EqOn e f (Metric.closedBall 0 1) := by
  let r := (1 + R) / 2
  have hr : 1 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  let U := Metric.ball (0 : ℂ) R
  let F := fun (s : ℝ) (z : ℂ) ↦ z * dslope f 0 ((s : ℂ) * z)
  have hds : DifferentiableOn ℂ (dslope f 0) U :=
    (Complex.differentiableOn_dslope (Metric.ball_mem_nhds 0 (zero_lt_one.trans hR))).mpr hf
  have hscale {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ U) : (s : ℂ) * z ∈ U := by
    have hzn : ‖z‖ < R := by simpa [U, Metric.mem_ball, dist_zero_right] using hz
    change (s : ℂ) * z ∈ Metric.ball 0 R
    rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_of_nonneg hs.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hs.2).trans_lt hzn
  have hF (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : DifferentiableOn ℂ (F s) U :=
    differentiableOn_id.mul (hds.comp (by fun_prop) (fun _ hz ↦ hscale hs hz))
  have heq (s : ℝ) (hs : s ≠ 0) : F s = fun z ↦ ((s : ℂ)⁻¹) * f ((s : ℂ) * z) := by
    funext z
    have hd := sub_smul_dslope f (0 : ℂ) ((s : ℂ) * z)
    rw [sub_zero, smul_eq_mul, h₀, sub_zero] at hd
    change z * dslope f 0 ((s : ℂ) * z) = _
    rw [← hd, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hs), one_mul]
  have hF₀ : F 0 = id := by funext z; simp [F, dslope_same, h₁]
  have hF₁ : F 1 = f := by simpa using heq 1 one_ne_zero
  have hFi (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : InjOn (F s) U := by
    by_cases hs₀ : s = 0
    · rw [hs₀, hF₀]
      exact fun _ _ _ _ hh ↦ hh
    · intro z hz w hw hzw
      rw [heq s hs₀] at hzw
      have hsn := Complex.ofReal_ne_zero.mpr hs₀
      exact mul_left_cancel₀ hsn (hi (hscale hs hz) (hscale hs hw)
        (mul_left_cancel₀ (inv_ne_zero hsn) hzw))
  have hDer (s : ℝ) (z : ℂ) : deriv (F s) z = deriv f ((s : ℂ) * z) := by
    by_cases hs : s = 0
    · simp [hs, hF₀, h₁]
    · rw [heq s hs, deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hs), one_mul]
  have hFn (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (z : ℂ) (hz : z ∈ U) : deriv (F s) z ≠ 0 := by
    rw [hDer]
    exact OAI.Brennan.univalent_deriv_ne_zero Metric.isOpen_ball ⟨hf, hi⟩ (hscale hs hz)
  let K := Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ℂ) r
  have hsc : Continuous (fun q : ℝ × ℂ ↦ (q.1 : ℂ) * q.2) := by fun_prop
  have hscmap : MapsTo (fun q : ℝ × ℂ ↦ (q.1 : ℂ) * q.2) K U :=
    fun _ hq ↦ hscale hq.1 (Metric.closedBall_subset_ball hrR hq.2)
  have hVal : ContinuousOn (fun q : ℝ × ℂ ↦ F q.1 q.2) K :=
    continuous_snd.continuousOn.mul (hds.continuousOn.comp hsc.continuousOn hscmap)
  have hDerCont : ContinuousOn (fun q : ℝ × ℂ ↦ deriv (F q.1) q.2) K := by
    simp only [hDer]
    exact ((hf.deriv Metric.isOpen_ball).continuousOn.comp hsc.continuousOn hscmap)
  obtain ⟨δ, hδ, hstep⟩ := exists_uniform_ambient_step hr hrR hF hFi hFn hVal hDerCont
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hN₀ : 0 < (N : ℝ) := (div_pos zero_lt_one hδ).trans hN
  have hNδ : 1 / (N : ℝ) < δ := (div_lt_iff₀ hN₀).mpr
    (by simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hN)
  let p := fun n : ℕ ↦ (n : ℝ) / (N : ℝ)
  have hp {n : ℕ} (hn : n ≤ N) : p n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (Nat.cast_nonneg n) hN₀.le, (div_le_one hN₀).mpr (Nat.cast_le.mpr hn)⟩
  have hseq (n : ℕ) (hn : n ≤ N) : ∃ e : ℂ ≃ₜ ℂ, EqOn e (F (p n)) (Metric.closedBall 0 1) := by
    induction n with
    | zero =>
      refine ⟨Homeomorph.refl ℂ, fun z _ ↦ ?_⟩
      simp [p, hF₀]
    | succ n ih =>
      have hn' : n ≤ N := (Nat.le_succ n).trans hn
      obtain ⟨e, he⟩ := ih hn'
      have hdiff : p (n + 1) - p n = 1 / (N : ℝ) := by simp only [p, Nat.cast_add, Nat.cast_one]; ring
      have hdist : dist (p (n + 1)) (p n) < δ := by
        rw [Real.dist_eq, hdiff, abs_of_nonneg (div_nonneg zero_le_one hN₀.le)]
        exact hNδ
      obtain ⟨e', he'⟩ := hstep (p n) (hp hn') (p (n + 1)) (hp hn) hdist
      refine ⟨e.trans e', fun z hz ↦ ?_⟩
      change e' (e z) = F (p (n + 1)) z
      rw [he hz, he' z hz]
  obtain ⟨e, he⟩ := hseq N le_rfl
  exact ⟨e, by simpa only [p, div_self hN₀.ne', hF₁] using he⟩

end Zalcman
