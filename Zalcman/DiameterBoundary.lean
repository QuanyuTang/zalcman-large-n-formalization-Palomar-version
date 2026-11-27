/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.AmplitudeIntegral
public import Zalcman.RadialComparison
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Diameter boundary estimates

Each half of the symmetric diameter integral is estimated on its own. The
interior kernel ratio controls its interior contribution. A fixed preceding
half-unit interval controls both amplitude and phase at its moving endpoint.
-/

@[expose] public section

noncomputable section

namespace Zalcman

open MeasureTheory Set
open scoped ComplexConjugate

/-- The sum of amplitude and phase energy on one half of a diameter. -/
def diameterHalfEnergy (Q V : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..x, amplitudeKernel (x - u) * Q u) + ∫ u in (0 : ℝ)..x, V u

/-- The derivative of the half-diameter energy. -/
def diameterHalfRate (Q V : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..x, amplitudeKernelDeriv (x - u) * Q u) + V x

private lemma hasDerivAt_primitive_of_continuous {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    HasDerivAt (fun t ↦ ∫ u in (0 : ℝ)..t, g u) (g x) x :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

private lemma amplitudeKernel_continuous : Continuous amplitudeKernel := by
  unfold amplitudeKernel
  exact ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).sub continuous_const).div_const _

private lemma amplitudeKernelDeriv_continuous : Continuous amplitudeKernelDeriv := by
  unfold amplitudeKernelDeriv
  exact (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).div_const _

/-- The amplitude kernel vanishes at its moving boundary, so differentiation
retains only the differentiated kernel inside the integral. -/
theorem hasDerivAt_amplitudeKernel_convolution {Q : ℝ → ℝ} (hQ : Continuous Q) (x : ℝ) :
    HasDerivAt (fun t ↦ ∫ u in (0 : ℝ)..t, amplitudeKernel (t - u) * Q u)
      (∫ u in (0 : ℝ)..x, amplitudeKernelDeriv (x - u) * Q u) x := by
  let E (t : ℝ) := Real.exp (4 * t)
  let F (t : ℝ) := Real.exp (-4 * t)
  let A (t : ℝ) := ∫ u in (0 : ℝ)..t, F u * Q u
  let B (t : ℝ) := ∫ u in (0 : ℝ)..t, E u * Q u
  let D (t : ℝ) := ∫ u in (0 : ℝ)..t, Q u
  have hEc : Continuous E := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hFc : Continuous F := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hE : HasDerivAt E (4 * E x) x := by
    simpa [E, mul_comm, id] using ((hasDerivAt_id x).const_mul (4 : ℝ)).exp
  have hF : HasDerivAt F (-4 * F x) x := by
    simpa [F, mul_comm, id] using ((hasDerivAt_id x).const_mul (-4 : ℝ)).exp
  have hA : HasDerivAt A (F x * Q x) x := hasDerivAt_primitive_of_continuous (hFc.mul hQ) x
  have hB : HasDerivAt B (E x * Q x) x := hasDerivAt_primitive_of_continuous (hEc.mul hQ) x
  have hD : HasDerivAt D (Q x) x := hasDerivAt_primitive_of_continuous hQ x
  have hprod : E x * F x = 1 := by
    dsimp [E, F]
    rw [← Real.exp_add, show 4 * x + -4 * x = 0 by ring, Real.exp_zero]
  have hK (t u : ℝ) : amplitudeKernel (t - u) * Q u =
      (E t * (F u * Q u) + F t * (E u * Q u) - 2 * Q u) / 32 := by
    rw [amplitudeKernel, Real.cosh_eq, show 4 * (t - u) = 4 * t + -4 * u by ring,
      show -(4 * t + -4 * u) = -4 * t + 4 * u by ring, Real.exp_add, Real.exp_add]
    dsimp only [E, F]
    ring
  have hK' (u : ℝ) : amplitudeKernelDeriv (x - u) * Q u =
      (E x * (F u * Q u) - F x * (E u * Q u)) / 8 := by
    rw [amplitudeKernelDeriv, Real.sinh_eq, show 4 * (x - u) = 4 * x + -4 * u by ring,
      show -(4 * x + -4 * u) = -4 * x + 4 * u by ring, Real.exp_add, Real.exp_add]
    dsimp only [E, F]
    ring
  have hInt (t : ℝ) : (∫ u in (0 : ℝ)..t, amplitudeKernel (t - u) * Q u) =
      (E t * A t + F t * B t - 2 * D t) / 32 := by
    simp_rw [hK]
    have ha : IntervalIntegrable (fun u ↦ E t * (F u * Q u)) volume 0 t :=
      ((hFc.mul hQ).intervalIntegrable (μ := volume) 0 t).const_mul (E t)
    have hb : IntervalIntegrable (fun u ↦ F t * (E u * Q u)) volume 0 t :=
      ((hEc.mul hQ).intervalIntegrable (μ := volume) 0 t).const_mul (F t)
    have hc := (hQ.intervalIntegrable (μ := volume) 0 t).const_mul 2
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (ha.add hb) hc,
      intervalIntegral.integral_add ha hb]
    simp only [intervalIntegral.integral_const_mul, A, B, D]
  have hInt' : (∫ u in (0 : ℝ)..x, amplitudeKernelDeriv (x - u) * Q u) =
      (E x * A x - F x * B x) / 8 := by
    simp_rw [hK']
    have ha : IntervalIntegrable (fun u ↦ E x * (F u * Q u)) volume 0 x :=
      ((hFc.mul hQ).intervalIntegrable (μ := volume) 0 x).const_mul (E x)
    have hb : IntervalIntegrable (fun u ↦ F x * (E u * Q u)) volume 0 x :=
      ((hEc.mul hQ).intervalIntegrable (μ := volume) 0 x).const_mul (F x)
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub ha hb]
    simp only [intervalIntegral.integral_const_mul, A, B]
  rw [show (fun t ↦ ∫ u in (0 : ℝ)..t, amplitudeKernel (t - u) * Q u) =
    (fun t ↦ (E t * A t + F t * B t - 2 * D t) / 32) from funext hInt, hInt']
  have h := (((hE.fun_mul hA).fun_add (hF.fun_mul hB)).fun_sub (hD.const_mul 2)).div_const 32
  have heq : ((4 * E x * A x + E x * (F x * Q x)) +
      (-4 * F x * B x + F x * (E x * Q x)) - 2 * Q x) / 32 =
        (E x * A x - F x * B x) / 8 := by
    calc
      _ = (4 * E x * A x - 4 * F x * B x + 2 * (E x * F x) * Q x - 2 * Q x) / 32 := by ring
      _ = _ := by rw [hprod]; ring
  rw [← heq]
  exact h

theorem hasDerivAt_diameterHalfEnergy {Q V : ℝ → ℝ}
    (hQ : Continuous Q) (hV : Continuous V) (x : ℝ) :
    HasDerivAt (diameterHalfEnergy Q V) (diameterHalfRate Q V x) x :=
  (hasDerivAt_amplitudeKernel_convolution hQ x).fun_add (hasDerivAt_primitive_of_continuous hV x)

private lemma amplitudeKernel_half_pos : 0 < amplitudeKernel (1 / 2) := by
  unfold amplitudeKernel
  exact div_pos (sub_pos.mpr (Real.one_lt_cosh.mpr (by norm_num))) (by norm_num)

private lemma amplitudeKernel_half_le {v : ℝ} (hv : 1 / 2 ≤ v) :
    amplitudeKernel (1 / 2) ≤ amplitudeKernel v := by
  unfold amplitudeKernel
  apply div_le_div_of_nonneg_right _ (by norm_num)
  suffices Real.cosh (4 * (1 / 2)) ≤ Real.cosh (4 * v) by linarith only [this]
  rw [Real.cosh_le_cosh]
  rw [abs_of_nonneg (by norm_num), abs_of_nonneg (by linarith only [hv])]
  linarith only [hv]

private lemma amplitudeKernelDeriv_half_nonneg : 0 ≤ amplitudeKernelDeriv (1 / 2) :=
  div_nonneg (Real.sinh_nonneg_iff.mpr (by norm_num)) (by norm_num)

private lemma amplitudeKernelDeriv_le_half {v : ℝ} (hv : v ≤ 1 / 2) :
    amplitudeKernelDeriv v ≤ amplitudeKernelDeriv (1 / 2) := by
  unfold amplitudeKernelDeriv
  exact div_le_div_of_nonneg_right (Real.sinh_le_sinh.mpr (by linarith only [hv])) (by norm_num)

/-- A phase curve with speed controlled by the square root of a locally
comparable deficit has a squared endpoint variation controlled by that deficit. -/
theorem phase_endpoint_sq_le {P P' : ℝ → ℂ} {d : ℝ → ℝ} {A x u : ℝ}
    (hP : ∀ t, HasDerivAt P (P' t) t) (hd : ∀ t, 0 ≤ d t) (hA : 0 ≤ A)
    (hspeed : ∀ t, ‖P' t‖ ≤ 2 * Real.sqrt (d t))
    (hlocal : ∀ t ∈ Icc (x - 1) x, d t ≤ A * d x)
    (hu : u ∈ Icc (x - 1) x) : ‖P x - P u‖ ^ 2 ≤ 4 * A * d x := by
  let M := 2 * Real.sqrt (A * d x)
  have hM₀ : 0 ≤ M := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hdiff : ‖P x - P u‖ ≤ M * (x - u) := by
    apply norm_image_sub_le_of_norm_deriv_le_segment' (a := u) (b := x)
      (fun t _ ↦ (hP t).hasDerivWithinAt)
    · intro t ht
      apply (hspeed t).trans
      exact mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hlocal t ⟨hu.1.trans ht.1, ht.2.le⟩)) (by norm_num)
    · exact right_mem_Icc.mpr hu.2
  have hdiff' : ‖P x - P u‖ ≤ M := by
    apply hdiff.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (show x - u ≤ 1 by linarith only [hu.1]) hM₀
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hdiff' 2
  dsimp only [M] at hsq
  rwa [mul_pow, Real.sq_sqrt (mul_nonneg hA (hd x)), show (2 : ℝ) ^ 2 = 4 by norm_num,
    ← mul_assoc] at hsq

/-- The squared phase distance at the endpoint is controlled by its value
one unit earlier and the local squared variation. -/
theorem phase_deficit_endpoint_le {P : ℝ → ℂ} {γ : ℂ} {d L x u : ℝ}
    (hvar : ‖P x - P u‖ ^ 2 ≤ L * d) :
    ‖P x - γ‖ ^ 2 / 2 ≤ 2 * (‖P u - γ‖ ^ 2 / 2) + L * d := by
  have htriangle : ‖P x - γ‖ ≤ ‖P x - P u‖ + ‖P u - γ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  nlinarith only [hsq, hvar, sq_nonneg (‖P x - P u‖ - ‖P u - γ‖)]

set_option maxHeartbeats 1500000 in
/-- The derivative of each nonnegative half-diameter energy is bounded by a
constant depending only on the local comparison constants of the amplitude and phase. -/
theorem exists_diameterHalfRate_le (A B L : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d W U p : ℝ → ℝ}, Continuous W → Continuous U → Continuous p →
      (∀ t, 0 ≤ d t) → (∀ t, 0 ≤ U t) → (∀ t, 0 ≤ p t) →
      (∀ t, 2 * d t ≤ W t ∧ W t ≤ 6 * d t) →
      (∀ x u, |u - x| ≤ 1 → d u ≤ A * d x) →
      (∀ x u, |u - x| ≤ 1 → U u ≤ B * U x) →
      (∀ x u, u ∈ Icc (x - 1) x → p x ≤ 2 * p u + L * d x) →
      ∀ x ≥ 2,
        diameterHalfRate (fun t ↦ W t * U t) (fun t ↦ U t * p t) x ≤
          C * diameterHalfEnergy (fun t ↦ W t * U t) (fun t ↦ U t * p t) x := by
  let c := 4 * ((Real.exp 2 + 1) / (Real.exp 2 - 1))
  let k := amplitudeKernel (1 / 2)
  let b₁ := 3 * amplitudeKernelDeriv (1 / 2) * A * B
  let b₂ := A * B / k
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  have hk : 0 < k := amplitudeKernel_half_pos
  have hc : 0 ≤ c := by
    have hexp : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
    exact mul_nonneg (by norm_num) (div_nonneg (by positivity) (sub_nonneg.mpr hexp.le))
  have hb₁ : 0 ≤ b₁ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) amplitudeKernelDeriv_half_nonneg) hA₀) hB₀
  have hb₂ : 0 ≤ b₂ := div_nonneg (mul_nonneg hA₀ hB₀) hk.le
  let C := c + (b₁ + L) * b₂ + 4 * B
  have hC : 0 < C := add_pos_of_nonneg_of_pos
    (add_nonneg hc (mul_nonneg (add_nonneg hb₁ hL) hb₂))
    (mul_pos (by norm_num) (zero_lt_one.trans_le hB))
  refine ⟨C, hC, ?_⟩
  intro d W U p hWc hUc hpc hd hU hp hW hdloc hUloc hploc x hx
  let a := x - 1
  let b := x - 1 / 2
  let D := d x * U x
  let Q (u : ℝ) := W u * U u
  let V (u : ℝ) := U u * p u
  let F (u : ℝ) := amplitudeKernel (x - u) * Q u
  let F' (u : ℝ) := amplitudeKernelDeriv (x - u) * Q u
  let I := ∫ u in (0 : ℝ)..x, F u
  let P := ∫ u in (0 : ℝ)..x, V u
  have ha : 0 ≤ a := by dsimp only [a]; linarith only [hx]
  have hab : a ≤ b := by dsimp only [a, b]; linarith
  have hbx : b ≤ x := by dsimp only [b]; linarith
  have hb : 0 ≤ b := ha.trans hab
  have hx₀ : 0 ≤ x := hb.trans hbx
  have hD₀ : 0 ≤ D := mul_nonneg (hd x) (hU x)
  have hQ₀ (u : ℝ) : 0 ≤ Q u :=
    mul_nonneg ((mul_nonneg (by norm_num) (hd u)).trans (hW u).1) (hU u)
  have hV₀ (u : ℝ) : 0 ≤ V u := mul_nonneg (hU u) (hp u)
  have hF₀ (u : ℝ) : 0 ≤ F u := mul_nonneg (amplitudeKernel_nonneg _) (hQ₀ u)
  have hFc : Continuous F := (amplitudeKernel_continuous.comp
    (continuous_const.sub continuous_id)).mul (hWc.mul hUc)
  have hF'c : Continuous F' := (amplitudeKernelDeriv_continuous.comp
    (continuous_const.sub continuous_id)).mul (hWc.mul hUc)
  have hVc : Continuous V := hUc.mul hpc
  have hI₀ : 0 ≤ I := intervalIntegral.integral_nonneg_of_forall hx₀ hF₀
  have hP₀ : 0 ≤ P := intervalIntegral.integral_nonneg_of_forall hx₀ hV₀
  have hablen : b - a = 1 / 2 := by dsimp only [a, b]; ring
  have hbxlen : x - b = 1 / 2 := by dsimp only [b]; ring
  have hdist (u : ℝ) (hu : u ∈ Icc a x) : |u - x| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hu.2)]
    have hu' : x - 1 ≤ u := hu.1
    linarith only [hu']
  have hQlower (u : ℝ) (hu : u ∈ Icc a x) : 2 * D ≤ (A * B) * Q u := by
    have hdist' : |x - u| ≤ 1 := by simpa only [abs_sub_comm] using hdist u hu
    have hprod := mul_le_mul (hdloc u x hdist') (hUloc u x hdist')
      (hU x) (mul_nonneg hA₀ (hd u))
    have hprod' := mul_le_mul_of_nonneg_left hprod (show 0 ≤ (2 : ℝ) by norm_num)
    have hWprod := mul_le_mul_of_nonneg_right (hW u).1 (hU u)
    have hWprod' := mul_le_mul_of_nonneg_left hWprod (mul_nonneg hA₀ hB₀)
    dsimp only [D, Q]
    nlinarith only [hprod', hWprod']
  have hQupper (u : ℝ) (hu : u ∈ Icc a x) : Q u ≤ (6 * A * B) * D := by
    have hprod := mul_le_mul (hdloc x u (hdist u hu)) (hUloc x u (hdist u hu))
      (hU u) (mul_nonneg hA₀ (hd x))
    have hprod' := mul_le_mul_of_nonneg_left hprod (show 0 ≤ (6 : ℝ) by norm_num)
    have hWprod := mul_le_mul_of_nonneg_right (hW u).2 (hU u)
    dsimp only [D, Q]
    nlinarith only [hprod', hWprod]
  have hDcontrol : D ≤ b₂ * I := by
    apply (mul_le_mul_iff_of_pos_left hk).mp
    calc
      k * D = ∫ u in a..b, 2 * k * D := by
        rw [intervalIntegral.integral_const, hablen, smul_eq_mul]
        ring
      _ ≤ ∫ u in a..b, (A * B) * F u := by
        apply intervalIntegral.integral_mono_on hab intervalIntegrable_const
          ((hFc.intervalIntegrable a b).const_mul _)
        intro u hu
        have hu' : u ∈ Icc a x := ⟨hu.1, hu.2.trans hbx⟩
        have hlow := mul_le_mul_of_nonneg_left (hQlower u hu') hk.le
        have hkv : k ≤ amplitudeKernel (x - u) := by
          apply amplitudeKernel_half_le
          have hu₂ : u ≤ x - 1 / 2 := hu.2
          linarith only [hu₂]
        have hhigh := mul_le_mul_of_nonneg_right hkv (mul_nonneg (mul_nonneg hA₀ hB₀) (hQ₀ u))
        change 2 * k * D ≤ (A * B) * (amplitudeKernel (x - u) * Q u)
        nlinarith only [hlow, hhigh]
      _ = (A * B) * (∫ u in a..b, F u) := intervalIntegral.integral_const_mul _ _
      _ ≤ (A * B) * I := mul_le_mul_of_nonneg_left
        (intervalIntegral.integral_mono_interval ha hab hbx (ae_of_all _ hF₀)
          (hFc.intervalIntegrable 0 x)) (mul_nonneg hA₀ hB₀)
      _ = k * (b₂ * I) := by
        dsimp only [b₂]
        field_simp [hk.ne']
        <;> ring
  have hEndpoint : U x * p x ≤ 4 * B * P + L * D := by
    calc
      U x * p x = ∫ u in a..b, 2 * (U x * p x) := by
        rw [intervalIntegral.integral_const, hablen, smul_eq_mul]
        ring
      _ ≤ ∫ u in a..b, 4 * B * V u + 2 * L * D := by
        apply intervalIntegral.integral_mono_on hab intervalIntegrable_const
          (((hVc.intervalIntegrable a b).const_mul _).add intervalIntegrable_const)
        intro u hu
        have hu' : u ∈ Icc a x := ⟨hu.1, hu.2.trans hbx⟩
        have hdist' : |x - u| ≤ 1 := by simpa only [abs_sub_comm] using hdist u hu'
        have hphase := mul_le_mul_of_nonneg_left (hploc x u hu') (hU x)
        have hamp := mul_le_mul_of_nonneg_right (hUloc u x hdist') (hp u)
        change 2 * (U x * p x) ≤ 4 * B * (U u * p u) + 2 * L * (d x * U x)
        nlinarith only [hphase, hamp]
      _ = 4 * B * (∫ u in a..b, V u) + L * D := by
        rw [intervalIntegral.integral_add ((hVc.intervalIntegrable (μ := volume) a b).const_mul (4 * B))
          intervalIntegrable_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
          hablen, smul_eq_mul]
        ring
      _ ≤ _ := add_le_add_left
        (mul_le_mul_of_nonneg_left
          (intervalIntegral.integral_mono_interval ha hab hbx (ae_of_all _ hV₀)
            (hVc.intervalIntegrable 0 x)) (by positivity)) _
  have hInterior : (∫ u in (0 : ℝ)..b, F' u) ≤ c * I := by
    calc
      _ ≤ ∫ u in (0 : ℝ)..b, c * F u := by
        apply intervalIntegral.integral_mono_on hb (hF'c.intervalIntegrable 0 b)
          ((hFc.intervalIntegrable 0 b).const_mul _)
        intro u hu
        have hu₂ : u ≤ x - 1 / 2 := hu.2
        have h := amplitudeKernelDeriv_le_mul (x - u) (by linarith only [hu₂])
        change amplitudeKernelDeriv (x - u) * Q u ≤ c * (amplitudeKernel (x - u) * Q u)
        simpa only [c, mul_assoc] using mul_le_mul_of_nonneg_right h (hQ₀ u)
      _ = c * (∫ u in (0 : ℝ)..b, F u) := intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (intervalIntegral.integral_mono_interval le_rfl hb hbx (ae_of_all _ hF₀)
          (hFc.intervalIntegrable 0 x)) hc
  have hBoundary : (∫ u in b..x, F' u) ≤ b₁ * D := by
    let M := amplitudeKernelDeriv (1 / 2) * ((6 * A * B) * D)
    calc
      _ ≤ ∫ _ in b..x, M := by
        apply intervalIntegral.integral_mono_on hbx (hF'c.intervalIntegrable b x)
          intervalIntegrable_const
        intro u hu
        have hu' : u ∈ Icc a x := ⟨hab.trans hu.1, hu.2⟩
        have hu₁ : x - 1 / 2 ≤ u := hu.1
        have hkd := amplitudeKernelDeriv_le_half (show x - u ≤ 1 / 2 by linarith only [hu₁])
        exact mul_le_mul hkd (hQupper u hu') (hQ₀ u) amplitudeKernelDeriv_half_nonneg
      _ = _ := by
        rw [intervalIntegral.integral_const, hbxlen, smul_eq_mul]
        dsimp only [M, b₁]
        ring
  have hRate : (∫ u in (0 : ℝ)..x, F' u) ≤ c * I + b₁ * D := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hF'c.intervalIntegrable (μ := volume) 0 b)
      (hF'c.intervalIntegrable (μ := volume) b x)]
    exact add_le_add hInterior hBoundary
  have hCoeff := mul_le_mul_of_nonneg_left hDcontrol (add_nonneg hb₁ hL)
  change (∫ u in (0 : ℝ)..x, F' u) + U x * p x ≤ C * (I + P)
  calc
    _ ≤ (c + (b₁ + L) * b₂) * I + (4 * B) * P := by
      nlinarith only [hRate, hEndpoint, hCoeff]
    _ ≤ _ := by
      dsimp only [C]
      nlinarith only [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hB₀) hI₀,
        mul_nonneg (add_nonneg hc (mul_nonneg (add_nonneg hb₁ hL) hb₂)) hP₀]

private lemma hasDerivAt_comp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g g' : ℝ → E} (hg : ∀ x, HasDerivAt g (g' x) x) (x : ℝ) :
    HasDerivAt (fun t ↦ g (-t)) (-g' (-x)) x := by
  simpa only [Function.comp_def, id, neg_one_smul] using
    (hg (-x)).scomp x ((hasDerivAt_id x).neg)

/-- A differential bound on the absolute derivative gives a two-sided comparison
on intervals of length at most one, including zeros of the underlying function. -/
theorem local_exp_comparison_of_abs_derivative {g g' : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg₀ : ∀ t, 0 ≤ g t) (hbound : ∀ t, |g' t| ≤ C * g t)
    {x u : ℝ} (hgap : |u - x| ≤ 1) : g u ≤ Real.exp C * g x := by
  have hforward {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
      (hf₀ : ∀ t, 0 ≤ f t) (hrate : ∀ t, f' t ≤ C * f t)
      {a b : ℝ} (hab : a ≤ b) (hgap' : b - a ≤ 1) : f b ≤ Real.exp C * f a := by
    apply (le_exp_mul_of_hasDerivAt_le hab (fun t _ ↦ hf t) (fun t _ ↦ hrate t)).trans
    apply mul_le_mul_of_nonneg_right _ (hf₀ a)
    apply Real.exp_le_exp.mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hgap' hC
  by_cases hxu : x ≤ u
  · exact hforward hg hg₀ (fun t ↦ (le_abs_self _).trans (hbound t)) hxu
      ((le_abs_self _).trans hgap)
  · have hux : u ≤ x := (le_of_not_ge hxu)
    have hneg : -x ≤ -u := neg_le_neg hux
    have hgap' : -u - -x ≤ 1 := by
      have habs := (abs_le.mp hgap).1
      linarith only [habs]
    have h := hforward (hasDerivAt_comp_neg hg) (fun t ↦ hg₀ (-t))
      (fun t ↦ (show -g' (-t) ≤ |g' (-t)| by simpa only [abs_neg] using le_abs_self (-g' (-t))).trans
        (hbound (-t))) hneg hgap'
    simpa only [neg_neg] using h

/-- The diameter energy is the sum of the energy on both half intervals. -/
def diameterEnergy (Q V : ℝ → ℝ) (x : ℝ) : ℝ :=
  diameterHalfEnergy Q V x + diameterHalfEnergy (fun t ↦ Q (-t)) (fun t ↦ V (-t)) x

/-- The exact derivative of the two half energies. -/
def diameterRate (Q V : ℝ → ℝ) (x : ℝ) : ℝ :=
  diameterHalfRate Q V x + diameterHalfRate (fun t ↦ Q (-t)) (fun t ↦ V (-t)) x

theorem diameterEnergy_nonneg {Q V : ℝ → ℝ} (hQ : ∀ t, 0 ≤ Q t) (hV : ∀ t, 0 ≤ V t)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ diameterEnergy Q V x := by
  have hh {q v : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (hv : ∀ t, 0 ≤ v t) :
      0 ≤ diameterHalfEnergy q v x :=
    add_nonneg (intervalIntegral.integral_nonneg_of_forall hx fun t ↦
      mul_nonneg (amplitudeKernel_nonneg _) (hq t)) (intervalIntegral.integral_nonneg_of_forall hx hv)
  exact add_nonneg (hh hQ hV) (hh (fun t ↦ hQ (-t)) (fun t ↦ hV (-t)))

theorem hasDerivAt_diameterEnergy {Q V : ℝ → ℝ} (hQ : Continuous Q) (hV : Continuous V) (x : ℝ) :
    HasDerivAt (diameterEnergy Q V) (diameterRate Q V x) x :=
  (hasDerivAt_diameterHalfEnergy hQ hV x).fun_add
    (hasDerivAt_diameterHalfEnergy (hQ.comp continuous_neg) (hV.comp continuous_neg) x)

/-- The reflected-half definition agrees with the symmetric diameter integral. -/
theorem diameterEnergy_eq_symmetric_integral {Q V : ℝ → ℝ}
    (hQ : Continuous Q) (hV : Continuous V) {x : ℝ} (hx : 0 ≤ x) :
    diameterEnergy Q V x =
      (∫ u in -x..x, amplitudeKernel (x - |u|) * Q u) + ∫ u in -x..x, V u := by
  let F (u : ℝ) := amplitudeKernel (x - |u|) * Q u
  have hF : Continuous F := (amplitudeKernel_continuous.comp
    (continuous_const.sub continuous_abs)).mul hQ
  have hPlus : (∫ u in (0 : ℝ)..x, amplitudeKernel (x - u) * Q u) = ∫ u in (0 : ℝ)..x, F u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hx] at hu
    change amplitudeKernel (x - u) * Q u = amplitudeKernel (x - |u|) * Q u
    rw [abs_of_nonneg hu.1]
  have hMinus : (∫ u in (0 : ℝ)..x, amplitudeKernel (x - u) * Q (-u)) =
      ∫ u in -x..(0 : ℝ), F u := by
    calc
      _ = ∫ u in (0 : ℝ)..x, F (-u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hx] at hu
        change amplitudeKernel (x - u) * Q (-u) = amplitudeKernel (x - |-u|) * Q (-u)
        rw [abs_neg, abs_of_nonneg hu.1]
      _ = _ := by rw [intervalIntegral.integral_comp_neg F, neg_zero]
  have hVneg : (∫ u in (0 : ℝ)..x, V (-u)) = ∫ u in -x..(0 : ℝ), V u := by
    rw [intervalIntegral.integral_comp_neg V, neg_zero]
  have hFjoin := intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (μ := volume) (-x) 0) (hF.intervalIntegrable (μ := volume) 0 x)
  have hVjoin := intervalIntegral.integral_add_adjacent_intervals
    (hV.intervalIntegrable (μ := volume) (-x) 0) (hV.intervalIntegrable (μ := volume) 0 x)
  unfold diameterEnergy diameterHalfEnergy
  rw [hPlus, hMinus, hVneg]
  change (∫ u in (0 : ℝ)..x, F u) + (∫ u in (0 : ℝ)..x, V u) +
    ((∫ u in -x..(0 : ℝ), F u) + ∫ u in -x..(0 : ℝ), V u) =
      (∫ u in -x..x, F u) + ∫ u in -x..x, V u
  linarith only [hFjoin, hVjoin]

/-- The complex phase and the amplitude-deficit differential bounds give the
diameter differential inequality with one constant for the two endpoints. -/
theorem exists_diameterEnergy_rate_le (Cd Cu : ℝ) (hCd : 0 ≤ Cd) (hCu : 0 ≤ Cu) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d d' U U' W : ℝ → ℝ} {P P' : ℝ → ℂ} (γ : ℂ),
      Continuous W → (∀ t, HasDerivAt d (d' t) t) → (∀ t, HasDerivAt U (U' t) t) →
      (∀ t, HasDerivAt P (P' t) t) → (∀ t, 0 ≤ d t) → (∀ t, 0 ≤ U t) →
      (∀ t, 2 * d t ≤ W t ∧ W t ≤ 6 * d t) →
      (∀ t, |d' t| ≤ Cd * d t) → (∀ t, |U' t| ≤ Cu * U t) →
      (∀ t, ‖P' t‖ ≤ 2 * Real.sqrt (d t)) →
      ∀ x ≥ 2, diameterRate (fun t ↦ W t * U t) (fun t ↦ U t * (‖P t - γ‖ ^ 2 / 2)) x ≤
        C * diameterEnergy (fun t ↦ W t * U t) (fun t ↦ U t * (‖P t - γ‖ ^ 2 / 2)) x := by
  let A := Real.exp Cd
  let B := Real.exp Cu
  have hA : 1 ≤ A := Real.one_le_exp_iff.mpr hCd
  have hB : 1 ≤ B := Real.one_le_exp_iff.mpr hCu
  obtain ⟨C, hC, hbound⟩ := exists_diameterHalfRate_le A B (4 * A) hA hB
    (mul_nonneg (by norm_num) (zero_le_one.trans hA))
  refine ⟨C, hC, ?_⟩
  intro d d' U U' W P P' γ hWc hd' hU' hP' hd hU hW hdRate hURate hspeed x hx
  let p (t : ℝ) := ‖P t - γ‖ ^ 2 / 2
  have hUc : Continuous U := continuous_iff_continuousAt.mpr fun t ↦ (hU' t).continuousAt
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun t ↦ (hP' t).continuousAt
  have hpc : Continuous p := ((hPc.sub continuous_const).norm.pow 2).div_const _
  have hp₀ (t : ℝ) : 0 ≤ p t := div_nonneg (sq_nonneg _) (by norm_num)
  have hdlocal (t u : ℝ) (hgap : |u - t| ≤ 1) : d u ≤ A * d t :=
    local_exp_comparison_of_abs_derivative hCd hd' hd hdRate hgap
  have hUlocal (t u : ℝ) (hgap : |u - t| ≤ 1) : U u ≤ B * U t :=
    local_exp_comparison_of_abs_derivative hCu hU' hU hURate hgap
  have hpp (t u : ℝ) (hu : u ∈ Icc (t - 1) t) : p t ≤ 2 * p u + (4 * A) * d t := by
    apply phase_deficit_endpoint_le
    apply phase_endpoint_sq_le hP' hd (zero_le_one.trans hA) hspeed _ hu
    intro v hv
    apply hdlocal
    rw [abs_of_nonpos (sub_nonpos.mpr hv.2)]
    linarith only [hv.1]
  have hboundPlus := hbound hWc hUc hpc hd hU hp₀ hW hdlocal hUlocal hpp x hx
  have hdlocalNeg (t u : ℝ) (hgap : |u - t| ≤ 1) : d (-u) ≤ A * d (-t) := by
    apply hdlocal
    rwa [show -u - -t = -(u - t) by ring, abs_neg]
  have hUlocalNeg (t u : ℝ) (hgap : |u - t| ≤ 1) : U (-u) ≤ B * U (-t) := by
    apply hUlocal
    rwa [show -u - -t = -(u - t) by ring, abs_neg]
  have hppNeg (t u : ℝ) (hu : u ∈ Icc (t - 1) t) :
      p (-t) ≤ 2 * p (-u) + (4 * A) * d (-t) := by
    apply phase_deficit_endpoint_le (P := fun v ↦ P (-v)) (x := t) (u := u)
    refine phase_endpoint_sq_le (d := fun v ↦ d (-v)) (hasDerivAt_comp_neg hP') (fun v ↦ hd (-v))
      (zero_le_one.trans hA) (fun v ↦ ?_) ?_ hu
    · simpa only [norm_neg] using hspeed (-v)
    · intro v hv
      apply hdlocalNeg
      rw [abs_of_nonpos (sub_nonpos.mpr hv.2)]
      linarith only [hv.1]
  have hboundMinus := hbound (hWc.comp continuous_neg) (hUc.comp continuous_neg)
    (hpc.comp continuous_neg) (fun t ↦ hd (-t)) (fun t ↦ hU (-t)) (fun t ↦ hp₀ (-t))
    (fun t ↦ hW (-t)) hdlocalNeg hUlocalNeg hppNeg x hx
  unfold diameterRate diameterEnergy
  rw [mul_add]
  exact add_le_add hboundPlus hboundMinus

/-- The unit-phase distance agrees with the real-part deficit. -/
theorem unit_phase_distance_eq_deficit {z γ : ℂ} (hz : ‖z‖ = 1) (hγ : ‖γ‖ = 1) :
    ‖z - γ‖ ^ 2 / 2 = 1 - (conj γ * z).re := by
  rw [Complex.sq_norm, Complex.normSq_sub]
  simp only [Complex.normSq_eq_norm_sq, hz, hγ, one_pow, mul_comm z (conj γ)]
  ring

/-- The amplitude equation and the unit-phase trace identify the diameter
energy with the unnormalized complex chord deficit. -/
theorem diameterEnergy_eq_trace_deficit {F P : ℝ → ℂ} {U U' Q : ℝ → ℝ} {γ : ℂ}
    (hF : ∀ t, HasDerivAt F ((U t : ℂ) * P t) t)
    (hP : Continuous P) (hP₁ : ∀ t, ‖P t‖ = 1) (hγ : ‖γ‖ = 1)
    (hU : ∀ t, HasDerivAt U (U' t) t) (hU' : ∀ t, HasDerivAt U' (16 * U t - Q t) t)
    (hU₀ : U 0 = 1) (hQ : Continuous Q) {x : ℝ} (hx : 0 ≤ x) :
    diameterEnergy Q (fun t ↦ U t * (‖P t - γ‖ ^ 2 / 2)) x =
      Real.sinh (4 * x) / 2 - (conj γ * (F x - F (-x))).re := by
  let p (t : ℝ) := ‖P t - γ‖ ^ 2 / 2
  let V (t : ℝ) := U t * p t
  have hUc : Continuous U := continuous_iff_continuousAt.mpr fun t ↦ (hU t).continuousAt
  have hpc : Continuous p := ((hP.sub continuous_const).norm.pow 2).div_const _
  have hVc : Continuous V := hUc.mul hpc
  have hTrace (t : ℝ) : HasDerivAt (fun u ↦ (conj γ * F u).re) (U t - V t) t := by
    have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ((hF t).const_mul (conj γ))
    have he : (conj γ * ((U t : ℂ) * P t)).re = U t - V t := by
      rw [show conj γ * ((U t : ℂ) * P t) = (U t : ℂ) * (conj γ * P t) by ring,
        Complex.re_ofReal_mul]
      dsimp only [V, p]
      rw [unit_phase_distance_eq_deficit (hP₁ t) hγ]
      ring
    simpa only [Function.comp_def, Complex.reCLM_apply, he] using hd
  have hTraceInt := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hTrace t)
    ((hUc.sub hVc).intervalIntegrable (-x) x)
  rw [intervalIntegral.integral_sub (hUc.intervalIntegrable (μ := volume) (-x) x)
    (hVc.intervalIntegrable (μ := volume) (-x) x),
    ← Complex.sub_re, ← mul_sub] at hTraceInt
  have hAmp := intervalIntegral_amplitude_symmetric_eq hU hU' hQ hx
  rw [hU₀, one_mul] at hAmp
  change diameterEnergy Q V x = _
  rw [diameterEnergy_eq_symmetric_integral hQ hVc hx]
  linarith only [hAmp, hTraceInt]

/-- Dividing by the increasing Koebe chord length transfers the diameter
differential estimate to a comparison at Euclidean radii. -/
theorem normalized_diameterEnergy_le {Q V : ℝ → ℝ} (hQc : Continuous Q) (hVc : Continuous V)
    (hQ : ∀ t, 0 ≤ Q t) (hV : ∀ t, 0 ≤ V t) {C r s : ℝ} (hC : 0 ≤ C)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s < 1) (hX : 2 ≤ Real.artanh r)
    (hRate : ∀ x ≥ 2, diameterRate Q V x ≤ C * diameterEnergy Q V x) :
    diameterEnergy Q V (Real.artanh s) / (Real.sinh (4 * Real.artanh s) / 2) ≤
      (2 : ℝ) ^ (C / 2) * ((1 - r) / (1 - s)) ^ (C / 2) *
        (diameterEnergy Q V (Real.artanh r) / (Real.sinh (4 * Real.artanh r) / 2)) := by
  have hxy := Real.artanh_le_artanh (show -1 < r by linarith) hs hrs
  have hrpos : 0 < Real.artanh r := by linarith only [hX]
  have hZpos : 0 < Real.sinh (4 * Real.artanh r) / 2 :=
    div_pos (Real.sinh_pos_iff.mpr (by positivity)) (by norm_num)
  have hZmono : Real.sinh (4 * Real.artanh r) / 2 ≤ Real.sinh (4 * Real.artanh s) / 2 :=
    div_le_div_of_nonneg_right (Real.sinh_le_sinh.mpr (by linarith only [hxy])) (by norm_num)
  exact normalized_deficit_le_of_hasDerivAt_le
    (H := diameterEnergy Q V) (H' := diameterRate Q V) (Z := fun x ↦ Real.sinh (4 * x) / 2) hr hrs hs hC
    (fun x _ ↦ hasDerivAt_diameterEnergy hQc hVc x)
    (fun x hx ↦ hRate x (hX.trans hx.1))
    (diameterEnergy_nonneg hQ hV hrpos.le) hZpos hZmono

end Zalcman
