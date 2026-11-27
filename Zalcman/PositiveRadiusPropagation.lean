/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.OneSidedRadial
public import Zalcman.RadialJet
public import Zalcman.RadialProjection
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Propagation on the positive radius
-/

@[expose] public section

namespace Zalcman

open Set
open scoped ComplexConjugate

/-- The Koebe normalization in hyperbolic time. -/
noncomputable def positiveRadiusNormalization (x : ℝ) : ℝ := (Real.exp (4 * x) - 1) / 4

/-- The unnormalized positive-radius deficit. -/
noncomputable def positiveRadiusDeficit (f : ℂ → ℂ) (γ : ℂ) (x : ℝ) : ℝ :=
  positiveRadiusNormalization x - (conj γ * radialTrace f x).re

/-- The Koebe normalization grows at rate `exp (4*x)`. -/
theorem hasDerivAt_positiveRadiusNormalization (x : ℝ) :
    HasDerivAt positiveRadiusNormalization (Real.exp (4 * x)) x := by
  have h := ((((hasDerivAt_id x).const_mul (4 : ℝ)).exp).sub_const (1 : ℝ)).div_const 4
  convert h using 1 <;> try rfl
  simp only [id, mul_one]
  ring

private theorem exp_coord_real_cancel (t : ℝ) :
    Real.exp (4 * t) * Real.exp (-(4 * t)) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem hasDerivAt_positiveRadiusDeficit {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    (γ : ℂ) (t : ℝ) :
    HasDerivAt (positiveRadiusDeficit f γ) (Real.exp (4 * t) *
      (1 - ((Real.exp (-(4 * t)) : ℂ) * conj γ * deriv (radialTrace f) t).re)) t := by
  have h := (hasDerivAt_positiveRadiusNormalization t).fun_sub
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_radialTrace hf t).differentiableAt.hasDerivAt.const_mul (conj γ)))
  convert h using 1 <;> try rfl
  simp only [Complex.reCLM_apply, mul_assoc, Complex.re_ofReal_mul]
  rw [mul_sub, mul_one, ← mul_assoc, exp_coord_real_cancel, one_mul]

private noncomputable def scaledTraceVelocity (f : ℂ → ℂ) (γ : ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-(4 * t)) : ℂ) * conj γ * deriv (radialTrace f) t

private theorem hasDerivAt_scaledTraceVelocity {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    (γ : ℂ) (t : ℝ) :
    HasDerivAt (scaledTraceVelocity f γ)
      (2 * (coeff (hyperbolicTranslate f t) 2 - 2) * scaledTraceVelocity f γ t) t := by
  have hF := hasDerivAt_radialTrace_iteratedDeriv hf.holomorphic 1 t
  rw [iteratedDeriv_one, (radialTrace_iteratedDeriv_of_translate hf t).1] at hF
  have hRate : HasDerivAt (fun v : ℝ ↦ -(4 * v)) (-4) t := by
    simpa only [id, mul_one, neg_mul] using! (hasDerivAt_id t).const_mul (-4 : ℝ)
  have h := ((hRate.exp.ofReal_comp).mul_const (conj γ)).fun_mul hF
  convert h using 1 <;> try rfl
  simp only [scaledTraceVelocity, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  ring

private theorem hasDerivAt_realSecondDeficit {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (t : ℝ) :
    let q : ℝ → ℂ := fun x ↦ coeff (hyperbolicTranslate f x) 2
    let a := coeff (hyperbolicTranslate f t) 3
    HasDerivAt (fun x ↦ 2 - (q x).re) (-(3 * a - 2 * q t ^ 2 - 1).re) t := by
  have hq := (hasDerivAt_translate_coeffs hf t).1
  simpa only [Function.comp_apply, Complex.reCLM_apply, zero_sub] using!
    (hasDerivAt_const t (2 : ℝ)).fun_sub
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hq)

/-- A uniform differential bound for the positive-radius deficit. -/
theorem exists_positiveRadiusDeficit_deriv_le :
    ∃ E > 0, ∀ {f : ℂ → ℂ} (hf : NormalizedUnivalent f) {γ : ℂ} (hγ : ‖γ‖ = 1)
      (x : ℝ), 2 ≤ x → deriv (positiveRadiusDeficit f γ) x ≤ E * positiveRadiusDeficit f γ x := by
  let C := 6 * (4 + (2 * Real.exp (-8))⁻¹) + 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨Real.exp (C + 4), Real.exp_pos _, ?_⟩
  intro f hf γ hγ x hx
  let q (t : ℝ) := coeff (hyperbolicTranslate f t) 2
  let P := scaledTraceVelocity f γ
  let V (t : ℝ) := 1 - (P t).re
  have hq (t : ℝ) : ‖q t‖ ≤ 2 := norm_coeff_two_le (hf.hyperbolicTranslate t)
  have hE'le (t : ℝ) : deriv (fun v ↦ 2 - (q v).re) t ≤ 8 * (2 - (q t).re) := by
    rw [(hasDerivAt_realSecondDeficit hf t).deriv]
    exact real_second_deficit_derivative_le (hq t)
      (norm_coeff_two_sq_sub_coeff_three_le (hf.hyperbolicTranslate t))
  have hPne (t : ℝ) : P t ≠ 0 := by
    have hγne : γ ≠ 0 := by
      intro h
      simp [h] at hγ
    exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
      ((map_ne_zero (starRingEnd ℂ)).mpr hγne)) (radialTrace_deriv_ne_zero hf t)
  have hF₀ : deriv (radialTrace f) 0 = 1 := by
    rw [(hasDerivAt_radialTrace hf 0).deriv]
    simp [hf.deriv_zero]
  have hP₀ : ‖P 0‖ = 1 := by
    simp only [P, scaledTraceVelocity, hF₀, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one,
      one_mul, mul_one, Complex.norm_conj, hγ]
  have hV' (t : ℝ) : HasDerivAt V (deriv V t) t :=
    ((hasDerivAt_const t (1 : ℝ)).fun_sub (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_scaledTraceVelocity hf γ t))).differentiableAt.hasDerivAt
  have hVd := radial_velocity_deficit_deriv_le
    (fun t _ ↦ hasDerivAt_scaledTraceVelocity hf γ t) (fun t _ ↦ hPne t)
    hP₀ (fun t _ ↦ hq t) (fun t _ ↦ (hasDerivAt_realSecondDeficit hf t).differentiableAt.hasDerivAt)
    (fun t _ ↦ hE'le t)
  have hV₀ (t : ℝ) (ht : 0 ≤ t) : 0 ≤ V t := by
    have hnorm (v : ℝ) : HasDerivAt (fun y ↦ ‖P y‖) (2 * (q v - 2).re * ‖P v‖) v :=
      hasDerivAt_velocity_norm (hasDerivAt_scaledTraceVelocity hf γ v) (hPne v)
    have h := le_exp_mul_of_hasDerivAt_le (x := 0) (y := t) (C := 0) ht
      (fun v _ ↦ hnorm v) (fun v _ ↦ by
        have hqre := (Complex.re_le_norm (q v)).trans (hq v)
        simp only [zero_mul, Complex.sub_re, Complex.re_ofNat]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hqre]) (norm_nonneg _))
    simp only [zero_mul, Real.exp_zero, one_mul, hP₀] at h
    exact sub_nonneg.mpr ((Complex.re_le_norm _).trans h)
  have hH₀ : positiveRadiusDeficit f γ 0 = 0 := by
    simp [positiveRadiusDeficit, positiveRadiusNormalization, radialTrace, hf.map_zero]
  exact oneSided_radial_deficit_deriv_le hC hH₀ hV₀
    (fun t _ ↦ hasDerivAt_positiveRadiusDeficit hf γ t) (fun t _ ↦ hV' t) hVd hx

private theorem positiveRadiusDeficit_div_normalization {f : ℂ → ℂ} (γ : ℂ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hZ : 0 < positiveRadiusNormalization (Real.artanh t)) :
    positiveRadiusDeficit f γ (Real.artanh t) / positiveRadiusNormalization (Real.artanh t) =
      radialPhaseDeficit f γ t := by
  have hK : koebe (t : ℂ) = (positiveRadiusNormalization (Real.artanh t) : ℂ) := by
    simpa only [Real.tanh_artanh ht, positiveRadiusNormalization] using koebe_tanh_eq (Real.artanh t)
  simp only [positiveRadiusDeficit, radialPhaseDeficit, radialTrace, Real.tanh_artanh ht, hK]
  rw [sub_div, div_self hZ.ne', div_eq_mul_inv (f (t : ℂ)), ← mul_assoc,
    mul_comm (conj γ * f (t : ℂ)), ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  congr 1
  exact div_eq_inv_mul _ _

/-- The positive-radius phase deficit has a uniform two-radius propagation bound. -/
theorem exists_positive_radius_deficit_propagation :
    ∃ K : ℝ, 0 < K ∧ ∃ B : ℝ, 0 < B ∧ ∀ {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
      (hCoeff : ∀ n : ℕ, ‖coeff f n‖ ≤ n) {γ : ℂ} (hγ : ‖γ‖ = 1)
      {r s : ℝ}, Real.tanh 2 ≤ r → 0 < r → r ≤ s → s < 1 →
      radialPhaseDeficit f γ s ≤ K * ((1 - r) / (1 - s)) ^ B * radialPhaseDeficit f γ r := by
  obtain ⟨E, hE, hHd⟩ := exists_positiveRadiusDeficit_deriv_le
  refine ⟨(2 : ℝ) ^ (E / 2), by positivity, E / 2, by positivity, ?_⟩
  intro f hf hCoeff γ hγ r s hr₀ hr hrs hs
  let H := positiveRadiusDeficit f γ
  let Z := positiveRadiusNormalization
  have hrI : r ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hrs.trans_lt hs⟩
  have hsI : s ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hs⟩
  have h₂r : 2 ≤ Real.artanh r := by
    have hh := Real.artanh_le_artanh (Real.neg_one_lt_tanh (2 : ℝ)) hrI.2 hr₀
    simpa only [Real.artanh_tanh] using hh
  have hXY := Real.artanh_le_artanh hrI.1 hs hrs
  have hZmono : Z (Real.artanh r) ≤ Z (Real.artanh s) := by
    apply div_le_div_of_nonneg_right (sub_le_sub_right (Real.exp_le_exp.mpr (by linarith only [hXY])) _)
    norm_num
  have hZpos : 0 < Z (Real.artanh r) := by
    exact div_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith only [h₂r]))) (by norm_num)
  have hHR : 0 ≤ H (Real.artanh r) := by
    have h : 0 ≤ H (Real.artanh r) / Z (Real.artanh r) := by
      change 0 ≤ positiveRadiusDeficit f γ (Real.artanh r) / positiveRadiusNormalization (Real.artanh r)
      rw [positiveRadiusDeficit_div_normalization γ hrI hZpos]
      exact radialPhaseDeficit_nonneg hf hγ hCoeff hr hrI.2
    simpa only [zero_mul] using (le_div_iff₀ hZpos).mp h
  have h := normalized_deficit_le_of_hasDerivAt_le hr.le hrs hs hE.le
    (fun t _ ↦ (hasDerivAt_positiveRadiusDeficit hf γ t).differentiableAt.hasDerivAt)
    (fun t ht ↦ hHd hf hγ t (h₂r.trans ht.1)) hHR hZpos hZmono
  change H (Real.artanh s) / Z (Real.artanh s) ≤ _ at h
  simpa only [H, Z, positiveRadiusDeficit_div_normalization γ hsI (hZpos.trans_le hZmono),
    positiveRadiusDeficit_div_normalization γ hrI hZpos] using h

end Zalcman
