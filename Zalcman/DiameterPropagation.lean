/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.DiameterBoundary
public import Zalcman.LowDegreeMilin
public import Zalcman.RadialJet
public import Zalcman.RadialKinematics
public import Zalcman.RadialProjection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Propagation of the odd coefficient deficit

The symmetric amplitude and phase integrals apply to the radial trace
once the low-degree coefficient bounds hold for its hyperbolic translates.
-/

public section

namespace Zalcman

open Set
open scoped ComplexConjugate

private theorem koebe_tanh_chord_eq (x : ℝ) :
    koebe (Real.tanh x : ℂ) - koebe (-(Real.tanh x : ℂ)) =
      ((Real.sinh (4 * x) / 2 : ℝ) : ℂ) := by
  rw [show -(Real.tanh x : ℂ) = (Real.tanh (-x) : ℂ) by
    rw [Real.tanh_neg, Complex.ofReal_neg]]
  rw [koebe_tanh_eq, koebe_tanh_eq, ← Complex.ofReal_sub]
  congr 1
  rw [Real.sinh_eq, show 4 * (-x) = -(4 * x) by ring]
  ring

private theorem diameter_trace_div_normalization {f : ℂ → ℂ} (γ : ℂ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) (ht' : 0 < Real.artanh t) :
    ((Real.sinh (4 * Real.artanh t) / 2) -
        (conj γ * (radialTrace f (Real.artanh t) - radialTrace f (-Real.artanh t))).re) /
      (Real.sinh (4 * Real.artanh t) / 2) = oddRadialPhaseDeficit f γ t := by
  let Z := Real.sinh (4 * Real.artanh t) / 2
  have hZ : 0 < Z :=
    div_pos (Real.sinh_pos_iff.mpr (mul_pos (by norm_num) ht')) (by norm_num)
  have hK : koebe (t : ℂ) - koebe (-(t : ℂ)) = (Z : ℂ) := by
    simpa only [Z, Real.tanh_artanh ht] using koebe_tanh_chord_eq (Real.artanh t)
  simp only [radialTrace, Real.tanh_neg, Real.tanh_artanh ht, Complex.ofReal_neg,
    oddRadialPhaseDeficit, hK]
  generalize (f (t : ℂ) - f (-(t : ℂ))) = D
  change (Z - (conj γ * D).re) / Z = 1 - (conj γ * (D / (Z : ℂ))).re
  rw [sub_div, div_self hZ.ne', div_eq_mul_inv D, ← mul_assoc,
    mul_comm (conj γ * D), ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  congr 1
  exact div_eq_inv_mul _ _

/-- The low-degree real-part estimate implies a uniform two-radius bound
for the odd phase deficit. -/
theorem exists_odd_radius_deficit_propagation_of_low_degree
    (hm : ∀ {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ), 0 ≤ (milinCoefficients hf).milinSum n)
    {C : ℝ} (hC : 0 ≤ C)
    (hLow : ∀ {f : ℂ → ℂ}, NormalizedUnivalent f →
      |(coeff f 4 - 2 * coeff f 2).re| ≤ C * (3 - (coeff f 3).re)) :
    ∃ K : ℝ, 0 < K ∧ ∃ B : ℝ, 0 < B ∧
      ∀ {f : ℂ → ℂ} (hf : NormalizedUnivalent f) {γ : ℂ} (hγ : ‖γ‖ = 1)
      {r s : ℝ}, Real.tanh 2 ≤ r → 0 < r → r ≤ s → s < 1 →
      oddRadialPhaseDeficit f γ s ≤ K * ((1 - r) / (1 - s)) ^ B * oddRadialPhaseDeficit f γ r := by
  obtain ⟨E, hE, hBound⟩ := exists_diameterEnergy_rate_le (4 * C + 11) 4 (by positivity) (by norm_num)
  refine ⟨(2 : ℝ) ^ (E / 2), by positivity, E / 2, by positivity, ?_⟩
  intro f hf γ hγ r s hr₀ hr hrs hs
  let F := radialTrace f
  let V := deriv F
  let q (t : ℝ) := coeff (hyperbolicTranslate f t) 2
  let a (t : ℝ) := coeff (hyperbolicTranslate f t) 3
  let b (t : ℝ) := coeff (hyperbolicTranslate f t) 4
  let d (t : ℝ) := 3 - (a t).re
  let U (t : ℝ) := ‖V t‖
  let P (t : ℝ) := V t / (U t : ℂ)
  let W (t : ℝ) := 6 * d t - 4 * (q t).im ^ 2
  have hq (t : ℝ) : ‖q t‖ ≤ 2 := norm_coeff_two_le (hf.hyperbolicTranslate t)
  have ha (t : ℝ) : ‖a t‖ ≤ 3 := by
    exact_mod_cast norm_coeff_le_of_milinSum_nonneg (hf.hyperbolicTranslate t) (hm (hf.hyperbolicTranslate t) 3)
  have him (t : ℝ) : (q t).im ^ 2 ≤ d t :=
    im_coeff_two_sq_le_three_sub_re_coeff_three_of_milin (hf.hyperbolicTranslate t)
      (hm (hf.hyperbolicTranslate t) 2) (hm (hf.hyperbolicTranslate t) 3)
  have hq' (t : ℝ) : HasDerivAt q (3 * a t - 2 * q t ^ 2 - 1) t :=
    (hasDerivAt_translate_coeffs hf t).1
  have ha' (t : ℝ) : HasDerivAt a (4 * b t - 2 * q t - 2 * q t * a t) t :=
    (hasDerivAt_translate_coeffs hf t).2
  have hV' (t : ℝ) : HasDerivAt V (2 * q t * V t) t := by
    have h := hasDerivAt_radialTrace_iteratedDeriv hf.holomorphic 1 t
    rw [iteratedDeriv_one, (radialTrace_iteratedDeriv_of_translate hf t).1] at h
    simpa only [V, F, q, mul_comm (deriv (radialTrace f) t)] using h
  have hVne (t : ℝ) : V t ≠ 0 := radialTrace_deriv_ne_zero hf t
  have hU' (t : ℝ) : HasDerivAt U (2 * (q t).re * U t) t :=
    hasDerivAt_velocity_norm (hV' t) (hVne t)
  have hP' (t : ℝ) : HasDerivAt P (2 * Complex.I * ((q t).im : ℂ) * P t) t :=
    hasDerivAt_velocity_phase (hV' t) (hVne t)
  have hP₁ (t : ℝ) : ‖P t‖ = 1 := by
    rw [show P t = V t / (‖V t‖ : ℂ) from rfl, norm_div, Complex.norm_of_nonneg (norm_nonneg _)]
    exact div_self (norm_pos_iff.mpr (hVne t)).ne'
  have hW (t : ℝ) : 2 * d t ≤ W t ∧ W t ≤ 6 * d t := amplitude_deficit_bounds (him t)
  have hd' (t : ℝ) : HasDerivAt d (-(4 * b t - 2 * q t - 2 * q t * a t).re) t := by
    simpa only [d, Function.comp_apply, Complex.reCLM_apply, zero_sub] using!
      (hasDerivAt_const t (3 : ℝ)).fun_sub (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (ha' t))
  have hWc : Continuous W := by
    have hd : Continuous d := continuous_iff_continuousAt.mpr fun t ↦ (hd' t).continuousAt
    have hqc : Continuous q := continuous_iff_continuousAt.mpr fun t ↦ (hq' t).continuousAt
    exact (hd.const_mul 6).sub (((Complex.continuous_im.comp hqc).pow 2).const_mul 4)
  have hUc : Continuous U := continuous_iff_continuousAt.mpr fun t ↦ (hU' t).continuousAt
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun t ↦ (hP' t).continuousAt
  have hU₀ : U 0 = 1 := by
    simp [U, V, F, (hasDerivAt_radialTrace hf 0).deriv, hf.deriv_zero]
  have hUd (t : ℝ) : HasDerivAt (deriv U) ((16 - W t) * U t) t :=
    hasDerivAt_deriv_velocity_norm hV' hVne (hq' t)
  let Q (t : ℝ) := W t * U t
  let Y (t : ℝ) := U t * (‖P t - γ‖ ^ 2 / 2)
  have hQc : Continuous Q := hWc.mul hUc
  have hYc : Continuous Y := hUc.mul (((hPc.sub continuous_const).norm.pow 2).div_const _)
  have hdRate (t : ℝ) : |-(4 * b t - 2 * q t - 2 * q t * a t).re| ≤ (4 * C + 11) * d t := by
    have h := real_third_deficit_derivative_abs_le (hq t) (ha t) (him t)
      (hLow (hf.hyperbolicTranslate t))
    simpa only [abs_neg] using h
  have hURate (t : ℝ) : |2 * (q t).re * U t| ≤ 4 * U t := by
    have h := (Complex.abs_re_le_norm (q t)).trans (hq t)
    rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg (V t)), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_right (by linarith only [h]) (norm_nonneg _)
  have hSpeed (t : ℝ) : ‖2 * Complex.I * ((q t).im : ℂ) * P t‖ ≤ 2 * Real.sqrt (d t) := by
    simp only [norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one, Complex.norm_real,
      Real.norm_eq_abs, hP₁ t]
    have hIm : |(q t).im| ≤ Real.sqrt (d t) :=
      Real.le_sqrt_of_sq_le (by rw [sq_abs]; exact him t)
    exact mul_le_mul_of_nonneg_left hIm (by norm_num)
  have hRate := hBound γ hWc hd' hU' hP' (fun t ↦ (sq_nonneg _).trans (him t))
    (fun _ ↦ norm_nonneg _) hW hdRate hURate hSpeed
  have hX : 2 ≤ Real.artanh r := by
    have h := Real.artanh_le_artanh (Real.neg_one_lt_tanh (2 : ℝ)) (hrs.trans_lt hs) hr₀
    simpa only [Real.artanh_tanh] using h
  have hX' := Real.artanh_le_artanh (show -1 < r by linarith) hs hrs
  have hEeq (t : ℝ) (ht : 0 ≤ t) :
      diameterEnergy Q Y t = Real.sinh (4 * t) / 2 - (conj γ * (F t - F (-t))).re := by
    apply diameterEnergy_eq_trace_deficit (γ := γ) ?_ hPc hP₁ hγ
      (fun t ↦ (hU' t).differentiableAt.hasDerivAt) ?_ hU₀ hQc ht
    · intro t
      have he : (U t : ℂ) * P t = V t := by
        exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr (hVne t)).ne')
      rw [he]
      exact (hasDerivAt_radialTrace hf t).differentiableAt.hasDerivAt
    · intro t
      convert hUd t using 1
      dsimp only [Q]
      ring
  have hrI : r ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hrs.trans_lt hs⟩
  have hsI : s ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hs⟩
  have hQ₀ (t : ℝ) : 0 ≤ Q t := by
    have hd₀ := (sq_nonneg _).trans (him t)
    have hW₀ := (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd₀).trans (hW t).1
    exact mul_nonneg hW₀ (norm_nonneg _)
  have h := normalized_diameterEnergy_le hQc hYc
    hQ₀
    (fun _ ↦ by dsimp only [Y, U]; positivity) hE.le hr.le hrs hs hX hRate
  have hXR : 0 < Real.artanh r := by linarith only [hX]
  have hXS : 0 < Real.artanh s := hXR.trans_le hX'
  rw [hEeq (Real.artanh r) hXR.le, hEeq (Real.artanh s) hXS.le] at h
  simpa only [F, diameter_trace_div_normalization γ hrI hXR,
    diameter_trace_div_normalization γ hsI hXS] using h

end Zalcman
