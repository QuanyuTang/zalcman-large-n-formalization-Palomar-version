/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The integral of an amplitude with a forcing term

Two exponential integrating factors give the exact hyperbolic kernel in the
diameter calculation. The proof uses only one-dimensional interval integrals.
-/

@[expose] public section

noncomputable section

namespace Zalcman

open MeasureTheory

/-- The convolution kernel for the integral of the amplitude. -/
def amplitudeKernel (v : ℝ) : ℝ := (Real.cosh (4 * v) - 1) / 16

/-- The first derivative of the integrated amplitude kernel. -/
def amplitudeKernelDeriv (v : ℝ) : ℝ := Real.sinh (4 * v) / 4

theorem hasDerivAt_amplitudeKernel (v : ℝ) : HasDerivAt amplitudeKernel (amplitudeKernelDeriv v) v := by
  have h := ((Real.hasDerivAt_cosh (4 * v)).scomp v ((hasDerivAt_id v).const_mul (4 : ℝ))).sub_const 1
  convert h.div_const (16 : ℝ) using 1 <;> try rfl
  simp only [amplitudeKernelDeriv, smul_eq_mul, mul_one]
  ring

theorem amplitudeKernel_nonneg (v : ℝ) : 0 ≤ amplitudeKernel v := by
  exact div_nonneg (sub_nonneg.mpr (Real.one_le_cosh (4 * v))) (by norm_num)

/-- Away from zero the derivative kernel is bounded by a fixed multiple of the integral kernel. -/
theorem amplitudeKernelDeriv_le_mul (v : ℝ) (hv : 1 / 2 ≤ v) :
    amplitudeKernelDeriv v ≤ (4 * ((Real.exp 2 + 1) / (Real.exp 2 - 1))) * amplitudeKernel v := by
  let E := Real.exp (4 * v)
  let A := Real.exp 2
  have hA : 1 < A := Real.one_lt_exp_iff.mpr (by norm_num)
  have hAv : A ≤ E := Real.exp_le_exp.mpr (by linarith)
  have hE : 1 < E := hA.trans_le hAv
  have hEq : amplitudeKernelDeriv v = (4 * ((E + 1) / (E - 1))) * amplitudeKernel v := by
    rw [amplitudeKernelDeriv, amplitudeKernel, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
    change (E - E⁻¹) / 2 / 4 = 4 * ((E + 1) / (E - 1)) * (((E + E⁻¹) / 2 - 1) / 16)
    have hne : E ≠ 0 := ne_of_gt (zero_lt_one.trans hE)
    have hden : E - 1 ≠ 0 := sub_ne_zero.mpr hE.ne'
    field_simp [hne, hden] <;> ring
  have hRatio : (E + 1) / (E - 1) ≤ (A + 1) / (A - 1) := by
    apply (div_le_div_iff₀ (sub_pos.mpr hE) (sub_pos.mpr hA)).mpr
    nlinarith only [hAv]
  rw [hEq]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRatio (by norm_num)) (amplitudeKernel_nonneg v)

/-- The integral of a solution to `U'' = 16 U − Q` separates into initial data and forcing. -/
theorem intervalIntegral_amplitude_eq {U V Q : ℝ → ℝ} (hU : ∀ x, HasDerivAt U (V x) x)
    (hV : ∀ x, HasDerivAt V (16 * U x - Q x) x) (hQ : Continuous Q) (x : ℝ) :
    (∫ u in (0 : ℝ)..x, U u) =
      U 0 * Real.sinh (4 * x) / 4 + V 0 * amplitudeKernel x -
        ∫ u in (0 : ℝ)..x, amplitudeKernel (x - u) * Q u := by
  let E (y : ℝ) := Real.exp (4 * y)
  let F (y : ℝ) := Real.exp (-4 * y)
  have hE : Continuous E := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hF : Continuous F := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hUc : Continuous U := continuous_iff_continuousAt.mpr (fun y => (hU y).continuousAt)
  have hP (y : ℝ) : HasDerivAt (fun t => F t * (V t + 4 * U t)) (-(F y * Q y)) y := by
    have he := ((hasDerivAt_id y).const_mul (-4 : ℝ)).exp
    convert he.fun_mul ((hV y).fun_add ((hU y).const_mul (4 : ℝ))) using 1 <;> try rfl
    simp only [F, id, mul_one]
    ring
  have hN (y : ℝ) : HasDerivAt (fun t => E t * (V t - 4 * U t)) (-(E y * Q y)) y := by
    have he := ((hasDerivAt_id y).const_mul (4 : ℝ)).exp
    convert he.fun_mul ((hV y).fun_sub ((hU y).const_mul (4 : ℝ))) using 1 <;> try rfl
    simp only [E, id, mul_one]
    ring
  have hP₁ : E x * (∫ u in (0 : ℝ)..x, F u * Q u) =
      E x * (V 0 + 4 * U 0) - (V x + 4 * U x) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hP y)
      ((hF.mul hQ).neg.intervalIntegrable 0 x)
    rw [intervalIntegral.integral_neg] at h
    have hF₀ : F 0 = 1 := by simp [F]
    have hCancel : E x * F x = 1 := by
      rw [show E x * F x = Real.exp (4 * x) * Real.exp (-4 * x) by rfl, ← Real.exp_add,
        show 4 * x + -4 * x = 0 by ring, Real.exp_zero]
    rw [hF₀, one_mul] at h
    have heq : (∫ u in (0 : ℝ)..x, F u * Q u) = V 0 + 4 * U 0 - F x * (V x + 4 * U x) := by
      linarith only [h]
    rw [heq, mul_sub, ← mul_assoc, hCancel, one_mul]
  have hN₁ : F x * (∫ u in (0 : ℝ)..x, E u * Q u) =
      F x * (V 0 - 4 * U 0) - (V x - 4 * U x) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hN y)
      ((hE.mul hQ).neg.intervalIntegrable 0 x)
    rw [intervalIntegral.integral_neg] at h
    have hE₀ : E 0 = 1 := by simp [E]
    have hCancel : F x * E x = 1 := by
      rw [show F x * E x = Real.exp (-4 * x) * Real.exp (4 * x) by rfl, ← Real.exp_add,
        show -4 * x + 4 * x = 0 by ring, Real.exp_zero]
    rw [hE₀, one_mul] at h
    have heq : (∫ u in (0 : ℝ)..x, E u * Q u) = V 0 - 4 * U 0 - E x * (V x - 4 * U x) := by
      linarith only [h]
    rw [heq, mul_sub, ← mul_assoc, hCancel, one_mul]
  have hU₁ : (∫ u in (0 : ℝ)..x, U u) = (V x - V 0 + ∫ u in (0 : ℝ)..x, Q u) / 16 := by
    have h16 : Continuous (fun u => 16 * U u) := continuous_const.mul hUc
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hV y)
      ((h16.sub hQ).intervalIntegrable 0 x)
    rw [intervalIntegral.integral_sub (h16.intervalIntegrable 0 x) (hQ.intervalIntegrable 0 x),
      intervalIntegral.integral_const_mul] at h
    linarith only [h]
  have hK : (∫ u in (0 : ℝ)..x, amplitudeKernel (x - u) * Q u) =
      (E x * (∫ u in (0 : ℝ)..x, F u * Q u) + F x * (∫ u in (0 : ℝ)..x, E u * Q u) -
        2 * (∫ u in (0 : ℝ)..x, Q u)) / 32 := by
    have hl (y : ℝ) : amplitudeKernel (x - y) * Q y =
        (E x * (F y * Q y) + F x * (E y * Q y) - 2 * Q y) / 32 := by
      rw [amplitudeKernel, Real.cosh_eq, show 4 * (x - y) = 4 * x + -4 * y by ring,
        show -(4 * x + -4 * y) = -4 * x + 4 * y by ring, Real.exp_add, Real.exp_add]
      dsimp only [E, F]
      ring
    simp_rw [hl]
    have ha : IntervalIntegrable (fun y => E x * (F y * Q y)) volume 0 x :=
      ((hF.mul hQ).intervalIntegrable 0 x).const_mul _
    have hb : IntervalIntegrable (fun y => F x * (E y * Q y)) volume 0 x :=
      ((hE.mul hQ).intervalIntegrable 0 x).const_mul _
    have hc : IntervalIntegrable (fun y => 2 * Q y) volume 0 x :=
      (hQ.intervalIntegrable 0 x).const_mul _
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (ha.add hb) hc,
      intervalIntegral.integral_add ha hb]
    simp only [intervalIntegral.integral_const_mul]
  rw [hU₁, hK, hP₁, hN₁, amplitudeKernel, Real.cosh_eq, Real.sinh_eq]
  dsimp only [E, F]
  ring

/-- The symmetric amplitude integral cancels the initial derivative term. -/
theorem intervalIntegral_amplitude_symmetric_eq {U V Q : ℝ → ℝ}
    (hU : ∀ x, HasDerivAt U (V x) x) (hV : ∀ x, HasDerivAt V (16 * U x - Q x) x)
    (hQ : Continuous Q) {X : ℝ} (hX : 0 ≤ X) :
    (∫ u in -X..X, U u) =
      U 0 * Real.sinh (4 * X) / 2 - ∫ u in -X..X, amplitudeKernel (X - |u|) * Q u := by
  have hUc : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hU x).continuousAt)
  have hKc : Continuous amplitudeKernel := by
    unfold amplitudeKernel
    exact ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).sub continuous_const).div_const _
  have hKernel : Continuous (fun u => amplitudeKernel (X - |u|) * Q u) :=
    (hKc.comp (continuous_const.sub continuous_abs)).mul hQ
  have hKplus : (∫ u in (0 : ℝ)..X, amplitudeKernel (X - u) * Q u) =
      ∫ u in (0 : ℝ)..X, amplitudeKernel (X - |u|) * Q u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hX] at hu
    change amplitudeKernel (X - u) * Q u = amplitudeKernel (X - |u|) * Q u
    rw [abs_of_nonneg hu.1]
  have hKminus : (∫ u in (0 : ℝ)..-X, amplitudeKernel (-X - u) * Q u) =
      -(∫ u in -X..(0 : ℝ), amplitudeKernel (X - |u|) * Q u) := by
    rw [intervalIntegral.integral_symm (a := -X) (b := (0 : ℝ))]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (neg_nonpos.mpr hX)] at hu
    change amplitudeKernel (-X - u) * Q u = amplitudeKernel (X - |u|) * Q u
    rw [abs_of_nonpos hu.2, sub_neg_eq_add]
    unfold amplitudeKernel
    rw [show 4 * (-X - u) = -(4 * (X + u)) by ring, Real.cosh_neg]
  have hUjoin := intervalIntegral.integral_add_adjacent_intervals
    (hUc.intervalIntegrable (μ := volume) (-X) 0) (hUc.intervalIntegrable (μ := volume) 0 X)
  have hKjoin := intervalIntegral.integral_add_adjacent_intervals
    (hKernel.intervalIntegrable (μ := volume) (-X) 0) (hKernel.intervalIntegrable (μ := volume) 0 X)
  have hPlus := intervalIntegral_amplitude_eq hU hV hQ X
  have hMinus := intervalIntegral_amplitude_eq hU hV hQ (-X)
  rw [hKplus] at hPlus
  rw [hKminus, mul_neg, Real.sinh_neg] at hMinus
  have hKeven : amplitudeKernel (-X) = amplitudeKernel X := by
    unfold amplitudeKernel
    rw [mul_neg, Real.cosh_neg]
  rw [hKeven, intervalIntegral.integral_symm (a := -X) (b := (0 : ℝ))] at hMinus
  linarith only [hUjoin, hKjoin, hPlus, hMinus]

end Zalcman
