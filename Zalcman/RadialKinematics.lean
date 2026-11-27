/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.RadialEstimates
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Amplitude and unit phase of a complex radial velocity

The real and imaginary parts of the logarithmic velocity control the amplitude and
the unit phase. A unit-phase curve suffices for comparisons of endpoint phases.
-/

public section

namespace Zalcman

open scoped ComplexConjugate

private theorem velocity_norm_sq_derivative {P : ℝ → ℂ} {x : ℝ} {v : ℂ}
    (hP : HasDerivAt P v x) :
    HasDerivAt (fun t => ‖P t‖ ^ 2) (2 * (v * conj (P x)).re) x := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hP
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hP
  convert (hr.fun_mul hr).fun_add (hi.fun_mul hi) using 1
  · funext t
    rw [Complex.sq_norm, Complex.normSq_apply]
    rfl
  · simp only [Function.comp_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.reCLM_apply, Complex.imCLM_apply]
    ring

/-- The magnitude of a nonzero complex velocity has the expected real logarithmic derivative. -/
theorem hasDerivAt_velocity_norm {P : ℝ → ℂ} {x : ℝ} {q : ℂ}
    (hP : HasDerivAt P (2 * q * P x) x) (hne : P x ≠ 0) :
    HasDerivAt (fun t => ‖P t‖) (2 * q.re * ‖P x‖) x := by
  have hp : 0 < ‖P x‖ := norm_pos_iff.mpr hne
  have h := (velocity_norm_sq_derivative hP).sqrt (pow_ne_zero 2 hp.ne')
  simp only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
  have hRe : (2 * q * P x * conj (P x)).re = 2 * q.re * ‖P x‖ ^ 2 := by
    rw [mul_assoc (2 * q), Complex.mul_conj, Complex.normSq_eq_norm_sq,
      mul_comm (2 * q), Complex.re_ofReal_mul]
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    ring
  convert h using 1
  rw [hRe]
  field_simp
  <;> ring

/-- The phase curve of a nonvanishing velocity is driven by its imaginary logarithmic derivative. -/
theorem hasDerivAt_velocity_phase {P : ℝ → ℂ} {x : ℝ} {q : ℂ}
    (hP : HasDerivAt P (2 * q * P x) x) (hne : P x ≠ 0) :
    HasDerivAt (fun t => P t / (‖P t‖ : ℂ))
      (2 * Complex.I * (q.im : ℂ) * (P x / (‖P x‖ : ℂ))) x := by
  have hnorm := hasDerivAt_velocity_norm hP hne
  have hcast : HasDerivAt (fun t ↦ (‖P t‖ : ℂ)) ((2 * q.re * ‖P x‖ : ℝ) : ℂ) x := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using!
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hnorm
  have hp : ((‖P x‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hne
  have hq : q - (q.re : ℂ) = Complex.I * (q.im : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  convert hP.fun_div hcast hp using 1
  rw [show 2 * Complex.I * (q.im : ℂ) = 2 * (q - (q.re : ℂ)) by rw [hq]; ring]
  push_cast
  field_simp [hp]

/-- The second amplitude derivative in the hyperbolic coordinate. -/
theorem hasDerivAt_deriv_velocity_norm {P Q : ℝ → ℂ} {x : ℝ} {a : ℂ}
    (hP : ∀ t, HasDerivAt P (2 * Q t * P t) t) (hne : ∀ t, P t ≠ 0)
    (hQ : HasDerivAt Q (3 * a - 2 * Q x ^ 2 - 1) x) :
    HasDerivAt (deriv (fun t => ‖P t‖))
      ((16 - (6 * (3 - a.re) - 4 * (Q x).im ^ 2)) * ‖P x‖) x := by
  have hnorm (t : ℝ) := hasDerivAt_velocity_norm (hP t) (hne t)
  have heq : deriv (fun t => ‖P t‖) = fun t => 2 * (Q t).re * ‖P t‖ :=
    funext fun t => (hnorm t).deriv
  have hr : HasDerivAt (fun t ↦ (Q t).re) (3 * a - 2 * Q x ^ 2 - 1).re x := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using!
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hQ
  rw [heq]
  convert (hr.const_mul 2).fun_mul (hnorm x) using 1
  simp only [pow_two, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re,
    zero_mul, sub_zero]
  ring

end Zalcman
