/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CoefficientContinuity
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Tactic.FieldSimp

/-!
# Absolute continuity of logarithmic coefficients in time

The square-root and logarithmic coefficients are obtained from the Taylor coefficients
by finite recursions, which preserve absolute continuity on each compact time interval.
-/

public section

namespace Zalcman

open Finset Set

private theorem ac_const {a b : ℝ} (z : ℂ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => z) a b :=
  (LipschitzOnWith.of_dist_le_mul (K := 0) (s := uIcc a b)
    (f := fun _ : ℝ => z) (by simp)).absolutelyContinuousOnInterval

private theorem ac_sum {ι : Type*} {a b : ℝ} {s : Finset ι} {f : ι → ℝ → ℂ}
    (h : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => ∑ i ∈ s, f i t) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty] using (ac_const (a := a) (b := b) 0)
  | insert i s hi ih =>
    simp only [sum_insert hi]
    exact (h i (mem_insert_self i s)).fun_add (ih (fun j hj => h j (mem_insert_of_mem hj)))

private theorem ac_mul {a b : ℝ} {f g : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => f t * g t) a b := by
  simpa only [smul_eq_mul] using hf.fun_smul hg

private theorem ac_mul_const {a b : ℝ} {f : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f a b) (c : ℂ) :
    AbsolutelyContinuousOnInterval (fun t => c * f t) a b := by
  simpa only [smul_eq_mul] using hf.const_smul c

private theorem ac_div_const {a b : ℝ} {f : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f a b) (c : ℂ) :
    AbsolutelyContinuousOnInterval (fun t => f t / c) a b := by
  simpa only [div_eq_mul_inv, mul_comm] using ac_mul_const hf c⁻¹

variable {F : ℝ → ℂ → ℂ} {a b : ℝ} (hF : ∀ t, NormalizedUnivalent (F t))
variable (hCoeff : ∀ n, AbsolutelyContinuousOnInterval (fun t => coeff (F t) n) a b)

include hCoeff

/-- Each square-root coefficient is absolutely continuous when the Taylor coefficients are. -/
theorem absolutelyContinuousOnInterval_rootCoeff (n : ℕ) :
    AbsolutelyContinuousOnInterval (fun t => rootCoeff (hF t) n) a b := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [rootCoeff_zero] using (ac_const (a := a) (b := b) 1)
    | succ n =>
      simp only [rootCoeff_succ_recursion _ n]
      apply ac_div_const
      apply (hCoeff (n + 2)).fun_sub
      apply ac_sum
      intro i hi
      have hi' := mem_range.mp hi
      exact ac_mul (ih (i + 1) (by omega)) (ih (n - i) (by omega))

/-- The normalized logarithmic derivative coefficients inherit time absolute continuity. -/
theorem absolutelyContinuousOnInterval_logCoeff (n : ℕ) :
    AbsolutelyContinuousOnInterval (fun t => logCoeff (hF t) n) a b := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [logCoeff_zero] using (ac_const (a := a) (b := b) 0)
    | succ n =>
      simp only [logCoeff_succ_recursion _ n]
      apply (ac_mul_const (absolutelyContinuousOnInterval_rootCoeff hF hCoeff (n + 1)) _).fun_sub
      apply ac_sum
      intro i hi
      exact ac_mul (ih (n - i) (by omega)) (absolutelyContinuousOnInterval_rootCoeff hF hCoeff _)

/-- Each coefficient of the normalized half-logarithm is absolutely continuous in time. -/
theorem absolutelyContinuousOnInterval_halfLogCoeff (n : ℕ) :
    AbsolutelyContinuousOnInterval (fun t =>
      coeff (fun z => normalizedLogarithm (hF t) z / 2) (n + 1)) a b := by
  have h := ac_div_const (absolutelyContinuousOnInterval_logCoeff hF hCoeff (n + 1))
    ((n : ℂ) + 1)
  have heq (t : ℝ) : logCoeff (hF t) (n + 1) / ((n : ℂ) + 1) =
      coeff (fun z => normalizedLogarithm (hF t) z / 2) (n + 1) := by
    rw [logCoeff, Nat.cast_succ, mul_comm, mul_div_cancel_right₀ _]
    exact_mod_cast (Nat.succ_ne_zero n)
  simpa only [heq] using h

end Zalcman
