/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Orthogonality of shifted Legendre polynomials

Rodrigues' formula and repeated integration by parts give orthogonality to
every real polynomial of strictly lower degree. The endpoint conditions follow
from the zero derivatives of the central Bernstein polynomial.
-/

public section

namespace Zalcman

open Polynomial
open scoped Polynomial

private lemma integral_iterate_derivative_mul (P Q : ℝ[X]) (n : ℕ)
    (hP : ∀ k < n, (derivative^[k] P).eval 0 = 0 ∧ (derivative^[k] P).eval 1 = 0) :
    (∫ x in (0 : ℝ)..1, (derivative^[n] P).eval x * Q.eval x) =
      (-1 : ℝ) ^ n * ∫ x in (0 : ℝ)..1, P.eval x * (derivative^[n] Q).eval x := by
  induction n generalizing Q with
  | zero => simp
  | succ n ih =>
    let R := derivative^[n] P
    have hR0 := (hP n (Nat.lt_succ_self _)).1
    have hR1 := (hP n (Nat.lt_succ_self _)).2
    change R.eval 0 = 0 at hR0
    change R.eval 1 = 0 at hR1
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a := 0) (b := 1) Q.continuous.continuousOn R.continuous.continuousOn
      (fun x _ ↦ Q.hasDerivAt x) (fun x _ ↦ R.hasDerivAt x)
      (Q.derivative.continuous.intervalIntegrable 0 1) (R.derivative.continuous.intervalIntegrable 0 1)
    rw [hR0, hR1, mul_zero, mul_zero, sub_self, zero_sub] at h
    have hleft : derivative^[n + 1] P = R.derivative := Function.iterate_succ_apply' _ _ _
    have hright : derivative^[n + 1] Q = derivative^[n] Q.derivative :=
      Function.iterate_succ_apply _ _ _
    rw [hleft, hright, pow_succ]
    calc
      _ = -(∫ x in (0 : ℝ)..1, R.eval x * Q.derivative.eval x) := by
        simpa only [mul_comm] using h
      _ = _ := by
        rw [show (∫ x in (0 : ℝ)..1, R.eval x * Q.derivative.eval x) =
          (-1 : ℝ) ^ n * ∫ x in (0 : ℝ)..1, P.eval x * (derivative^[n] Q.derivative).eval x
          from ih Q.derivative (fun k hk ↦ hP k (hk.trans n.lt_succ_self))]
        ring

private lemma central_vanishes (n : ℕ) {k : ℕ} (hk : k < n) :
    (derivative^[k] ((X : ℝ[X]) ^ n * (1 - X) ^ n)).eval 0 = 0 ∧
    (derivative^[k] ((X : ℝ[X]) ^ n * (1 - X) ^ n)).eval 1 = 0 := by
  have hn : 2 * n - n = n := by omega
  have hB : bernsteinPolynomial ℝ (2 * n) n =
      ((Nat.choose (2 * n) n : ℕ) : ℝ[X]) * ((X : ℝ[X]) ^ n * (1 - X) ^ n) := by
    rw [bernsteinPolynomial, hn, mul_assoc]
  have hc : (Nat.choose (2 * n) n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 2 * n)).ne'
  have h0 := bernsteinPolynomial.iterate_derivative_at_0_eq_zero_of_lt ℝ (2 * n) hk
  have h1 := bernsteinPolynomial.iterate_derivative_at_1_eq_zero_of_lt ℝ (2 * n)
    (show k < 2 * n - n by simpa only [hn] using hk)
  constructor
  · simpa only [hB, iterate_derivative_natCast_mul, eval_mul, eval_natCast,
      mul_eq_zero, hc, false_or] using h0
  · simpa only [hB, iterate_derivative_natCast_mul, eval_mul, eval_natCast,
      mul_eq_zero, hc, false_or] using h1

/-- A shifted Legendre polynomial of degree `n` is orthogonal on `[0,1]` to
every polynomial of degree strictly below `n`. -/
theorem integral_shiftedLegendre_mul_eq_zero {Q : ℝ[X]} {n : ℕ}
    (hQ : Q.degree < n) :
    (∫ x in (0 : ℝ)..1, ((shiftedLegendre n).map (Int.castRingHom ℝ)).eval x * Q.eval x) = 0 := by
  have hd := congrArg (Polynomial.map (Int.castRingHom ℝ)) (factorial_mul_shiftedLegendre_eq n)
  have hD : ((n.factorial : ℕ) : ℝ[X]) * (shiftedLegendre n).map (Int.castRingHom ℝ) =
      derivative^[n] ((X : ℝ[X]) ^ n * (1 - X) ^ n) := by
    simpa only [Polynomial.map_mul, Polynomial.map_natCast, ← iterate_derivative_map,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub, Polynomial.map_one] using hd
  have h := integral_iterate_derivative_mul ((X : ℝ[X]) ^ n * (1 - X) ^ n) Q n
    (fun _ ↦ central_vanishes n)
  rw [← hD, iterate_derivative_eq_zero_of_degree_lt hQ] at h
  simp only [eval_mul, eval_natCast, eval_zero, mul_zero, intervalIntegral.integral_zero] at h
  simp_rw [mul_assoc] at h
  rw [intervalIntegral.integral_const_mul, mul_eq_zero] at h
  exact h.resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

private lemma integral_nat_beta (m n : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ n) =
      (m.factorial : ℝ) * n.factorial / (m + n + 1).factorial := by
  have hpos : 0 < ((m : ℂ) + 1).re := by simp; positivity
  have hL : Complex.betaIntegral ((m : ℂ) + 1) ((n : ℂ) + 1) =
      Complex.ofReal (∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ n) := by
    rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [add_sub_cancel_right, Complex.cpow_natCast, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_sub, Complex.ofReal_one]
  have hprod : (m.factorial : ℂ) * (∏ j ∈ Finset.range (n + 1), ((m : ℂ) + 1 + j)) =
      ((m + n + 1).factorial : ℂ) := by
    exact_mod_cast (show m.factorial * (∏ j ∈ Finset.range (n + 1), (m + 1 + j)) =
      (m + n + 1).factorial by
        rw [← Nat.ascFactorial_eq_prod_range, Nat.factorial_mul_ascFactorial, Nat.add_assoc])
  have hmf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hc : Complex.ofReal (∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ n) =
      (m.factorial : ℂ) * n.factorial / (m + n + 1).factorial := calc
    _ = (n.factorial : ℂ) / (∏ j ∈ Finset.range (n + 1), ((m : ℂ) + 1 + j)) :=
      hL.symm.trans (Complex.betaIntegral_eval_nat_add_one_right hpos n)
    _ = _ := by rw [← mul_div_mul_left _ _ hmf, hprod]
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast] using hc

private lemma derivative_iterate_shiftedLegendre (n : ℕ) :
    derivative^[n] ((shiftedLegendre n).map (Int.castRingHom ℝ)) =
      C (((-1 : ℝ) ^ n * (2 * n).choose n) * n.factorial) := by
  let L := (shiftedLegendre n).map (Int.castRingHom ℝ)
  let a : ℝ := (-1 : ℝ) ^ n * (2 * n).choose n
  have hdeg : (L - C a * X ^ n).degree < (n : WithBot ℕ) := by
    rw [degree_lt_iff_coeff_zero]
    intro k hk
    rw [coeff_sub, coeff_C_mul_X_pow]
    dsimp only [L]
    rw [coeff_map, coeff_shiftedLegendre]
    by_cases he : n = k
    · subst k
      simp [a, two_mul]
    · have hlt : n < k := lt_of_le_of_ne hk he
      simp [Ne.symm he, Nat.choose_eq_zero_of_lt hlt]
  have hz := iterate_derivative_eq_zero_of_degree_lt hdeg
  rw [iterate_derivative_sub, sub_eq_zero] at hz
  change derivative^[n] L = C (a * n.factorial)
  rw [hz, iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul]
  simp [Nat.descFactorial_self, C_mul]

/-- The squared norm of the shifted Legendre polynomial on [0,1]. -/
theorem integral_shiftedLegendre_sq (n : ℕ) :
    (∫ x in (0 : ℝ)..1, (((shiftedLegendre n).map (Int.castRingHom ℝ)).eval x) ^ 2) =
      1 / (2 * (n : ℝ) + 1) := by
  let L := (shiftedLegendre n).map (Int.castRingHom ℝ)
  let a : ℝ := (-1 : ℝ) ^ n * (2 * n).choose n
  have hD : derivative^[n] L = C (a * n.factorial) := derivative_iterate_shiftedLegendre n
  have hR : ((n.factorial : ℕ) : ℝ[X]) * L =
      derivative^[n] ((X : ℝ[X]) ^ n * (1 - X) ^ n) := by
    have hd := congrArg (Polynomial.map (Int.castRingHom ℝ)) (factorial_mul_shiftedLegendre_eq n)
    simpa only [L, Polynomial.map_mul, Polynomial.map_natCast, ← iterate_derivative_map,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub, Polynomial.map_one] using hd
  have h := integral_iterate_derivative_mul ((X : ℝ[X]) ^ n * (1 - X) ^ n) L n
    (fun _ ↦ central_vanishes n)
  rw [← hR, hD] at h
  simp only [eval_mul, eval_natCast, eval_C, eval_pow, eval_X, eval_sub, eval_one] at h
  have hprod (x : ℝ) : (n.factorial : ℝ) * L.eval x * L.eval x =
      (n.factorial : ℝ) * (L.eval x) ^ 2 := by ring
  simp only [hprod] at h
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const, integral_nat_beta] at h
  have hs : (-1 : ℝ) ^ n * a = ((2 * n).choose n : ℝ) := by
    dsimp only [a]
    rw [← mul_assoc, ← mul_pow]
    norm_num
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hchoose : ((2 * n).choose n : ℝ) * (n.factorial : ℝ) * n.factorial =
      ((2 * n).factorial : ℝ) := by
    exact_mod_cast (show (2 * n).choose n * n.factorial * n.factorial = (2 * n).factorial by
      simpa only [show 2 * n - n = n by omega] using
        (Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ 2 * n)))
  change (∫ x in (0 : ℝ)..1, (L.eval x) ^ 2) = _
  apply mul_left_cancel₀ hf
  calc
    _ = (-1 : ℝ) ^ n * ((n.factorial : ℝ) * n.factorial / (n + n + 1).factorial *
        (a * n.factorial)) := h
    _ = (n.factorial : ℝ) * (((-1 : ℝ) ^ n * a) *
        ((n.factorial : ℝ) * n.factorial) / (n + n + 1).factorial) := by ring
    _ = _ := by
      rw [hs, ← mul_assoc _ (n.factorial : ℝ) (n.factorial : ℝ), hchoose,
        show n + n + 1 = 2 * n + 1 by omega, Nat.factorial_succ]
      push_cast
      have hn : ((2 * n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hn' : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      field_simp

end Zalcman
