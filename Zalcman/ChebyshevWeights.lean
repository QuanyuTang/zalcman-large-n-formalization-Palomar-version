/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.Ring

/-!
# The weight differential equation in cleared polynomial form

The variables q and z represent the radial time variable and the Laurent
variable. Clearing the Laurent denominator gives a polynomial recurrence.
The differential equation follows by the product rule and this recurrence.
-/

@[expose] public section

noncomputable section

namespace Zalcman

open MvPolynomial

/-- Polynomials in the radial time and Laurent variables. -/
abbrev WeightPolynomial := MvPolynomial Bool ℤ

/-- The time variable, to be evaluated at exp(−u). -/
def weightTime : WeightPolynomial := X false

/-- The Laurent variable, with nonnegative powers after clearing. -/
def weightVariable : WeightPolynomial := X true

/-- Twice the Chebyshev argument after multiplication by the Laurent variable. -/
def twiceRadialArgument : WeightPolynomial :=
  (1 - weightTime) * weightVariable + (1 - weightTime) * weightVariable +
    weightTime * (weightVariable ^ 2 + 1)

/-- The cleared form of the Chebyshev polynomial defining the Laurent weights. -/
def clearedChebyshevWeight : ℕ → WeightPolynomial
  | 0 => 1
  | 1 => twiceRadialArgument
  | n + 2 => twiceRadialArgument * clearedChebyshevWeight (n + 1) -
    weightVariable ^ 2 * clearedChebyshevWeight n

/-- The polynomial differential operator for the radial weight identity. -/
def weightFlow (P : WeightPolynomial) : WeightPolynomial :=
  -((1 + weightVariable) * weightTime) * pderiv false P -
    ((1 - weightVariable) * weightVariable) * pderiv true P

private lemma weightFlow_mul (P Q : WeightPolynomial) :
    weightFlow (P * Q) = weightFlow P * Q + P * weightFlow Q := by
  simp only [weightFlow, pderiv_mul]
  ring

private lemma weightFlow_add (P Q : WeightPolynomial) :
    weightFlow (P + Q) = weightFlow P + weightFlow Q := by
  simp only [weightFlow, map_add]
  ring

private lemma weightFlow_sub (P Q : WeightPolynomial) :
    weightFlow (P - Q) = weightFlow P - weightFlow Q := by
  simp only [weightFlow, map_sub]
  ring

private lemma weightFlow_time :
    weightFlow weightTime = -((1 + weightVariable) * weightTime) := by
  simp [weightFlow, weightTime, weightVariable]

private lemma weightFlow_variable :
    weightFlow weightVariable = -((1 - weightVariable) * weightVariable) := by
  simp [weightFlow, weightTime, weightVariable]

private lemma weightFlow_character :
    weightFlow twiceRadialArgument = -(1 - weightVariable) * twiceRadialArgument := by
  simp only [twiceRadialArgument, weightFlow_add, weightFlow_sub, weightFlow_mul, pow_two,
    weightFlow_variable, weightFlow_time, show weightFlow 1 = 0 by simp [weightFlow]]
  ring

private lemma weightFlow_variable_sq :
    weightFlow (weightVariable ^ 2) = -2 * (1 - weightVariable) * weightVariable ^ 2 := by
  rw [pow_two, weightFlow_mul, weightFlow_variable]
  ring

/-- The cleared Chebyshev weight of degree n is an eigenfunction of the
radial differential operator with factor -n(1-z). -/
theorem weightFlow_clearedChebyshevWeight (n : ℕ) :
    weightFlow (clearedChebyshevWeight n) =
      -(n : WeightPolynomial) * (1 - weightVariable) * clearedChebyshevWeight n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [clearedChebyshevWeight, weightFlow]
  | one => simpa only [clearedChebyshevWeight, Nat.cast_one, neg_mul, one_mul] using
      weightFlow_character
  | more n ih ihs =>
    simp only [clearedChebyshevWeight, weightFlow_sub, weightFlow_mul, weightFlow_character,
      weightFlow_variable_sq, ih, ihs, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring

end Zalcman
