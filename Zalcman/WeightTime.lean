/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.WeightIntegration
import Zalcman.ChebyshevWeights
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Radial time weights

The index `k` denotes the positive Laurent coefficient with exponent `k + 1`.
The finite tail of these coefficients gives the potential weight.
-/

@[expose] public section

noncomputable section

namespace Zalcman

open Finset
open scoped BigOperators LaurentPolynomial

/-- The positive radial Laurent coefficient, shifted to a zero-based index. -/
def radialWeightLambda (M k : ℕ) (u : ℝ) : ℝ :=
  (chebyshevRadialLaurent M (Real.exp (-u))).coeff ((k + 1 : ℕ) : ℤ)

/-- The de Branges weight formed from the current Laurent coefficient and twice its tail. -/
def radialWeightTau (M k : ℕ) (u : ℝ) : ℝ :=
  radialWeightLambda M k u + 2 * ∑ i ∈ Ico (k + 1) M, radialWeightLambda M i u

theorem radialWeightLambda_eq_zero_of_le {M k : ℕ} (h : M ≤ k) (u : ℝ) :
    radialWeightLambda M k u = 0 := by
  rw [radialWeightLambda, chebyshevRadialLaurent_coeff_eq_legendre_sum]
  refine sum_eq_zero fun n hn ↦ ?_
  have hn' := mem_range.mp hn
  rw [diagonalLegendreLaurent_coeff_eq_zero_of_nat_lt (by omega : n < k + 1), mul_zero]

theorem radialWeightTau_eq_zero_of_le {M k : ℕ} (h : M ≤ k) (u : ℝ) :
    radialWeightTau M k u = 0 := by
  have h' : M ≤ k + 1 := by omega
  simp [radialWeightTau, radialWeightLambda_eq_zero_of_le h, Ico_eq_empty_of_le h']

theorem radialWeightTau_succ_sub (M k : ℕ) (u : ℝ) :
    radialWeightTau M k u - radialWeightTau M (k + 1) u =
      radialWeightLambda M k u + radialWeightLambda M (k + 1) u := by
  by_cases hk : k + 1 < M
  · unfold radialWeightTau
    rw [sum_eq_sum_Ico_succ_bot hk]
    ring
  · have hk' : M ≤ k + 1 := by omega
    simp [radialWeightTau, radialWeightLambda_eq_zero_of_le hk', Ico_eq_empty_of_le hk',
      Ico_eq_empty_of_le (show M ≤ k + 1 + 1 by omega)]

private def laurentAtUnitTime (M : ℕ) : ℝ[T;T⁻¹] :=
  ∑ i ∈ range (M + 1), LaurentPolynomial.T (2 * (i : ℤ) - (M : ℤ))

private lemma twice_radial_argument_one :
    (2 : ℝ[T;T⁻¹]) * (LaurentPolynomial.C ((1 : ℝ) - 1) +
      LaurentPolynomial.C ((1 : ℝ) / 2) * (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))) =
      LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) := by
  have htwo : (2 : ℝ[T;T⁻¹]) = LaurentPolynomial.C (2 : ℝ) :=
    (map_ofNat LaurentPolynomial.C 2).symm
  rw [sub_self, map_zero, zero_add, htwo, ← mul_assoc, ← map_mul]
  norm_num

private lemma chebyshevRadialLaurent_one_add_two (M : ℕ) :
    chebyshevRadialLaurent (M + 2) 1 = (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) *
      chebyshevRadialLaurent (M + 1) 1 - chebyshevRadialLaurent M 1 := by
  simp only [chebyshevRadialLaurent, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [Polynomial.Chebyshev.U_add_two, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_mul, Polynomial.eval₂_ofNat, Polynomial.eval₂_X, twice_radial_argument_one]

private lemma T_one_mul_laurentAtUnitTime (M : ℕ) :
    LaurentPolynomial.T 1 * laurentAtUnitTime (M + 1) =
      laurentAtUnitTime M + LaurentPolynomial.T ((M : ℤ) + 2) := by
  rw [laurentAtUnitTime, laurentAtUnitTime, mul_sum, sum_range_succ _ (M + 1)]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine sum_congr rfl fun i _ ↦ ?_
    rw [← LaurentPolynomial.T_add]
    congr 1
    push_cast
    ring
  · rw [← LaurentPolynomial.T_add]
    congr 1
    push_cast
    ring

private lemma laurentAtUnitTime_add_two (M : ℕ) :
    laurentAtUnitTime (M + 2) =
      LaurentPolynomial.T (-1) * laurentAtUnitTime (M + 1) + LaurentPolynomial.T ((M : ℤ) + 2) := by
  rw [laurentAtUnitTime, laurentAtUnitTime, mul_sum, sum_range_succ _ (M + 2)]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine sum_congr rfl fun i _ ↦ ?_
    rw [← LaurentPolynomial.T_add]
    congr 1
    push_cast
    ring
  · congr 1
    push_cast
    ring

private lemma chebyshevRadialLaurent_one_eq_laurentAtUnitTime (M : ℕ) :
    chebyshevRadialLaurent M 1 = laurentAtUnitTime M := by
  induction M using Nat.twoStepInduction with
  | zero => simp [chebyshevRadialLaurent, laurentAtUnitTime]
  | one =>
    simp only [chebyshevRadialLaurent, Nat.cast_one, Polynomial.Chebyshev.U_one,
      Polynomial.eval₂_mul, Polynomial.eval₂_ofNat, Polynomial.eval₂_X, twice_radial_argument_one]
    norm_num [laurentAtUnitTime, sum_range_succ, add_comm]
  | more M h h' =>
    rw [chebyshevRadialLaurent_one_add_two, h, h', laurentAtUnitTime_add_two, add_mul,
      T_one_mul_laurentAtUnitTime]
    ring

/-- At radial time zero, the coefficients are those of the finite alternating-exponent sum. -/
theorem chebyshevRadialLaurent_one (M : ℕ) :
    chebyshevRadialLaurent M 1 =
      ∑ i ∈ range (M + 1), LaurentPolynomial.T (2 * (i : ℤ) - (M : ℤ)) :=
  chebyshevRadialLaurent_one_eq_laurentAtUnitTime M

theorem radialWeightLambda_zero_add_succ {M k : ℕ} (h : k < M) :
    radialWeightLambda M k 0 + radialWeightLambda M (k + 1) 0 = 1 := by
  let i : ℕ := (M + k + 2) / 2
  have hi : i ∈ range (M + 1) := by
    apply mem_range.mpr
    dsimp only [i]
    omega
  have he : 2 * (i : ℤ) - (M : ℤ) = ((k + 1 : ℕ) : ℤ) ∨
      2 * (i : ℤ) - (M : ℤ) = ((k + 1 + 1 : ℕ) : ℤ) := by
    dsimp only [i]
    omega
  simp only [radialWeightLambda, neg_zero, Real.exp_zero, chebyshevRadialLaurent_one,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, ← sum_add_distrib,
    LaurentPolynomial.T_apply, Nat.cast_add, Nat.cast_one]
  rw [sum_eq_single_of_mem i hi]
  · rcases he with he | he
    · have he' : 2 * (i : ℤ) - (M : ℤ) = (k : ℤ) + 1 := by omega
      have hne : 2 * (i : ℤ) - (M : ℤ) ≠ (k : ℤ) + 1 + 1 := by omega
      rw [ite_eq_left he', ite_eq_right hne, add_zero]
    · have he' : 2 * (i : ℤ) - (M : ℤ) = (k : ℤ) + 1 + 1 := by omega
      have hne : 2 * (i : ℤ) - (M : ℤ) ≠ (k : ℤ) + 1 := by omega
      rw [ite_eq_right hne, ite_eq_left he', zero_add]
  · intro j _ hji
    have hj₁ : 2 * (j : ℤ) - (M : ℤ) ≠ (k : ℤ) + 1 := by
      rcases he with h₁ | h₂ <;> omega
    have hj₂ : 2 * (j : ℤ) - (M : ℤ) ≠ (k : ℤ) + 1 + 1 := by
      rcases he with h₁ | h₂ <;> omega
    rw [ite_eq_right hj₁, ite_eq_right hj₂, add_zero]

/-- The initial weight agrees with the coefficient in the Milin sum. -/
theorem radialWeightTau_zero {M k : ℕ} (hk : k ≤ M) :
    radialWeightTau M k 0 = (M : ℝ) - k := by
  refine Nat.decreasingInduction (motive := fun j _ ↦ radialWeightTau M j 0 = (M : ℝ) - j)
    ?_ ?_ hk
  · intro j hj hnext
    have hd := radialWeightTau_succ_sub M j 0
    rw [radialWeightLambda_zero_add_succ hj, hnext, Nat.cast_succ] at hd
    linarith
  · simp [radialWeightTau_eq_zero_of_le le_rfl]

private def weightSpecialize (q : ℝ) : WeightPolynomial →+* ℝ[T;T⁻¹] :=
  MvPolynomial.eval₂Hom (LaurentPolynomial.C.comp (Int.castRingHom ℝ))
    (fun b ↦ if b then LaurentPolynomial.T 1 else LaurentPolynomial.C q)

@[simp] private lemma weightSpecialize_X_false (q : ℝ) :
    weightSpecialize q (MvPolynomial.X false) = LaurentPolynomial.C q := by
  simp [weightSpecialize]

@[simp] private lemma weightSpecialize_X_true (q : ℝ) :
    weightSpecialize q (MvPolynomial.X true) = LaurentPolynomial.T 1 := by
  simp [weightSpecialize]

@[simp] private lemma weightSpecialize_C (q : ℝ) (a : ℤ) :
    weightSpecialize q (MvPolynomial.C a) = LaurentPolynomial.C (a : ℝ) := by
  simp [weightSpecialize]

private lemma radial_coeff_C_mul (a : ℝ) (P : ℝ[T;T⁻¹]) (i : ℤ) :
    (LaurentPolynomial.C a * P).coeff i = a * P.coeff i := by
  change (AddMonoidAlgebra.single (0 : ℤ) a * P).coeff i = _
  simpa only [neg_zero, zero_add] using AddMonoidAlgebra.coeff_single_mul_apply P a (0 : ℤ) i

private lemma radial_coeff_mul_C (a : ℝ) (P : ℝ[T;T⁻¹]) (i : ℤ) :
    (P * LaurentPolynomial.C a).coeff i = a * P.coeff i := by
  rw [mul_comm, radial_coeff_C_mul]

private lemma radial_coeff_T_mul (j : ℤ) (P : ℝ[T;T⁻¹]) (i : ℤ) :
    (LaurentPolynomial.T j * P).coeff i = P.coeff (i - j) := by
  change (AddMonoidAlgebra.single j (1 : ℝ) * P).coeff i = _
  simpa only [one_mul, sub_eq_add_neg, add_comm] using
    AddMonoidAlgebra.coeff_single_mul_apply P (1 : ℝ) j i

private lemma radial_coeff_mul_T (j : ℤ) (P : ℝ[T;T⁻¹]) (i : ℤ) :
    (P * LaurentPolynomial.T j).coeff i = P.coeff (i - j) := by
  rw [mul_comm, radial_coeff_T_mul]

private lemma hasDerivAt_exp_neg (u : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.exp (-t)) (-Real.exp (-u)) u := by
  have hneg : HasDerivAt (fun t : ℝ ↦ -t) (-1) u := (hasDerivAt_id u).neg
  simpa only [Function.comp_def, mul_neg, mul_one] using
    (Real.hasDerivAt_exp (-u)).comp u hneg

private lemma hasDerivAt_weightSpecialize_coeff (P : WeightPolynomial) :
    ∀ (i : ℤ) (u : ℝ),
      HasDerivAt (fun t ↦ (weightSpecialize (Real.exp (-t)) P).coeff i)
        (-Real.exp (-u) * (weightSpecialize (Real.exp (-u)) (MvPolynomial.pderiv false P)).coeff i) u := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro i u
    simpa only [weightSpecialize_C, MvPolynomial.pderiv_C, map_zero,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, mul_zero] using
      hasDerivAt_const u ((LaurentPolynomial.C (a : ℝ)).coeff i)
  | add P Q hP hQ =>
    intro i u
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]
    exact (hP i u).fun_add (hQ i u)
  | mul_X P b ih =>
    intro i u
    cases b
    · simp only [MvPolynomial.pderiv_mul, map_add, AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, MvPolynomial.pderiv_X_self, mul_one, map_mul,
        weightSpecialize_X_false, radial_coeff_mul_C]
      convert (hasDerivAt_exp_neg u).fun_mul (ih i u) using 1
      ring
    · simpa only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne (by decide : true ≠ false),
        mul_zero, add_zero, map_mul, weightSpecialize_X_true, radial_coeff_mul_T] using
        ih (i - 1) u

private lemma coeff_weightSpecialize_variable_pderiv (P : WeightPolynomial) (q : ℝ) :
    ∀ i : ℤ, (weightSpecialize q (MvPolynomial.X true * MvPolynomial.pderiv true P)).coeff i =
      (i : ℝ) * (weightSpecialize q P).coeff i := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro i
    simp only [MvPolynomial.pderiv_C, mul_zero, map_zero, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply, weightSpecialize_C, LaurentPolynomial.C_apply]
    by_cases hi : i = 0
    · rw [ite_eq_left hi, hi, Int.cast_zero, zero_mul]
    · rw [ite_eq_right hi, mul_zero]
  | add P Q hP hQ =>
    intro i
    simp only [map_add, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]
  | mul_X P b ih =>
    intro i
    cases b
    · have hp : MvPolynomial.X true * MvPolynomial.pderiv true (P * MvPolynomial.X false) =
          (MvPolynomial.X true * MvPolynomial.pderiv true P) * MvPolynomial.X false := by
        rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne (by decide : false ≠ true),
          mul_zero, add_zero, mul_assoc]
      rw [hp, map_mul, weightSpecialize_X_false, radial_coeff_mul_C, ih,
        map_mul, weightSpecialize_X_false, radial_coeff_mul_C]
      ring
    · have hp : MvPolynomial.X true * MvPolynomial.pderiv true (P * MvPolynomial.X true) =
          (MvPolynomial.X true * MvPolynomial.pderiv true P + P) * MvPolynomial.X true := by
        rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self]
        ring
      rw [hp, map_mul, weightSpecialize_X_true, radial_coeff_mul_T]
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      rw [ih (i - 1), map_mul, weightSpecialize_X_true, radial_coeff_mul_T,
        Int.cast_sub, Int.cast_one]
      ring

private def radialLaurentArgument (q : ℝ) : ℝ[T;T⁻¹] :=
  LaurentPolynomial.C (1 - q) + LaurentPolynomial.C (q / 2) *
    (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))

private lemma chebyshevRadialLaurent_add_two (M : ℕ) (q : ℝ) :
    chebyshevRadialLaurent (M + 2) q = 2 * radialLaurentArgument q *
      chebyshevRadialLaurent (M + 1) q - chebyshevRadialLaurent M q := by
  simp only [chebyshevRadialLaurent, radialLaurentArgument, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [Polynomial.Chebyshev.U_add_two, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_mul, Polynomial.eval₂_ofNat, Polynomial.eval₂_X]

private lemma weightSpecialize_twiceRadialArgument (q : ℝ) :
    weightSpecialize q twiceRadialArgument = LaurentPolynomial.T 1 * (2 * radialLaurentArgument q) := by
  have hsub : (1 : ℝ[T;T⁻¹]) - LaurentPolynomial.C q = LaurentPolynomial.C (1 - q) := by
    rw [map_sub, map_one]
  have hq : (2 : ℝ[T;T⁻¹]) * LaurentPolynomial.C (q / 2) = LaurentPolynomial.C q := by
    have he : (2 : ℝ[T;T⁻¹]) = LaurentPolynomial.C (2 : ℝ) :=
      (map_ofNat LaurentPolynomial.C 2).symm
    rw [he, ← map_mul]
    congr 1
    ring
  have hT : (LaurentPolynomial.T 1 : ℝ[T;T⁻¹]) * LaurentPolynomial.T (-1) = 1 := by
    rw [← LaurentPolynomial.T_add]
    norm_num
  simp only [twiceRadialArgument, weightTime, weightVariable, map_add, map_mul, map_sub, map_one,
    map_pow, weightSpecialize_X_false, weightSpecialize_X_true, radialLaurentArgument]
  rw [hsub]
  calc
    _ = 2 * LaurentPolynomial.C (1 - q) * LaurentPolynomial.T 1 +
        LaurentPolynomial.C q * (LaurentPolynomial.T 1 ^ 2 + LaurentPolynomial.T 1 * LaurentPolynomial.T (-1)) := by
      rw [hT]
      ring
    _ = _ := by rw [← hq]; ring

private lemma weightSpecialize_clearedChebyshevWeight (M : ℕ) (q : ℝ) :
    weightSpecialize q (clearedChebyshevWeight M) =
      LaurentPolynomial.T (M : ℤ) * chebyshevRadialLaurent M q := by
  induction M using Nat.twoStepInduction with
  | zero => simp [clearedChebyshevWeight, chebyshevRadialLaurent]
  | one =>
    simp only [clearedChebyshevWeight, weightSpecialize_twiceRadialArgument,
      chebyshevRadialLaurent, radialLaurentArgument, Nat.cast_one, Polynomial.Chebyshev.U_one,
      Polynomial.eval₂_mul, Polynomial.eval₂_ofNat, Polynomial.eval₂_X]
  | more M h h' =>
    have hT₁ : (LaurentPolynomial.T 1 : ℝ[T;T⁻¹]) * LaurentPolynomial.T ((M + 1 : ℕ) : ℤ) =
        LaurentPolynomial.T ((M + 2 : ℕ) : ℤ) := by
      rw [← LaurentPolynomial.T_add]
      congr 1
      push_cast
      ring
    have hT₂ : (LaurentPolynomial.T 1 : ℝ[T;T⁻¹]) ^ 2 * LaurentPolynomial.T (M : ℤ) =
        LaurentPolynomial.T ((M + 2 : ℕ) : ℤ) := by
      rw [pow_two, ← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add]
      congr 1
      push_cast
      ring
    simp only [clearedChebyshevWeight, map_sub, map_mul, map_pow, weightVariable,
      weightSpecialize_X_true, weightSpecialize_twiceRadialArgument, h, h',
      chebyshevRadialLaurent_add_two]
    calc
      _ = (LaurentPolynomial.T 1 * LaurentPolynomial.T ((M + 1 : ℕ) : ℤ)) *
          (2 * radialLaurentArgument q * chebyshevRadialLaurent (M + 1) q) -
          (LaurentPolynomial.T 1 ^ 2 * LaurentPolynomial.T (M : ℤ)) * chebyshevRadialLaurent M q := by ring
      _ = _ := by rw [hT₁, hT₂]; ring

private lemma weightSpecialize_coeff_flow (M : ℕ) (q : ℝ) (i : ℤ) :
    let P := clearedChebyshevWeight M;
    -q * (weightSpecialize q (MvPolynomial.pderiv false P)).coeff i +
      -q * (weightSpecialize q (MvPolynomial.pderiv false P)).coeff (i - 1) =
      ((i : ℝ) - M) * (weightSpecialize q P).coeff i -
        ((i : ℝ) - 1 - M) * (weightSpecialize q P).coeff (i - 1) := by
  let P := clearedChebyshevWeight M
  let Z : ℝ[T;T⁻¹] := LaurentPolynomial.T 1
  let A : ℝ[T;T⁻¹] := weightSpecialize q P
  let B : ℝ[T;T⁻¹] := weightSpecialize q (MvPolynomial.pderiv false P)
  let C : ℝ[T;T⁻¹] := weightSpecialize q (MvPolynomial.pderiv true P)
  let D : ℝ[T;T⁻¹] := -LaurentPolynomial.C q * B
  let H : ℝ[T;T⁻¹] := Z * C
  have hM : weightSpecialize q (M : WeightPolynomial) = LaurentPolynomial.C (M : ℝ) := by
    rw [map_natCast, map_natCast]
  have hFlow := congrArg (weightSpecialize q) (weightFlow_clearedChebyshevWeight M)
  simp only [weightFlow, weightTime, weightVariable, map_add, map_sub, map_neg, map_mul,
    map_one, weightSpecialize_X_false, weightSpecialize_X_true, hM] at hFlow
  change -((1 + Z) * LaurentPolynomial.C q) * B - ((1 - Z) * Z) * C =
    -LaurentPolynomial.C (M : ℝ) * (1 - Z) * A at hFlow
  have hflow : D + Z * D - H + Z * H =
      -(LaurentPolynomial.C (M : ℝ) * A) + LaurentPolynomial.C (M : ℝ) * (Z * A) := by
    dsimp only [D, H]
    linear_combination hFlow
  have hcoef := congrArg (fun R : ℝ[T;T⁻¹] ↦ R.coeff i) hflow
  have hH (j : ℤ) : H.coeff j = (j : ℝ) * A.coeff j := by
    have h := coeff_weightSpecialize_variable_pderiv P q j
    simpa only [map_mul, weightSpecialize_X_true, A, H, Z, C] using h
  have hD (j : ℤ) : D.coeff j = -q * B.coeff j := by
    rw [show D = LaurentPolynomial.C (-q) * B by simp [D], radial_coeff_C_mul]
  change (D + LaurentPolynomial.T 1 * D - H + LaurentPolynomial.T 1 * H).coeff i =
    (-(LaurentPolynomial.C (M : ℝ) * A) + LaurentPolynomial.C (M : ℝ) *
      (LaurentPolynomial.T 1 * A)).coeff i at hcoef
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_neg,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.neg_apply, radial_coeff_T_mul, radial_coeff_C_mul,
    hD, hH, Int.cast_sub, Int.cast_one] at hcoef
  change -q * B.coeff i + -q * B.coeff (i - 1) =
    ((i : ℝ) - M) * A.coeff i - ((i : ℝ) - 1 - M) * A.coeff (i - 1)
  linear_combination hcoef

/-- The shared derivative of two consecutive Laurent coefficients, after clearing the shift. -/
theorem hasDerivAt_radialWeightLambda_add_succ (M k : ℕ) (u : ℝ) :
    HasDerivAt (fun t ↦ radialWeightLambda M k t + radialWeightLambda M (k + 1) t)
      (((k : ℝ) + 2) * radialWeightLambda M (k + 1) u -
        ((k : ℝ) + 1) * radialWeightLambda M k u) u := by
  let P := clearedChebyshevWeight M
  let i : ℤ := (M : ℤ) + ((k + 1 + 1 : ℕ) : ℤ)
  have hcur : (fun t ↦ (weightSpecialize (Real.exp (-t)) P).coeff (i - 1)) = radialWeightLambda M k := by
    funext t
    rw [radialWeightLambda, show P = clearedChebyshevWeight M from rfl,
      weightSpecialize_clearedChebyshevWeight, radial_coeff_T_mul]
    congr 1
    dsimp only [i]
    omega
  have hnext : (fun t ↦ (weightSpecialize (Real.exp (-t)) P).coeff i) = radialWeightLambda M (k + 1) := by
    funext t
    rw [radialWeightLambda, show P = clearedChebyshevWeight M from rfl,
      weightSpecialize_clearedChebyshevWeight, radial_coeff_T_mul]
    congr 1
    dsimp only [i]
    omega
  have hc := hasDerivAt_weightSpecialize_coeff P (i - 1) u
  have hn := hasDerivAt_weightSpecialize_coeff P i u
  rw [hcur] at hc
  rw [hnext] at hn
  have hd := weightSpecialize_coeff_flow M (Real.exp (-u)) i
  change -Real.exp (-u) * (weightSpecialize (Real.exp (-u)) (MvPolynomial.pderiv false P)).coeff i +
    -Real.exp (-u) * (weightSpecialize (Real.exp (-u)) (MvPolynomial.pderiv false P)).coeff (i - 1) =
      ((i : ℝ) - M) * (weightSpecialize (Real.exp (-u)) P).coeff i -
        ((i : ℝ) - 1 - M) * (weightSpecialize (Real.exp (-u)) P).coeff (i - 1) at hd
  rw [congrFun hnext u, congrFun hcur u] at hd
  have hiR : (i : ℝ) - M = (k : ℝ) + 2 := by
    dsimp only [i]
    push_cast
    ring
  have hiR' : (i : ℝ) - 1 - M = (k : ℝ) + 1 := by linarith
  rw [hiR, hiR'] at hd
  convert hc.fun_add hn using 1
  linear_combination -hd

/-- The time derivative of a potential weight is minus its index times its Laurent coefficient. -/
theorem hasDerivAt_radialWeightTau {M k : ℕ} (hk : k ≤ M) (u : ℝ) :
    HasDerivAt (radialWeightTau M k) (-((k : ℝ) + 1) * radialWeightLambda M k u) u := by
  refine Nat.decreasingInduction
    (motive := fun j _ ↦ HasDerivAt (radialWeightTau M j)
      (-((j : ℝ) + 1) * radialWeightLambda M j u) u) ?_ ?_ hk
  · intro j _ hj
    have heq : radialWeightTau M j = fun t ↦ radialWeightTau M (j + 1) t +
        (radialWeightLambda M j t + radialWeightLambda M (j + 1) t) := by
      funext t
      linarith [radialWeightTau_succ_sub M j t]
    rw [heq]
    convert hj.fun_add (hasDerivAt_radialWeightLambda_add_succ M j u) using 1
    rw [Nat.cast_succ]
    ring
  · have hzero : radialWeightTau M M = fun _ ↦ 0 := funext (radialWeightTau_eq_zero_of_le le_rfl)
    rw [hzero, radialWeightLambda_eq_zero_of_le le_rfl, mul_zero]
    exact hasDerivAt_const u 0

/-- Laurent coefficient paths are continuous in radial time. -/
theorem continuous_radialWeightLambda (M k : ℕ) : Continuous (radialWeightLambda M k) := by
  unfold radialWeightLambda
  simp_rw [chebyshevRadialLaurent_coeff_eq_legendre_sum]
  refine continuous_finsetSum _ fun n _ ↦ ?_
  exact continuous_const.mul
    ((continuous_diagonalLegendreLaurent_coeff n ((k + 1 : ℕ) : ℤ)).comp
      (Real.continuous_exp.comp continuous_neg))

/-- Every potential weight is absolutely continuous on compact time intervals. -/
theorem absolutelyContinuousOnInterval_radialWeightTau {M k : ℕ} (hk : k ≤ M) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (radialWeightTau M k) a b := by
  have hd : deriv (radialWeightTau M k) =
      fun u ↦ -((k : ℝ) + 1) * radialWeightLambda M k u :=
    funext (fun u ↦ (hasDerivAt_radialWeightTau hk u).deriv)
  have hc : Continuous (deriv (radialWeightTau M k)) := by
    rw [hd]
    exact continuous_const.mul (continuous_radialWeightLambda M k)
  have hSmooth : ContDiff ℝ 1 (radialWeightTau M k) :=
    contDiff_one_iff_deriv.mpr ⟨fun u ↦ (hasDerivAt_radialWeightTau hk u).differentiableAt, hc⟩
  obtain ⟨K, hK⟩ := hSmooth.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_uIcc a b) isCompact_uIcc
  exact hK.absolutelyContinuousOnInterval

end Zalcman
