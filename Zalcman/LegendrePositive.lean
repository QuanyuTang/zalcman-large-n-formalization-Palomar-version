/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positivity of the polynomial obtained by clearing the Legendre Laurent denominator

The middle coefficient in a homogeneous substitution of degree `2 * n` gives
the Bernstein expression for the Legendre polynomial. Conjugating the
substitution `diag(X, 1)` by a real rotation exhibits its spectral coefficients
as weighted real squares. The usual Laurent coefficients are indexed by shifting
the polynomial coefficient indices by `n`.
-/

public section

noncomputable section

namespace Zalcman

open Polynomial Finset
open scoped LaurentPolynomial Polynomial.Bivariate

private def linearPolynomial {R : Type*} [Semiring R] (a b : R) : R[X] := C a * X + C b

private def substitutionCoefficient {R : Type*} [Semiring R]
    (n i j : ℕ) (a b c d : R) : R :=
  ((linearPolynomial a b) ^ j * (linearPolynomial c d) ^ (n - j)).coeff i

private lemma substitutionCoefficient_map {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (n i j : ℕ) (a b c d : R) :
    f (substitutionCoefficient n i j a b c d) =
      substitutionCoefficient n i j (f a) (f b) (f c) (f d) := by
  simp only [substitutionCoefficient, linearPolynomial, ← Polynomial.coeff_map,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, map_X, map_C]

private lemma linearPolynomial_pow_coeff {R : Type*} [CommSemiring R]
    (n i : ℕ) (hi : i ≤ n) (a b : R) :
    ((linearPolynomial a b) ^ n).coeff i = (n.choose i : R) * a ^ i * b ^ (n - i) := by
  have hterm (k : ℕ) :
      (C a * X) ^ k * (C b) ^ (n - k) * (n.choose k : R[X]) =
        C ((n.choose k : R) * a ^ k * b ^ (n - k)) * X ^ k := by
    simp only [mul_pow, map_mul, map_pow, C_eq_natCast]
    ring
  rw [linearPolynomial, add_pow, finsetSum_coeff]
  simp_rw [hterm, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [Ne.symm hki]
  · simp [Finset.mem_range.mpr (Nat.lt_succ_of_le hi)]

private lemma swap_coeff_coeff {R : Type*} [CommSemiring R]
    (P : R[X][Y]) (i j : ℕ) :
    ((Polynomial.Bivariate.swap P).coeff j).coeff i = (P.coeff i).coeff j := by
  induction P using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial n f =>
    induction f using Polynomial.induction_on' with
    | add f g hf hg => rw [map_add (monomial n)]; simp [hf, hg]
    | monomial m r =>
      by_cases hi : n = i <;> by_cases hj : m = j <;>
        simp [Polynomial.Bivariate.swap_monomial_monomial, coeff_monomial, hi, hj]

private lemma substitutionCoefficient_transpose {R : Type*} [CommSemiring R]
    {n i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) (a b c d : R) :
    (n.choose j : R) * substitutionCoefficient n i j a b c d =
      (n.choose i : R) * substitutionCoefficient n j i a c b d := by
  let P : R[X][Y] := (linearPolynomial (linearPolynomial a b) (linearPolynomial c d)) ^ n
  have hswap : Polynomial.Bivariate.swap P =
      (linearPolynomial (linearPolynomial a c) (linearPolynomial b d)) ^ n := by
    simp only [P, linearPolynomial, map_pow, map_mul, map_add, Polynomial.Bivariate.swap_C,
      Polynomial.Bivariate.swap_Y, map_C, map_X]
    ring
  have h := (swap_coeff_coeff P j i).symm
  rw [hswap] at h
  dsimp only [P] at h
  simpa only [linearPolynomial_pow_coeff n j hj, linearPolynomial_pow_coeff n i hi,
    ← C_eq_natCast, mul_assoc, coeff_C_mul, substitutionCoefficient] using h

private lemma degree_linearPolynomial_le {R : Type*} [Semiring R] (a b : R) :
    (linearPolynomial a b).natDegree ≤ 1 := by
  unfold linearPolynomial
  apply natDegree_add_le_of_degree_le
  · simpa only [pow_one] using natDegree_C_mul_X_pow_le a 1
  · simp

private lemma homogenize_pow_degree_one {R : Type*} [CommSemiring R] (p : R[X])
    (hp : p.natDegree ≤ 1) (n : ℕ) : (p ^ n).homogenize n = (p.homogenize 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hdeg : (p ^ n).natDegree ≤ n := by simpa using natDegree_pow_le_of_le n hp
    rw [pow_succ p, homogenize_mul _ _ hdeg hp, ih, pow_succ]

private lemma apply_homogenize {R : Type*} [CommSemiring R] (p : R[X])
    (n : ℕ) (x y : R) : MvPolynomial.eval ![x, y] (p.homogenize n) =
      ∑ i ∈ range (n + 1), p.coeff i * x ^ i * y ^ (n - i) := by
  simp only [Polynomial.homogenize, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    MvPolynomial.eval_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two, mul_assoc]

private lemma substitution_expansion {R : Type*} [CommSemiring R]
    (n j : ℕ) (hj : j ≤ n) (a b c d x y : R) :
    (a * x + b * y) ^ j * (c * x + d * y) ^ (n - j) =
      ∑ i ∈ range (n + 1), substitutionCoefficient n i j a b c d * x ^ i * y ^ (n - i) := by
  let p := linearPolynomial a b
  let q := linearPolynomial c d
  have hp := degree_linearPolynomial_le a b
  have hq := degree_linearPolynomial_le c d
  have hpd : (p ^ j).natDegree ≤ j := by simpa using natDegree_pow_le_of_le j hp
  have hqd : (q ^ (n - j)).natDegree ≤ n - j := by
    simpa using natDegree_pow_le_of_le (n - j) hq
  have h := homogenize_mul (p ^ j) (q ^ (n - j)) hpd hqd
  rw [Nat.add_sub_of_le hj, homogenize_pow_degree_one p hp j,
    homogenize_pow_degree_one q hq (n - j)] at h
  calc
    _ = MvPolynomial.eval ![x, y] (((p ^ j) * (q ^ (n - j))).homogenize n) := by
      rw [h]
      simp [p, q, linearPolynomial, homogenize_add, homogenize_C_mul,
        homogenize_X Nat.one_ne_zero, homogenize_C]
    _ = _ := apply_homogenize _ _ _ _

private lemma central_coefficient {R : Type*} [CommSemiring R] (n : ℕ) (a b c d : R) :
    substitutionCoefficient (2 * n) n n a b c d =
      ∑ i ∈ range (n + 1), (n.choose i : R) ^ 2 * (a * d) ^ i * (b * c) ^ (n - i) := by
  have hn : 2 * n - n = n := by omega
  rw [substitutionCoefficient, hn, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun i hi ↦ ?_
  have hle := Nat.le_of_lt_succ (mem_range.mp hi)
  rw [linearPolynomial_pow_coeff _ _ hle, linearPolynomial_pow_coeff _ _ (Nat.sub_le _ _),
    Nat.choose_symm hle, Nat.sub_sub_self hle, mul_pow, mul_pow, pow_two]
  ring

private lemma rotation_product_nonneg (n i : ℕ) (hi : i ≤ 2 * n) (a b : ℝ) :
    0 ≤ substitutionCoefficient (2 * n) i n a b (-b) a *
      substitutionCoefficient (2 * n) n i a (-b) b a := by
  let r := substitutionCoefficient (2 * n) i n a b (-b) a
  let s := substitutionCoefficient (2 * n) n i a (-b) b a
  have hn : n ≤ 2 * n := by omega
  have h := substitutionCoefficient_transpose hi hn a b (-b) a
  change ((2 * n).choose n : ℝ) * r = ((2 * n).choose i : ℝ) * s at h
  change 0 ≤ r * s
  have hi' : (0 : ℝ) < (2 * n).choose i := by exact_mod_cast Nat.choose_pos hi
  apply nonneg_of_mul_nonneg_right _ hi'
  calc
    0 ≤ ((2 * n).choose n : ℝ) * r ^ 2 := by positivity
    _ = r * (((2 * n).choose n : ℝ) * r) := by ring
    _ = ((2 * n).choose i : ℝ) * (r * s) := by rw [h]; ring

private lemma rotation_middle (n : ℕ) (a b : ℝ) :
    substitutionCoefficient (2 * n) n n
      (C (a ^ 2) * X + C (b ^ 2)) (C (a * b) * (1 - X))
      (C (a * b) * (1 - X)) (C (b ^ 2) * X + C (a ^ 2)) =
      ∑ i ∈ range (2 * n + 1),
        C (substitutionCoefficient (2 * n) i n a b (-b) a *
          substitutionCoefficient (2 * n) n i a (-b) b a) * X ^ i := by
  let lift : ℝ →+* ℝ[X][Y] := (C : ℝ[X] →+* ℝ[X][Y]).comp (C : ℝ →+* ℝ[X])
  let u : ℝ[X][Y] := linearPolynomial (C a) (C (-b))
  let v : ℝ[X][Y] := linearPolynomial (C b) (C a)
  let A : ℝ[X] := C (a ^ 2) * X + C (b ^ 2)
  let B : ℝ[X] := C (a * b) * (1 - X)
  let D : ℝ[X] := C (b ^ 2) * X + C (a ^ 2)
  have hn : n ≤ 2 * n := by omega
  have hnn : 2 * n - n = n := by omega
  have h₁ : lift a * (C X * u) + lift b * v = linearPolynomial A B := by
    simp only [lift, RingHom.comp_apply, u, v, A, B, linearPolynomial,
      map_mul, map_add, map_pow, map_neg, map_sub, map_one]
    ring
  have h₂ : lift (-b) * (C X * u) + lift a * v = linearPolynomial B D := by
    simp only [lift, RingHom.comp_apply, u, v, B, D, linearPolynomial,
      map_mul, map_add, map_pow, map_neg, map_sub, map_one]
    ring
  have h := substitution_expansion (2 * n) n hn (lift a) (lift b) (lift (-b))
    (lift a) (C X * u) v
  simp only [h₁, h₂, hnn, ← substitutionCoefficient_map lift] at h
  change substitutionCoefficient (2 * n) n n A B B D = _
  calc
    _ = ((linearPolynomial A B) ^ n * (linearPolynomial B D) ^ n).coeff n := by
      simp only [substitutionCoefficient, hnn]
    _ = (∑ i ∈ range (2 * n + 1),
      lift (substitutionCoefficient (2 * n) i n a b (-b) a) * (C X * u) ^ i *
        v ^ (2 * n - i)).coeff n := congrArg (fun P : ℝ[X][Y] ↦ P.coeff n) h
    _ = _ := by
      rw [finsetSum_coeff]
      refine sum_congr rfl fun i _ ↦ ?_
      have hfactor : lift (substitutionCoefficient (2 * n) i n a b (-b) a) *
          (C X * u) ^ i * v ^ (2 * n - i) =
        C (C (substitutionCoefficient (2 * n) i n a b (-b) a) * X ^ i) *
          (u ^ i * v ^ (2 * n - i)) := by
        simp only [lift, RingHom.comp_apply, map_mul, map_pow, mul_pow]
        ring
      have hc : (u ^ i * v ^ (2 * n - i)).coeff n =
          C (substitutionCoefficient (2 * n) n i a (-b) b a) :=
        (substitutionCoefficient_map (C : ℝ →+* ℝ[X]) (2 * n) n i a (-b) b a).symm
      rw [hfactor, coeff_C_mul, hc, map_mul]
      ring

/-- The Legendre Bernstein expression, with the Laurent denominator cleared. -/
@[expose] def clearedDiagonalLegendre (n : ℕ) (q : ℝ) : ℝ[X] :=
  let J : ℝ[X] := C (q / 4) * (X - 1) ^ 2
  ∑ i ∈ range (n + 1), C ((n.choose i : ℝ) ^ 2) * (X + J) ^ i * J ^ (n - i)

/-- Every coefficient of the cleared diagonal Legendre polynomial is nonnegative. -/
theorem clearedDiagonalLegendre_coeff_nonneg (n k : ℕ) {q : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) : 0 ≤ (clearedDiagonalLegendre n q).coeff k := by
  let r := Real.sqrt (1 - q)
  have hr₀ : 0 ≤ r := Real.sqrt_nonneg _
  have hr₂ : r ^ 2 = 1 - q := Real.sq_sqrt (sub_nonneg.mpr hq₁)
  have hr₁ : r ≤ 1 := by nlinarith only [hq₀, hr₂, sq_nonneg (r - 1)]
  let a := Real.sqrt ((1 + r) / 2)
  let b := Real.sqrt ((1 - r) / 2)
  have ha₂ : a ^ 2 = (1 + r) / 2 := Real.sq_sqrt (by positivity)
  have hb₂ : b ^ 2 = (1 - r) / 2 := Real.sq_sqrt (by linarith)
  have hs : a ^ 2 + b ^ 2 = 1 := by rw [ha₂, hb₂]; ring
  have hp : (a * b) ^ 2 = q / 4 := by rw [mul_pow, ha₂, hb₂]; nlinarith only [hr₂]
  let A : ℝ[X] := C (a ^ 2) * X + C (b ^ 2)
  let B : ℝ[X] := C (a * b) * (1 - X)
  let D : ℝ[X] := C (b ^ 2) * X + C (a ^ 2)
  let J : ℝ[X] := C (q / 4) * (X - 1) ^ 2
  have hB : B ^ 2 = J := by
    dsimp only [B, J]
    rw [mul_pow, ← C_pow, hp, show ((1 : ℝ[X]) - X) ^ 2 = (X - 1) ^ 2 by ring]
  have hAD : A * D = X + J := by
    rw [← hB]
    have hs' : (C a : ℝ[X]) ^ 2 + (C b) ^ 2 = 1 := by
      rw [← C_pow, ← C_pow, ← C_add, hs, map_one]
    simp only [A, B, D, map_pow, map_mul]
    linear_combination X * ((C a : ℝ[X]) ^ 2 + (C b) ^ 2 + 1) * hs'
  have hmiddle : substitutionCoefficient (2 * n) n n A B B D = clearedDiagonalLegendre n q := by
    rw [central_coefficient, hAD, ← pow_two B, hB]
    simp only [clearedDiagonalLegendre, J, C_eq_natCast, map_pow]
  have hrotation := rotation_middle n a b
  change substitutionCoefficient (2 * n) n n A B B D = _ at hrotation
  rw [← hmiddle, hrotation, finsetSum_coeff]
  refine sum_nonneg fun i hi ↦ ?_
  rw [coeff_C_mul_X_pow]
  split_ifs
  · exact rotation_product_nonneg n i (Nat.le_of_lt_succ (mem_range.mp hi)) a b
  · exact le_rfl

private lemma choose_mul_complementary_descFactorial {n i : ℕ} (hi : i ≤ n) :
    n.choose i * n.descFactorial (n - i) * n.descFactorial i =
      n.factorial * n.choose i ^ 2 := by
  rw [Nat.descFactorial_eq_factorial_mul_choose n (n - i),
    Nat.descFactorial_eq_factorial_mul_choose n i, Nat.choose_symm hi]
  calc
    _ = (n.choose i * i.factorial * (n - i).factorial) * n.choose i ^ 2 := by ring
    _ = _ := by rw [Nat.choose_mul_factorial_mul_factorial hi]

private lemma iterate_derivative_one_sub_pow (n j : ℕ) :
    (Polynomial.derivative^[j]) ((1 - X : ℤ[X]) ^ n) =
      (-1) ^ j * (n.descFactorial j : ℤ[X]) * (1 - X) ^ (n - j) := by
  have hcomp : ((X : ℤ[X]) ^ n).comp (1 - X) = (1 - X) ^ n := by simp [pow_comp]
  rw [← hcomp, iterate_derivative_comp_one_sub_X, iterate_derivative_X_pow_eq_natCast_mul,
    mul_comp, natCast_comp, pow_comp, X_comp, mul_assoc]

/-- The Bernstein expression for Mathlib's shifted Legendre polynomial follows from
Rodrigues' formula and the iterated product rule. -/
theorem shiftedLegendre_eq_bernstein_sum (n : ℕ) : shiftedLegendre n =
    ∑ i ∈ range (n + 1), C ((n.choose i : ℤ) ^ 2) * (1 - X) ^ i * (-X) ^ (n - i) := by
  have hn : (n.factorial : ℤ[X]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply mul_left_cancel₀ hn
  rw [factorial_mul_shiftedLegendre_eq, mul_comm ((X : ℤ[X]) ^ n) ((1 - X) ^ n),
    iterate_derivative_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Nat.le_of_lt_succ (mem_range.mp hi)
  have hcast : (n.choose i : ℤ[X]) * (n.descFactorial (n - i) : ℤ[X]) *
      (n.descFactorial i : ℤ[X]) = (n.factorial : ℤ[X]) * (n.choose i : ℤ[X]) ^ 2 := by
    exact_mod_cast choose_mul_complementary_descFactorial hi'
  have hpow : (-X : ℤ[X]) ^ (n - i) = (-1) ^ (n - i) * X ^ (n - i) := by
    rw [← neg_one_mul, mul_pow]
  rw [iterate_derivative_one_sub_pow, iterate_derivative_X_pow_eq_natCast_mul,
    Nat.sub_sub_self hi', nsmul_eq_mul, hpow, C_pow, C_eq_natCast]
  calc
    _ = ((n.choose i : ℤ[X]) * (n.descFactorial (n - i) : ℤ[X]) *
      (n.descFactorial i : ℤ[X])) * ((-1) ^ (n - i) * (1 - X) ^ i * X ^ (n - i)) := by ring
    _ = _ := by rw [hcast]; ring

/-- The diagonal Laurent argument expressed in Mathlib's shifted Legendre variable. -/
@[expose] def shiftedDiagonalArgument (q : ℝ) : ℝ[T;T⁻¹] :=
  LaurentPolynomial.C (q / 4) * (2 - LaurentPolynomial.T 1 - LaurentPolynomial.T (-1))

/-- The exact Laurent polynomial with argument `1 - q + (q / 2) * (T + T⁻¹)` in the
unshifted Legendre convention. Mathlib uses the variable `y = (1 - x) / 2`. -/
@[expose] def diagonalLegendreLaurent (n : ℕ) (q : ℝ) : ℝ[T;T⁻¹] :=
  (shiftedLegendre n).eval₂ (LaurentPolynomial.C.comp (Int.castRingHom ℝ))
    (shiftedDiagonalArgument q)

private lemma diagonalLegendreLaurent_eq_bernstein (n : ℕ) (q : ℝ) :
    diagonalLegendreLaurent n q =
      ∑ i ∈ range (n + 1), LaurentPolynomial.C ((n.choose i : ℝ) ^ 2) *
        (1 - shiftedDiagonalArgument q) ^ i * (-shiftedDiagonalArgument q) ^ (n - i) := by
  rw [diagonalLegendreLaurent, shiftedLegendre_eq_bernstein_sum]
  simp only [eval₂_finsetSum, eval₂_mul, eval₂_pow, eval₂_natCast, eval₂_sub,
    eval₂_neg, eval₂_one, eval₂_X, map_pow, map_natCast]

/-- Multiplication by `T^n` moves all Laurent coefficient indices to `ℕ` and gives
the cleared Bernstein polynomial used in the positivity proof. -/
theorem toLaurent_clearedDiagonalLegendre (n : ℕ) (q : ℝ) :
    (clearedDiagonalLegendre n q).toLaurent =
      LaurentPolynomial.T (n : ℤ) * diagonalLegendreLaurent n q := by
  let J : ℝ[X] := C (q / 4) * (X - 1) ^ 2
  let y := shiftedDiagonalArgument q
  let z : ℝ[T;T⁻¹] := LaurentPolynomial.T 1
  have hT : (LaurentPolynomial.T (-1) : ℝ[T;T⁻¹]) * z = 1 := by
    dsimp only [z]
    rw [← LaurentPolynomial.T_add]
    norm_num
  have hJ : J.toLaurent = -y * z := by
    simp only [J, y, z, shiftedDiagonalArgument, map_mul, map_pow, map_sub, map_one,
      toLaurent_C, toLaurent_X]
    change (LaurentPolynomial.C (q / 4) * (z - 1) ^ 2) =
      -(LaurentPolynomial.C (q / 4) * (2 - z - LaurentPolynomial.T (-1))) * z
    linear_combination -LaurentPolynomial.C (q / 4) * hT
  have hplus : ((X : ℝ[X]) + J).toLaurent = (1 - y) * z := by
    rw [map_add, toLaurent_X, hJ]
    change z + -y * z = _
    ring
  rw [diagonalLegendreLaurent_eq_bernstein, Finset.mul_sum]
  change (∑ i ∈ range (n + 1), C ((n.choose i : ℝ) ^ 2) * (X + J) ^ i *
    J ^ (n - i)).toLaurent = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Nat.le_of_lt_succ (mem_range.mp hi)
  have hp : z ^ i * z ^ (n - i) = (LaurentPolynomial.T (n : ℤ) : ℝ[T;T⁻¹]) := by
    rw [← pow_add, Nat.add_sub_of_le hi']
    simp [z]
  simp only [map_mul (Polynomial.toLaurent (R := ℝ)), map_pow (Polynomial.toLaurent (R := ℝ)),
    toLaurent_C]
  rw [hplus, hJ, mul_pow (1 - y), mul_pow (-y)]
  calc
    _ = (z ^ i * z ^ (n - i)) *
        (LaurentPolynomial.C ((n.choose i : ℝ) ^ 2) * (1 - y) ^ i * (-y) ^ (n - i)) := by ring
    _ = _ := by rw [hp]

/-- The Legendre Laurent coefficients in the positive triangular representation are nonnegative. -/
theorem diagonalLegendreLaurent_coeff_nonneg (n : ℕ) (k : ℤ) {q : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) : 0 ≤ (diagonalLegendreLaurent n q).coeff k := by
  have h := congrArg (fun p : ℝ[T;T⁻¹] ↦ p.coeff ((n : ℤ) + k))
    (toLaurent_clearedDiagonalLegendre n q)
  have hshift : ((LaurentPolynomial.T (n : ℤ)) * diagonalLegendreLaurent n q).coeff
      ((n : ℤ) + k) = (diagonalLegendreLaurent n q).coeff k := by
    rw [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_add, one_mul]
  rw [hshift] at h
  rw [← h, LaurentPolynomial.coeff_toLaurent]
  by_cases hk : 0 ≤ (n : ℤ) + k
  · let i := ((n : ℤ) + k).toNat
    have hi : (i : ℤ) = (n : ℤ) + k := Int.toNat_of_nonneg hk
    rw [← hi]
    change 0 ≤ Finsupp.mapDomain (Nat.castEmbedding : ℕ ↪ ℤ)
      (clearedDiagonalLegendre n q).toFinsupp.coeff ((Nat.castEmbedding : ℕ ↪ ℤ) i)
    rw [Finsupp.mapDomain_apply_of_injective (Nat.castEmbedding : ℕ ↪ ℤ).injective,
      Polynomial.toFinsupp_apply]
    exact clearedDiagonalLegendre_coeff_nonneg n i hq₀ hq₁
  · have hnot : (n : ℤ) + k ∉ Set.range (Nat.castEmbedding : ℕ ↪ ℤ) := by
      rintro ⟨i, hi⟩
      change (i : ℤ) = (n : ℤ) + k at hi
      exact hk (hi ▸ Int.natCast_nonneg i)
    rw [Finsupp.mapDomain_of_notMem_range _ _ hnot]

end Zalcman
