/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.LegendrePositive
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite Fourier weights of a Legendre polynomial

Specializing the positive Laurent polynomial to `q = 1` gives the cosine
expansion of `Pₙ(cos θ)`. Its weights form a probability mass supported on
the integers between `-n` and `n` of parity `n`.
-/

public section

noncomputable section

namespace Zalcman

open Polynomial Finset
open scoped LaurentPolynomial

/-- The finite Fourier weight at an integer frequency for `Pₙ(cos θ)`. -/
@[expose] def legendreFourierWeight (n : ℕ) (k : ℤ) : ℝ :=
  (diagonalLegendreLaurent n 1).coeff k

/-- Exactly the frequencies whose Fourier weights are nonzero. -/
@[expose] def legendreFourierSupport (n : ℕ) : Finset ℤ :=
  (diagonalLegendreLaurent n 1).coeff.support

theorem legendreFourierWeight_nonneg (n : ℕ) (k : ℤ) : 0 ≤ legendreFourierWeight n k :=
  diagonalLegendreLaurent_coeff_nonneg n k zero_le_one le_rfl

private lemma diagonalLegendreLaurent_coeff_shift (n : ℕ) (q : ℝ) (k : ℤ) :
    (diagonalLegendreLaurent n q).coeff k =
      if 0 ≤ (n : ℤ) + k then (clearedDiagonalLegendre n q).coeff ((n : ℤ) + k).toNat else 0 := by
  have h := congrArg (fun p : ℝ[T;T⁻¹] ↦ p.coeff ((n : ℤ) + k))
    (toLaurent_clearedDiagonalLegendre n q)
  have hshift : (LaurentPolynomial.T (n : ℤ) * diagonalLegendreLaurent n q).coeff
      ((n : ℤ) + k) = (diagonalLegendreLaurent n q).coeff k := by
    rw [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_add, one_mul]
  rw [hshift] at h
  rw [← h, LaurentPolynomial.coeff_toLaurent]
  by_cases hk : 0 ≤ (n : ℤ) + k
  · rw [ite_eq_left hk]
    set i := ((n : ℤ) + k).toNat
    have hi : (i : ℤ) = (n : ℤ) + k := Int.toNat_of_nonneg hk
    rw [← hi]
    change Finsupp.mapDomain (Nat.castEmbedding : ℕ ↪ ℤ)
      (clearedDiagonalLegendre n q).toFinsupp.coeff ((Nat.castEmbedding : ℕ ↪ ℤ) i) = _
    rw [Finsupp.mapDomain_apply_of_injective (Nat.castEmbedding : ℕ ↪ ℤ).injective,
      Polynomial.toFinsupp_apply]
  · rw [ite_eq_right hk]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨i, hi⟩
    change (i : ℤ) = (n : ℤ) + k at hi
    exact hk (hi ▸ Int.natCast_nonneg i)

private lemma clearedDiagonalLegendre_natDegree_le (n : ℕ) (q : ℝ) :
    (clearedDiagonalLegendre n q).natDegree ≤ 2 * n := by
  let J : ℝ[X] := C (q / 4) * (X - 1) ^ 2
  have hJ : J.natDegree ≤ 2 := by
    dsimp only [J]
    refine (natDegree_C_mul_le _ _).trans ?_
    have hlin : ((X : ℝ[X]) - 1).natDegree ≤ 1 := by simpa using natDegree_X_sub_C_le (1 : ℝ)
    simpa using natDegree_pow_le_of_le 2 hlin
  have hplus : ((X : ℝ[X]) + J).natDegree ≤ 2 :=
    natDegree_add_le_of_degree_le (natDegree_X_le.trans (by decide)) hJ
  change (∑ i ∈ range (n + 1), C ((n.choose i : ℝ) ^ 2) * (X + J) ^ i *
    J ^ (n - i)).natDegree ≤ _
  refine natDegree_sum_le_of_forall_le (range (n + 1)) _ fun i hi ↦ ?_
  have hi' := Nat.le_of_lt_succ (mem_range.mp hi)
  calc
    _ ≤ ((X + J) ^ i).natDegree + (J ^ (n - i)).natDegree :=
      natDegree_mul_le.trans (Nat.add_le_add_right (natDegree_C_mul_le _ _) _)
    _ ≤ i * 2 + (n - i) * 2 :=
      Nat.add_le_add (natDegree_pow_le_of_le _ hplus) (natDegree_pow_le_of_le _ hJ)
    _ = _ := by omega

theorem legendreFourierWeight_eq_zero_of_outside (n : ℕ) (k : ℤ)
    (hk : k < -(n : ℤ) ∨ (n : ℤ) < k) : legendreFourierWeight n k = 0 := by
  rw [legendreFourierWeight, diagonalLegendreLaurent_coeff_shift]
  rcases hk with hlo | hhi
  · exact ite_eq_right (by omega)
  · have hk' : 0 ≤ (n : ℤ) + k := by omega
    have hdeg : 2 * n < ((n : ℤ) + k).toNat := by omega
    rw [ite_eq_left hk']
    exact coeff_eq_zero_of_natDegree_lt ((clearedDiagonalLegendre_natDegree_le n 1).trans_lt hdeg)

private lemma clearedDiagonalLegendre_one_comp_neg_X (n : ℕ) :
    (clearedDiagonalLegendre n 1).comp (-X) = clearedDiagonalLegendre n 1 := by
  let J : ℝ[X] := C ((1 : ℝ) / 4) * (X - 1) ^ 2
  have hJ : J.comp (-X) = X + J := by
    have hquarter : C ((1 : ℝ) / 4) * (4 : ℝ[X]) = 1 := by
      calc
        _ = C (((1 : ℝ) / 4) * 4) := by rw [C_mul, C_ofNat 4]
        _ = 1 := by norm_num
    simp only [J, mul_comp, C_comp, pow_comp, sub_comp, X_comp, one_comp]
    linear_combination X * hquarter
  have hplus : ((X : ℝ[X]) + J).comp (-X) = J := by
    rw [add_comp, X_comp, hJ]
    ring
  let term (i : ℕ) : ℝ[X] := C ((n.choose i : ℝ) ^ 2) * (X + J) ^ i * J ^ (n - i)
  change (∑ i ∈ range (n + 1), term i).comp (-X) = ∑ i ∈ range (n + 1), term i
  rw [Polynomial.sum_comp]
  calc
    _ = ∑ i ∈ range (n + 1), term (n - i) := by
      refine sum_congr rfl fun i hi ↦ ?_
      have hi' := Nat.le_of_lt_succ (mem_range.mp hi)
      simp only [term, mul_comp, C_comp, pow_comp, hJ, hplus,
        Nat.choose_symm hi', Nat.sub_sub_self hi']
      ring
    _ = _ := by simpa using Finset.sum_range_reflect term (n + 1)

private lemma coeff_comp_neg_X (p : ℝ[X]) (k : ℕ) :
    (p.comp (-X)).coeff k = (-1 : ℝ) ^ k * p.coeff k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [add_comp, coeff_add, hp, hq, mul_add]
  | monomial n c =>
    have hneg : (-X : ℝ[X]) ^ n = C ((-1 : ℝ) ^ n) * X ^ n := by
      rw [← neg_one_mul (X : ℝ[X]), mul_pow, C_pow]
      simp
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp, hneg,
      ← mul_assoc, ← C_mul, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    by_cases h : k = n
    · subst k
      simp [mul_comm]
    · simp [h]

private lemma clearedDiagonalLegendre_one_odd_coeff_zero (n i : ℕ) (hi : Odd i) :
    (clearedDiagonalLegendre n 1).coeff i = 0 := by
  have h := congrArg (fun p : ℝ[X] ↦ p.coeff i) (clearedDiagonalLegendre_one_comp_neg_X n)
  change ((clearedDiagonalLegendre n 1).comp (-X)).coeff i = _ at h
  rw [coeff_comp_neg_X, hi.neg_one_pow] at h
  linarith only [h]

theorem legendreFourierWeight_eq_zero_of_not_modEq (n : ℕ) (k : ℤ)
    (hk : ¬ k ≡ (n : ℤ) [ZMOD 2]) : legendreFourierWeight n k = 0 := by
  rw [legendreFourierWeight, diagonalLegendreLaurent_coeff_shift]
  by_cases hnk : 0 ≤ (n : ℤ) + k
  · rw [ite_eq_left hnk]
    apply clearedDiagonalLegendre_one_odd_coeff_zero
    apply Nat.not_even_iff_odd.mp
    intro he
    obtain ⟨j, hj⟩ := even_iff_exists_two_mul.mp he
    have hc : ((((n : ℤ) + k).toNat : ℕ) : ℤ) = 2 * (j : ℤ) := by exact_mod_cast hj
    rw [Int.toNat_of_nonneg hnk] at hc
    exact hk (Int.modEq_iff_dvd.mpr ⟨(n : ℤ) - j, by omega⟩)
  · exact ite_eq_right hnk

private lemma legendreFourierWeight_ne_zero_of_mem {n : ℕ} {k : ℤ}
    (hk : k ∈ legendreFourierSupport n) : legendreFourierWeight n k ≠ 0 :=
  Finsupp.mem_support_iff.mp hk

/-- The finite weights satisfy the frequency bound needed by the connection average. -/
theorem abs_le_of_mem_legendreFourierSupport {n : ℕ} {k : ℤ}
    (hk : k ∈ legendreFourierSupport n) : |(k : ℝ)| ≤ (n : ℝ) := by
  have hne := legendreFourierWeight_ne_zero_of_mem hk
  have hlo : -(n : ℤ) ≤ k := le_of_not_gt fun h ↦ hne
    (legendreFourierWeight_eq_zero_of_outside n k (Or.inl h))
  have hhi : k ≤ (n : ℤ) := le_of_not_gt fun h ↦ hne
    (legendreFourierWeight_eq_zero_of_outside n k (Or.inr h))
  apply abs_le.mpr
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

/-- Frequencies in the finite support have the same parity as the Legendre degree. -/
theorem modEq_of_mem_legendreFourierSupport {n : ℕ} {k : ℤ}
    (hk : k ∈ legendreFourierSupport n) : k ≡ (n : ℤ) [ZMOD 2] := by
  by_contra h
  exact legendreFourierWeight_ne_zero_of_mem hk
    (legendreFourierWeight_eq_zero_of_not_modEq n k h)

private lemma legendreLaurent_eq_sum (n : ℕ) : diagonalLegendreLaurent n 1 =
    ∑ k ∈ legendreFourierSupport n, LaurentPolynomial.C (legendreFourierWeight n k) *
      LaurentPolynomial.T k := by
  simp_rw [← LaurentPolynomial.single_eq_C_mul_T]
  exact (AddMonoidAlgebra.sum_coeff_single (diagonalLegendreLaurent n 1)).symm

/-- The exact finite cosine expansion of `Pₙ(cos θ)` in Mathlib's shifted convention. -/
theorem shiftedLegendre_eval_cos_eq_fourier_sum (n : ℕ) (θ : ℝ) :
    (shiftedLegendre n).eval₂ (Int.castRingHom ℝ) ((1 - Real.cos θ) / 2) =
      ∑ k ∈ legendreFourierSupport n, legendreFourierWeight n k * Real.cos ((k : ℝ) * θ) := by
  let z : ℂˣ := Units.mk0 (Complex.exp ((θ : ℂ) * Complex.I)) (Complex.exp_ne_zero _)
  let e := LaurentPolynomial.eval₂ Complex.ofRealHom z
  have hT (k : ℤ) : e (LaurentPolynomial.T k) =
      Complex.exp (((k : ℝ) * θ : ℝ) * Complex.I) := by
    dsimp only [e]
    rw [LaurentPolynomial.eval₂_T, Units.val_zpow_eq_zpow_val]
    change Complex.exp ((θ : ℂ) * Complex.I) ^ k = _
    rw [← Complex.exp_int_mul, Complex.ofReal_mul, Complex.ofReal_intCast]
    congr 1
    ring
  have hC (x : ℝ) : e (LaurentPolynomial.C x) = (x : ℂ) := by
    exact LaurentPolynomial.eval₂_C _ _ _
  have harg : e (shiftedDiagonalArgument 1) = ((1 - Real.cos θ) / 2 : ℝ) := by
    rw [shiftedDiagonalArgument, map_mul, map_sub, map_sub, hC, hT, hT]
    simp only [map_ofNat, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul,
      Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Complex.ofReal_sub, Complex.ofReal_div]
    norm_num <;> ring
  have hhom : e.comp (LaurentPolynomial.C.comp (Int.castRingHom ℝ)) = Int.castRingHom ℂ :=
    Subsingleton.elim _ _
  have hhom' : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ :=
    Subsingleton.elim _ _
  have heval : e (diagonalLegendreLaurent n 1) =
      Complex.ofReal ((shiftedLegendre n).eval₂ (Int.castRingHom ℝ) ((1 - Real.cos θ) / 2)) := by
    rw [diagonalLegendreLaurent, Polynomial.hom_eval₂, hhom, harg]
    change _ = Complex.ofRealHom ((shiftedLegendre n).eval₂ (Int.castRingHom ℝ) _)
    rw [Polynomial.hom_eval₂, hhom'] <;> rfl
  have h := congrArg e (legendreLaurent_eq_sum n)
  change e (diagonalLegendreLaurent n 1) = e (∑ k ∈ legendreFourierSupport n,
    LaurentPolynomial.C (legendreFourierWeight n k) * LaurentPolynomial.T k) at h
  rw [heval, map_sum] at h
  have hterm (k : ℤ) : (e (LaurentPolynomial.C (legendreFourierWeight n k) *
      LaurentPolynomial.T k)).re = legendreFourierWeight n k * Real.cos ((k : ℝ) * θ) := by
    rw [map_mul, hC, hT, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
  simpa only [Complex.ofReal_re, Complex.re_sum, hterm] using congrArg Complex.re h

/-- The finite Fourier weights have total mass one. -/
theorem sum_legendreFourierWeight (n : ℕ) :
    (∑ k ∈ legendreFourierSupport n, legendreFourierWeight n k) = 1 := by
  have h := shiftedLegendre_eval_cos_eq_fourier_sum n 0
  rw [Real.cos_zero, sub_self, zero_div, eval₂_at_zero, coeff_shiftedLegendre] at h
  simpa using h.symm

end Zalcman
