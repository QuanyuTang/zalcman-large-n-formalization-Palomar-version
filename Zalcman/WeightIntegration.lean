/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.WeightDerivative
public import Zalcman.ConnectionFormula
public import Zalcman.Milin
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integrating the de Branges–Weinstein energy

The Koebe endpoint makes the weighted energy zero. Its initial value is the
negative Milin sum. The Legendre expansion then yields one nonnegative
triangular representation with weights shared across all rows.
-/

public section

noncomputable section

namespace Zalcman

open Finset MeasureTheory Set
open scoped BigOperators LaurentPolynomial

private lemma norm_succ_natCast_complex (k : ℕ) : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
  rw [← Nat.cast_succ (R := ℂ), Complex.norm_natCast, Nat.cast_succ]

private lemma absolutelyContinuousOnInterval_const (r a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ r) a b :=
  (LipschitzWith.const r).lipschitzOnWith.absolutelyContinuousOnInterval

private lemma absolutelyContinuousOnInterval_finsetSum (s : Finset ℕ) (f : ℕ → ℝ → ℝ)
    {a b : ℝ} (h : ∀ k ∈ s, AbsolutelyContinuousOnInterval (f k) a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∑ k ∈ s, f k t) a b := by
  induction s using Finset.induction_on with
  | empty => simpa using absolutelyContinuousOnInterval_const 0 a b
  | insert i s hi ih =>
    have hhead := h i (mem_insert_self i s)
    have htail := ih (fun k hk ↦ h k (mem_insert_of_mem hk))
    simpa only [sum_insert hi] using hhead.fun_add htail

/-- The weighted energy is absolutely continuous if its coefficient and weight paths are. -/
theorem absolutelyContinuousOnInterval_weightedLogEnergy (γ : ℕ → ℝ → ℂ)
    (τ : ℕ → ℝ → ℝ) (M : ℕ) {a b : ℝ}
    (hγ : ∀ k < M, AbsolutelyContinuousOnInterval (γ k) a b)
    (hτ : ∀ k < M, AbsolutelyContinuousOnInterval (τ k) a b) :
    AbsolutelyContinuousOnInterval (weightedLogEnergy γ τ M) a b := by
  unfold weightedLogEnergy
  refine absolutelyContinuousOnInterval_finsetSum (range M) _ fun k hk ↦ ?_
  have hnormLip : LipschitzOnWith 1 (norm : ℂ → ℝ) Set.univ :=
    lipschitzWith_one_norm.lipschitzOnWith
  have hnorm : AbsolutelyContinuousOnInterval (fun t ↦ ‖γ k t‖) a b :=
    hnormLip.comp_absolutelyContinuousOnInterval (mapsTo_univ _ _) (hγ k (mem_range.mp hk))
  have hsq : AbsolutelyContinuousOnInterval (fun t ↦ ‖γ k t‖ ^ 2) a b := by
    simpa only [pow_two] using hnorm.fun_mul hnorm
  exact (hτ k (mem_range.mp hk)).fun_mul
    ((hsq.const_mul ((k : ℝ) + 1)).fun_sub
      (absolutelyContinuousOnInterval_const (1 / ((k : ℝ) + 1)) a b))

/-- The energy at the initial time equals the negative Milin sum. -/
theorem weightedLogEnergy_zero_eq_neg_milinSum (c : MilinCoefficients)
    (γ : ℕ → ℝ → ℂ) (τ : ℕ → ℝ → ℝ) (M : ℕ)
    (hτ : ∀ k < M, τ k 0 = (M : ℝ) - k)
    (hγ : ∀ k < M, c.t (k + 1) = ((k : ℂ) + 1) * γ k 0) :
    weightedLogEnergy γ τ M 0 = -c.milinSum (M + 1) := by
  have hzero : ((↑(M + 1) : ℝ) / ((M : ℝ) + 1) - 1) * (1 - ‖c.t (M + 1)‖ ^ 2) = 0 := by
    rw [Nat.cast_succ, div_self (by positivity), sub_self, zero_mul]
  rw [weightedLogEnergy, MilinCoefficients.milinSum, sum_range_succ, hzero, add_zero,
    ← sum_neg_distrib]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk' := mem_range.mp hk
  have hk₀ : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [hτ k hk', hγ k hk', norm_mul, norm_succ_natCast_complex, mul_pow, Nat.cast_succ]
  field_simp; ring

/-- The energy vanishes at the Koebe endpoint. -/
theorem weightedLogEnergy_eq_zero_of_koebe_terminal (γ : ℕ → ℝ → ℂ) (τ : ℕ → ℝ → ℝ)
    (M : ℕ) (T : ℝ) (hγ : ∀ k < M, γ k T = ((k : ℂ) + 1)⁻¹) :
    weightedLogEnergy γ τ M T = 0 := by
  unfold weightedLogEnergy
  refine sum_eq_zero fun k hk ↦ ?_
  have hk₀ : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [hγ k (mem_range.mp hk), norm_inv, norm_succ_natCast_complex]
  field_simp; ring

/-- The integrand of row `M` in the integrated energy identity. -/
@[expose] def chebyshevEnergyRow (d : ℕ → ℝ → ℂ) (M : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ range M, (chebyshevRadialLaurent M (Real.exp (-u))).coeff
    ((k + 1 : ℕ) : ℤ) * ‖d k u‖ ^ 2

/-- A row is integrable when it is the almost everywhere derivative of an
absolutely continuous energy. -/
theorem intervalIntegrable_chebyshevEnergyRow_of_weightedLogEnergy
    (γ : ℕ → ℝ → ℂ) (τ : ℕ → ℝ → ℝ) (d : ℕ → ℝ → ℂ) (M : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hAC : AbsolutelyContinuousOnInterval (weightedLogEnergy γ τ M) 0 T)
    (hDeriv : ∀ᵐ u : ℝ ∂volume, u ∈ Set.Ioc 0 T →
      HasDerivAt (weightedLogEnergy γ τ M) (chebyshevEnergyRow d M u) u) :
    IntervalIntegrable (chebyshevEnergyRow d M) volume 0 T := by
  apply hAC.intervalIntegrable_deriv.congr_ae
  rw [Set.uIoc_of_le hT]
  exact (ae_restrict_iff' measurableSet_Ioc).2 (hDeriv.mono fun _ hU hu ↦ (hU hu).deriv)

/-- The exact integral identity on the interval ending at the Koebe continuation. -/
theorem milinSum_eq_intervalIntegral_of_weightedLogEnergy (c : MilinCoefficients)
    (γ : ℕ → ℝ → ℂ) (τ : ℕ → ℝ → ℝ) (d : ℕ → ℝ → ℂ) (M : ℕ) {T : ℝ}
    (hT : 0 ≤ T)
    (hτ : ∀ k < M, τ k 0 = (M : ℝ) - k)
    (hγ₀ : ∀ k < M, c.t (k + 1) = ((k : ℂ) + 1) * γ k 0)
    (hγT : ∀ k < M, γ k T = ((k : ℂ) + 1)⁻¹)
    (hAC : AbsolutelyContinuousOnInterval (weightedLogEnergy γ τ M) 0 T)
    (hDeriv : ∀ᵐ u : ℝ ∂volume, u ∈ Set.Ioc 0 T →
      HasDerivAt (weightedLogEnergy γ τ M) (chebyshevEnergyRow d M u) u) :
    c.milinSum (M + 1) = ∫ u in (0 : ℝ)..T, chebyshevEnergyRow d M u := by
  calc
    _ = weightedLogEnergy γ τ M T - weightedLogEnergy γ τ M 0 := by
      rw [weightedLogEnergy_eq_zero_of_koebe_terminal γ τ M T hγT,
        weightedLogEnergy_zero_eq_neg_milinSum c γ τ M hτ hγ₀, zero_sub, neg_neg]
    _ = ∫ u in (0 : ℝ)..T, deriv (weightedLogEnergy γ τ M) u :=
      hAC.integral_deriv_eq_sub.symm
    _ = _ := by
      apply intervalIntegral.integral_congr_ae
      rw [Set.uIoc_of_le hT]
      exact hDeriv.mono (fun _ hU hu ↦ (hU hu).deriv)

open Polynomial in
private lemma natDegree_clearedDiagonalLegendre_le (n : ℕ) (q : ℝ) :
    (clearedDiagonalLegendre n q).natDegree ≤ 2 * n := by
  let J : ℝ[X] := C (q / 4) * (X - 1) ^ 2
  have hX1 : ((X : ℝ[X]) - 1).natDegree ≤ 1 := by
    simpa using natDegree_sub_le (X : ℝ[X]) 1
  have hJ : J.natDegree ≤ 2 := calc
    _ ≤ (C (q / 4)).natDegree + (((X : ℝ[X]) - 1) ^ 2).natDegree :=
      natDegree_mul_le
    _ ≤ _ := by simpa using natDegree_pow_le_of_le 2 hX1
  have hXJ : ((X : ℝ[X]) + J).natDegree ≤ 2 :=
    natDegree_add_le_of_degree_le (by simp) hJ
  change (∑ i ∈ range (n + 1), C ((n.choose i : ℝ) ^ 2) * (X + J) ^ i * J ^ (n - i)).natDegree ≤ _
  refine natDegree_sum_le_of_forall_le (range (n + 1)) _ fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  calc
    _ ≤ (0 + i * 2) + (n - i) * 2 :=
      natDegree_mul_le_of_le (natDegree_mul_le_of_le (by simp) (natDegree_pow_le_of_le i hXJ))
        (natDegree_pow_le_of_le (n - i) hJ)
    _ = _ := by omega

/-- Legendre radial coefficients of positive index above the degree vanish. -/
theorem diagonalLegendreLaurent_coeff_eq_zero_of_nat_lt {n k : ℕ} (h : n < k) (q : ℝ) :
    (diagonalLegendreLaurent n q).coeff (k : ℤ) = 0 := by
  have hshift := congrArg (fun p : ℝ[T;T⁻¹] ↦ p.coeff ((n : ℤ) + k))
    (toLaurent_clearedDiagonalLegendre n q)
  have hmul : ((LaurentPolynomial.T (n : ℤ)) * diagonalLegendreLaurent n q).coeff
      ((n : ℤ) + k) = (diagonalLegendreLaurent n q).coeff k := by
    rw [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_add, one_mul]
  rw [hmul] at hshift
  rw [← hshift, LaurentPolynomial.coeff_toLaurent, ← Int.natCast_add]
  change Finsupp.mapDomain (Nat.castEmbedding : ℕ ↪ ℤ)
    (clearedDiagonalLegendre n q).toFinsupp.coeff ((Nat.castEmbedding : ℕ ↪ ℤ) (n + k)) = 0
  rw [Finsupp.mapDomain_apply_of_injective (Nat.castEmbedding : ℕ ↪ ℤ).injective,
    Polynomial.toFinsupp_apply]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    ((natDegree_clearedDiagonalLegendre_le n q).trans_lt (by omega))

/-- The integrand of a single column of the triangular Milin representation. -/
def legendreEnergyColumn (d : ℕ → ℝ → ℂ) (n : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ range n, (diagonalLegendreLaurent n (Real.exp (-u))).coeff
    ((k + 1 : ℕ) : ℤ) * ‖d k u‖ ^ 2

open Polynomial in
/-- A diagonal Laurent coefficient is a polynomial function of the radial parameter. -/
theorem continuous_diagonalLegendreLaurent_coeff (n : ℕ) (k : ℤ) :
    Continuous (fun q : ℝ ↦ (diagonalLegendreLaurent n q).coeff k) := by
  let A : ℝ[T;T⁻¹] := 2 - LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)
  have heq (q : ℝ) : (diagonalLegendreLaurent n q).coeff k =
      ∑ i ∈ (shiftedLegendre n).support, ((shiftedLegendre n).coeff i : ℝ) *
        (q / 4) ^ i * (A ^ i).coeff k := by
    rw [diagonalLegendreLaurent, eval₂_eq_sum, Polynomial.sum, AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply]
    refine sum_congr rfl fun i _ ↦ ?_
    change (LaurentPolynomial.C (((shiftedLegendre n).coeff i : ℤ) : ℝ) *
      (LaurentPolynomial.C (q / 4) * A) ^ i).coeff k = _
    rw [mul_pow, ← map_pow, ← mul_assoc, ← map_mul]
    let a : ℝ := ((shiftedLegendre n).coeff i : ℝ) * (q / 4) ^ i
    change (AddMonoidAlgebra.single (0 : ℤ) a * A ^ i).coeff k = a * (A ^ i).coeff k
    simpa only [zero_add] using AddMonoidAlgebra.coeff_single_mul_add (A ^ i) a (0 : ℤ) k
  simp_rw [heq]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  exact (continuous_const.mul ((continuous_id.div_const (4 : ℝ)).pow i)).mul continuous_const

/-- Measurable coefficient velocities give measurable Legendre energy columns. -/
theorem measurable_legendreEnergyColumn (d : ℕ → ℝ → ℂ) (hd : ∀ k, Measurable (d k))
    (n : ℕ) : Measurable (legendreEnergyColumn d n) := by
  unfold legendreEnergyColumn
  refine Finset.measurable_fun_sum _ fun k _ ↦ ?_
  exact ((continuous_diagonalLegendreLaurent_coeff n ((k + 1 : ℕ) : ℤ)).comp
    (Real.continuous_exp.comp continuous_neg)).measurable.mul ((hd k).norm.pow_const 2)

/-- Expanding, exchanging the two finite sums and using support gives the triangular expression. -/
theorem chebyshevEnergy_eq_legendreEnergy (d : ℕ → ℝ → ℂ) (M : ℕ) (u : ℝ) :
    chebyshevEnergyRow d M u =
    ∑ n ∈ range (M + 1), connectionCoefficient M n * legendreEnergyColumn d n u := by
  unfold chebyshevEnergyRow
  let q := Real.exp (-u)
  let b (n k : ℕ) := (diagonalLegendreLaurent n q).coeff ((k + 1 : ℕ) : ℤ) * ‖d k u‖ ^ 2
  calc
    _ = ∑ k ∈ range M, ∑ n ∈ range (M + 1), connectionCoefficient M n * b n k := by
      simp only [chebyshevRadialLaurent_coeff_eq_legendre_sum, sum_mul, b, q, mul_assoc]
    _ = ∑ n ∈ range (M + 1), connectionCoefficient M n * ∑ k ∈ range M, b n k := by
      rw [sum_comm]
      simp only [← mul_sum]
    _ = _ := by
      refine sum_congr rfl fun n hn ↦ congrArg (connectionCoefficient M n * ·) ?_
      have hn' := mem_range.mp hn
      unfold legendreEnergyColumn
      change (∑ k ∈ range M, b n k) = ∑ k ∈ range n, b n k
      symm
      apply sum_subset (range_mono (Nat.le_of_lt_succ hn'))
      intro k _ hk
      have hk' : n < k + 1 := by
        have hnk : ¬k < n := fun h ↦ hk (mem_range.mpr h)
        omega
      simp only [b, diagonalLegendreLaurent_coeff_eq_zero_of_nat_lt hk', zero_mul]

/-- The common integrated column is nonnegative for positive radial time. -/
theorem legendreEnergyColumn_nonneg (d : ℕ → ℝ → ℂ) (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ legendreEnergyColumn d n u := by
  have hq₁ : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
  exact sum_nonneg fun k _ ↦ mul_nonneg
    (diagonalLegendreLaurent_coeff_nonneg n ((k + 1 : ℕ) : ℤ) (Real.exp_pos _).le hq₁)
    (sq_nonneg _)

/-- Each measurable column is integrable when the row on its diagonal is
integrable. Positivity prevents cancellation in the row. -/
theorem intervalIntegrable_legendreEnergyColumn_of_row (d : ℕ → ℝ → ℂ) (n : ℕ) {T : ℝ}
    (hT : 0 ≤ T)
    (hMeas : AEStronglyMeasurable (legendreEnergyColumn d n)
      (volume.restrict (Set.uIoc 0 T)))
    (hRow : IntervalIntegrable (chebyshevEnergyRow d n) volume 0 T) :
    IntervalIntegrable (legendreEnergyColumn d n) volume 0 T := by
  have hB : 0 < connectionCoefficient n n := by
    rw [connectionCoefficient_diagonal]
    have hchoose := Nat.choose_pos (by omega : n ≤ 2 * n)
    positivity
  apply (hRow.const_mul (connectionCoefficient n n)⁻¹).mono_fun' hMeas
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  have hu₀ : 0 ≤ u := by
    rw [Set.uIoc_of_le hT] at hu
    exact hu.1.le
  have hdiag : connectionCoefficient n n * legendreEnergyColumn d n u ≤
      chebyshevEnergyRow d n u := by
    rw [chebyshevEnergy_eq_legendreEnergy]
    exact single_le_sum
      (fun i _ ↦ mul_nonneg (connectionCoefficient_nonneg n i) (legendreEnergyColumn_nonneg d i hu₀))
      (mem_range.mpr (Nat.lt_succ_self n))
  change ‖legendreEnergyColumn d n u‖ ≤ (connectionCoefficient n n)⁻¹ * chebyshevEnergyRow d n u
  rw [Real.norm_eq_abs, abs_of_nonneg (legendreEnergyColumn_nonneg d n hu₀), ← div_eq_inv_mul]
  exact (le_div_iff₀ hB).2 (by simpa only [mul_comm] using hdiag)

/-- The finite weight identities give a shared nonnegative triangular representation. -/
theorem exists_nonnegative_triangular_milin_representation_of_integral (c : MilinCoefficients)
    (d : ℕ → ℝ → ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hInt : ∀ n, IntervalIntegrable (legendreEnergyColumn d n) volume 0 T)
    (hMilin : ∀ M, c.milinSum (M + 1) = ∫ u in (0 : ℝ)..T, chebyshevEnergyRow d M u) :
    ∃ rho : ℕ → ℝ, rho 0 = 0 ∧ (∀ n, 0 ≤ rho n) ∧ ∀ M,
      (∑ n ∈ range (M + 1), connectionCoefficient M n * rho n) = c.milinSum (M + 1) := by
  let rho (n : ℕ) : ℝ := ∫ u in (0 : ℝ)..T, legendreEnergyColumn d n u
  refine ⟨rho, by simp [rho, legendreEnergyColumn], ?_, ?_⟩
  · intro n
    apply intervalIntegral.integral_nonneg hT
    intro u hu
    exact legendreEnergyColumn_nonneg d n hu.1
  · intro M
    rw [hMilin M]
    calc
      _ = ∫ u in (0 : ℝ)..T, ∑ n ∈ range (M + 1),
          connectionCoefficient M n * legendreEnergyColumn d n u := by
        rw [intervalIntegral.integral_finsetSum
          (fun n _ ↦ (hInt n).const_mul (connectionCoefficient M n))]
        simp only [intervalIntegral.integral_const_mul, rho]
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro u _
        exact (chebyshevEnergy_eq_legendreEnergy d M u).symm

/-- The first and last coefficient values and the almost everywhere energy equations give the
nonnegative triangular formula for the initial function of a chain. -/
theorem exists_nonnegative_triangular_milin_representation_of_weightedLogEnergy
    (c : MilinCoefficients) (γ d : ℕ → ℝ → ℂ) (τ : ℕ → ℕ → ℝ → ℝ) {T : ℝ}
    (hT : 0 ≤ T)
    (hτ : ∀ M k, k < M → τ M k 0 = (M : ℝ) - k)
    (hγ₀ : ∀ k, c.t (k + 1) = ((k : ℂ) + 1) * γ k 0)
    (hγT : ∀ k, γ k T = ((k : ℂ) + 1)⁻¹)
    (hAC : ∀ M, AbsolutelyContinuousOnInterval (weightedLogEnergy γ (τ M) M) 0 T)
    (hDeriv : ∀ M, ∀ᵐ u : ℝ ∂volume, u ∈ Set.Ioc 0 T →
      HasDerivAt (weightedLogEnergy γ (τ M) M) (chebyshevEnergyRow d M u) u)
    (hMeas : ∀ n, AEStronglyMeasurable (legendreEnergyColumn d n)
      (volume.restrict (Set.uIoc 0 T))) :
    ∃ rho : ℕ → ℝ, rho 0 = 0 ∧ (∀ n, 0 ≤ rho n) ∧ ∀ M,
      (∑ n ∈ range (M + 1), connectionCoefficient M n * rho n) = c.milinSum (M + 1) := by
  apply exists_nonnegative_triangular_milin_representation_of_integral c d hT
  · intro n
    exact intervalIntegrable_legendreEnergyColumn_of_row d n hT (hMeas n)
      (intervalIntegrable_chebyshevEnergyRow_of_weightedLogEnergy γ (τ n) d n hT (hAC n) (hDeriv n))
  · intro M
    exact milinSum_eq_intervalIntegral_of_weightedLogEnergy c γ (τ M) d M hT
      (hτ M) (fun k _ ↦ hγ₀ k) (fun k _ ↦ hγT k) (hAC M) (hDeriv M)

end Zalcman
