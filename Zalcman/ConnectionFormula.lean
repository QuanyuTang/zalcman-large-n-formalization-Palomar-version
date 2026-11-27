/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.LegendreOrthogonality
public import Zalcman.LegendreFourier
import Zalcman.ConnectionBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Chebyshev–Legendre connection coefficients

The polynomial identities use the shifted variable `x = (1 - t) / 2`, so the
orthogonality integrals are over `[0, 1]`. The resulting coefficients are those
of `U_M(t)` in the ordinary Legendre basis. The finite cosine expansion gives
their exact weighted kernel formula and parity support.
-/

@[expose] public section

noncomputable section

namespace Zalcman

open Polynomial Finset
open scoped LaurentPolynomial

/-- The shifted Legendre polynomial viewed over the reals. -/
def shiftedLegendreReal (n : ℕ) : ℝ[X] := (shiftedLegendre n).map (Int.castRingHom ℝ)

/-- The Chebyshev polynomial of the second kind in the same shifted variable. -/
def shiftedChebyshevU (M : ℕ) : ℝ[X] :=
  (Polynomial.Chebyshev.U ℝ (M : ℤ)).comp (1 - C (2 : ℝ) * X)

/-- Orthogonal projection onto the shifted Legendre polynomial of degree `n`. -/
def connectionCoefficient (M n : ℕ) : ℝ :=
  (2 * (n : ℝ) + 1) * ∫ x in (0 : ℝ)..1,
    (shiftedChebyshevU M).eval x * (shiftedLegendreReal n).eval x

private lemma degree_shiftedLegendreReal (n : ℕ) : (shiftedLegendreReal n).degree = n := by
  rw [shiftedLegendreReal, degree_map_eq_of_injective Int.cast_injective, degree_shiftedLegendre]

private lemma degree_affine : ((1 : ℝ[X]) - C (2 : ℝ) * X).degree = 1 := by
  have h := degree_C_mul_X (show (2 : ℝ) ≠ 0 by norm_num)
  rw [degree_sub_eq_right_of_degree_lt (by rw [h]; simp), h]

private lemma degree_shiftedChebyshevU (M : ℕ) : (shiftedChebyshevU M).degree = M := by
  rw [shiftedChebyshevU, degree_comp (by rw [degree_affine]; simp),
    Polynomial.Chebyshev.degree_U_natCast, degree_affine, mul_one]

private def shiftedLegendreSequence : Polynomial.Sequence ℝ :=
  ⟨shiftedLegendreReal, degree_shiftedLegendreReal⟩

private lemma shiftedLegendre_inner (i n : ℕ) :
    (∫ x in (0 : ℝ)..1, (shiftedLegendreReal i).eval x * (shiftedLegendreReal n).eval x) =
      if i = n then 1 / (2 * (n : ℝ) + 1) else 0 := by
  by_cases h : i = n
  · subst i
    simpa [shiftedLegendreReal, pow_two] using integral_shiftedLegendre_sq n
  · rw [ite_eq_right h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have ho := integral_shiftedLegendre_mul_eq_zero (n := n) (Q := shiftedLegendreReal i)
        (by rw [degree_shiftedLegendreReal]; exact_mod_cast hlt)
      simpa only [shiftedLegendreReal, mul_comm] using ho
    · have ho := integral_shiftedLegendre_mul_eq_zero (n := i) (Q := shiftedLegendreReal n)
        (by rw [degree_shiftedLegendreReal]; exact_mod_cast hgt)
      simpa only [shiftedLegendreReal] using ho

/-- A degree above `M` has zero Chebyshev–Legendre connection coefficient. -/
theorem connectionCoefficient_eq_zero_of_lt {M n : ℕ} (h : M < n) :
    connectionCoefficient M n = 0 := by
  have hdegree : (shiftedChebyshevU M).degree < n := by
    rw [degree_shiftedChebyshevU]
    exact_mod_cast h
  have hz := integral_shiftedLegendre_mul_eq_zero (n := n) hdegree
  have hz' : (∫ x in (0 : ℝ)..1,
      (shiftedChebyshevU M).eval x * (shiftedLegendreReal n).eval x) = 0 := by
    simpa only [shiftedLegendreReal, mul_comm] using hz
  simp only [connectionCoefficient, hz', mul_zero]

/-- The coefficients defined by the orthogonality integral give the exact polynomial expansion. -/
theorem shiftedChebyshevU_eq_legendre_sum (M : ℕ) : shiftedChebyshevU M =
    ∑ n ∈ range (M + 1), C (connectionCoefficient M n) * shiftedLegendreReal n := by
  let L := shiftedLegendreSequence
  have hspan : Submodule.span ℝ (L '' (range (M + 1) : Set ℕ)) = degreeLT ℝ (M + 1) := by
    rw [Finset.coe_range]
    apply L.span_degreeLT
    intro i _
    exact isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (L.ne_zero i))
  have hmem : shiftedChebyshevU M ∈ Submodule.span ℝ (L '' (range (M + 1) : Set ℕ)) := by
    rw [hspan, mem_degreeLT, degree_shiftedChebyshevU]
    exact_mod_cast Nat.lt_succ_self M
  obtain ⟨a, ha⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' (R := ℝ)).mp hmem
  change (∑ i ∈ range (M + 1), a i • shiftedLegendreReal i) = shiftedChebyshevU M at ha
  have hcoeff (n : ℕ) (hn : n ∈ range (M + 1)) : connectionCoefficient M n = a n := by
    have hproj : (∫ x in (0 : ℝ)..1,
        (shiftedChebyshevU M).eval x * (shiftedLegendreReal n).eval x) =
        a n * (1 / (2 * (n : ℝ) + 1)) := by
      calc
        _ = ∫ x in (0 : ℝ)..1, ∑ i ∈ range (M + 1),
            a i * ((shiftedLegendreReal i).eval x * (shiftedLegendreReal n).eval x) := by
          apply intervalIntegral.integral_congr
          intro x _
          change (shiftedChebyshevU M).eval x * (shiftedLegendreReal n).eval x =
            ∑ i ∈ range (M + 1), a i * ((shiftedLegendreReal i).eval x * (shiftedLegendreReal n).eval x)
          have he := congrArg (fun p : ℝ[X] ↦ p.eval x) ha
          change (∑ i ∈ range (M + 1), a i • shiftedLegendreReal i).eval x =
            (shiftedChebyshevU M).eval x at he
          rw [eval_finsetSum] at he
          rw [← he, Finset.sum_mul]
          simp only [eval_smul, smul_eq_mul, mul_assoc]
        _ = ∑ i ∈ range (M + 1), a i * (if i = n then 1 / (2 * (n : ℝ) + 1) else 0) := by
          rw [intervalIntegral.integral_finsetSum]
          · simp only [intervalIntegral.integral_const_mul, shiftedLegendre_inner]
          · intro i _
            exact (((shiftedLegendreReal i).continuous.mul
              (shiftedLegendreReal n).continuous).const_mul (a i)).intervalIntegrable _ _
        _ = _ := by
          rw [Finset.sum_eq_single_of_mem n hn]
          · simp
          · intro i _ hi
            simp [hi]
    rw [connectionCoefficient, hproj]
    field_simp [show 2 * (n : ℝ) + 1 ≠ 0 by positivity] <;> ring
  rw [← ha]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [hcoeff n hn, C_mul']

private lemma shiftedCheb_eval_cos_times_sin (M : ℕ) (θ : ℝ) :
    (shiftedChebyshevU M).eval ((1 - Real.cos θ) / 2) * Real.sin θ =
      Real.sin (((M : ℝ) + 1) * θ) := by
  have he : ((1 : ℝ[X]) - C (2 : ℝ) * X).eval ((1 - Real.cos θ) / 2) = Real.cos θ := by
    simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]
    ring
  rw [shiftedChebyshevU, eval_comp, he]
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using
    Polynomial.Chebyshev.U_real_cos θ (M : ℤ)

private lemma shiftedLegendre_eval_cos_times_fourier (n : ℕ) (θ : ℝ) :
    (shiftedLegendreReal n).eval ((1 - Real.cos θ) / 2) =
      ∑ k ∈ legendreFourierSupport n, legendreFourierWeight n k * Real.cos ((k : ℝ) * θ) := by
  rw [shiftedLegendreReal, eval_map]
  exact shiftedLegendre_eval_cos_eq_fourier_sum n θ

private lemma chebyshevLegendre_inner_fourier (M n : ℕ) :
    (∫ x in (0 : ℝ)..1, (shiftedChebyshevU M).eval x * (shiftedLegendreReal n).eval x) =
      (1 / 2 : ℝ) * ∑ k ∈ legendreFourierSupport n, legendreFourierWeight n k *
        ∫ θ in (0 : ℝ)..Real.pi, Real.sin (((M : ℝ) + 1) * θ) * Real.cos ((k : ℝ) * θ) := by
  let u (θ : ℝ) := (1 - Real.cos θ) / 2
  let g (x : ℝ) := (shiftedChebyshevU M).eval x * (shiftedLegendreReal n).eval x
  have hu (θ : ℝ) : HasDerivAt u (Real.sin θ / 2) θ := by
    have h := ((hasDerivAt_const θ (1 : ℝ)).fun_sub (Real.hasDerivAt_cos θ)).div_const (2 : ℝ)
    simpa only [u, zero_sub, neg_neg] using h
  have hcont : Continuous (fun θ : ℝ ↦ Real.sin θ / 2) := by fun_prop
  have hg : Continuous g := (shiftedChebyshevU M).continuous.mul (shiftedLegendreReal n).continuous
  have hchange := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := Real.pi)
    (fun θ _ ↦ hu θ) hcont.continuousOn hg
  have h0 : u 0 = 0 := by simp [u]
  have hπ : u Real.pi = 1 := by norm_num [u, Real.cos_pi]
  change (∫ θ in (0 : ℝ)..Real.pi, g (u θ) * (Real.sin θ / 2)) =
    ∫ θ in u 0..u Real.pi, g θ at hchange
  rw [h0, hπ] at hchange
  change (∫ x in (0 : ℝ)..1, g x) = _
  rw [← hchange]
  calc
    _ = ∫ θ in (0 : ℝ)..Real.pi, (1 / 2 : ℝ) * ∑ k ∈ legendreFourierSupport n,
        legendreFourierWeight n k * (Real.sin (((M : ℝ) + 1) * θ) * Real.cos ((k : ℝ) * θ)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only [g, u]
      rw [show (shiftedChebyshevU M).eval ((1 - Real.cos θ) / 2) *
          (shiftedLegendreReal n).eval ((1 - Real.cos θ) / 2) * (Real.sin θ / 2) =
        (1 / 2 : ℝ) * (((shiftedChebyshevU M).eval ((1 - Real.cos θ) / 2) * Real.sin θ) *
          (shiftedLegendreReal n).eval ((1 - Real.cos θ) / 2)) by ring,
        shiftedCheb_eval_cos_times_sin, shiftedLegendre_eval_cos_times_fourier, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
      · simp only [intervalIntegral.integral_const_mul]
      · intro k _
        exact (show Continuous (fun θ : ℝ ↦ legendreFourierWeight n k *
          (Real.sin (((M : ℝ) + 1) * θ) * Real.cos ((k : ℝ) * θ))) by fun_prop).intervalIntegrable _ _

private lemma integral_sin_integer_freq (j : ℤ) (hj : 0 < j) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin ((j : ℝ) * θ)) =
      if Odd j then 2 / (j : ℝ) else 0 := by
  have hne : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  let m := j.toNat
  have hm : (m : ℤ) = j := Int.toNat_of_nonneg hj.le
  have hcast : (j : ℝ) = (m : ℝ) := by exact_mod_cast hm.symm
  have hcos : Real.cos ((j : ℝ) * Real.pi) = (-1 : ℝ) ^ m := by rw [hcast, Real.cos_nat_mul_pi]
  rw [intervalIntegral.integral_comp_mul_left Real.sin hne, integral_sin, mul_zero,
    Real.cos_zero, smul_eq_mul, hcos]
  by_cases hodd : Odd j
  · have hm' : Odd m := (Int.odd_coe_nat m).mp (by simpa only [hm] using hodd)
    rw [ite_eq_left hodd, hm'.neg_one_pow]
    ring
  · have hm' : Even m := by
      by_contra he
      exact hodd (by simpa only [hm] using (Int.odd_coe_nat m).mpr (Nat.not_even_iff_odd.mp he))
    rw [ite_eq_right hodd, hm'.neg_one_pow, sub_self, mul_zero]

private lemma integral_sin_cos_kernel (a k : ℤ) {good : Prop} [Decidable good]
    (hminus : 0 < a - k) (hplus : 0 < a + k)
    (hodd₁ : Odd (a - k) ↔ good) (hodd₂ : Odd (a + k) ↔ good) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin ((a : ℝ) * θ) * Real.cos ((k : ℝ) * θ)) =
      if good then 2 * ((a : ℝ) / ((a : ℝ) ^ 2 - (k : ℝ) ^ 2)) else 0 := by
  have hI (j : ℤ) : IntervalIntegrable (fun θ : ℝ ↦ Real.sin ((j : ℝ) * θ))
      MeasureTheory.volume 0 Real.pi :=
    (show Continuous (fun θ : ℝ ↦ Real.sin ((j : ℝ) * θ)) by fun_prop).intervalIntegrable _ _
  calc
    _ = ∫ θ in (0 : ℝ)..Real.pi, (1 / 2 : ℝ) *
          (Real.sin (((a - k : ℤ) : ℝ) * θ) + Real.sin (((a + k : ℤ) : ℝ) * θ)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      change Real.sin ((a : ℝ) * θ) * Real.cos ((k : ℝ) * θ) = (1 / 2 : ℝ) *
        (Real.sin (((a - k : ℤ) : ℝ) * θ) + Real.sin (((a + k : ℤ) : ℝ) * θ))
      rw [Int.cast_sub, Int.cast_add, sub_mul, add_mul]
      nlinarith only [Real.two_mul_sin_mul_cos ((a : ℝ) * θ) ((k : ℝ) * θ)]
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hI (a - k)) (hI (a + k)),
        integral_sin_integer_freq _ hminus, integral_sin_integer_freq _ hplus]
      by_cases hg : good
      · simp only [ite_eq_left (hodd₁.mpr hg), ite_eq_left (hodd₂.mpr hg), ite_eq_left hg,
          Int.cast_sub, Int.cast_add]
        have hmn : 0 < (a : ℝ) - (k : ℝ) := by exact_mod_cast hminus
        have hpl : 0 < (a : ℝ) + (k : ℝ) := by exact_mod_cast hplus
        have hd : (a : ℝ) ^ 2 - (k : ℝ) ^ 2 ≠ 0 := by
          rw [sq_sub_sq]
          exact (mul_pos hpl hmn).ne'
        field_simp [hmn.ne', hpl.ne', hd] <;> ring
      · have h₁ : ¬ Odd (a - k) := fun ho ↦ hg (hodd₁.mp ho)
        have h₂ : ¬ Odd (a + k) := fun ho ↦ hg (hodd₂.mp ho)
        simp only [ite_eq_right h₁, ite_eq_right h₂, ite_eq_right hg, add_zero, mul_zero]

private lemma integral_sin_cos_chebyshev_frequency {M n : ℕ} (hnM : n ≤ M) {k : ℤ}
    (hk : k ∈ legendreFourierSupport n) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin (((M : ℝ) + 1) * θ) * Real.cos ((k : ℝ) * θ)) =
      if (M : ℤ) ≡ (n : ℤ) [ZMOD 2] then
        2 * (((M : ℝ) + 1) / (((M : ℝ) + 1) ^ 2 - (k : ℝ) ^ 2)) else 0 := by
  have hmod := modEq_of_mem_legendreFourierSupport hk
  obtain ⟨hklo, hkhi⟩ := abs_le.mp (abs_le_of_mem_legendreFourierSupport hk)
  have hlo : -(n : ℤ) ≤ k := by exact_mod_cast hklo
  have hhi : k ≤ (n : ℤ) := by exact_mod_cast hkhi
  have hMn : (n : ℤ) ≤ M := by exact_mod_cast hnM
  let a : ℤ := (M : ℤ) + 1
  have hm : 0 < a - k := by dsimp only [a]; omega
  have hp : 0 < a + k := by dsimp only [a]; omega
  have hodd₁ : Odd (a - k) ↔ (M : ℤ) ≡ (n : ℤ) [ZMOD 2] := by
    simp only [a, Int.odd_iff, Int.ModEq] at hmod ⊢
    omega
  have hodd₂ : Odd (a + k) ↔ (M : ℤ) ≡ (n : ℤ) [ZMOD 2] := by
    simp only [a, Int.odd_iff, Int.ModEq] at hmod ⊢
    omega
  simpa only [a, Int.cast_add, Int.cast_natCast, Int.cast_one] using
    integral_sin_cos_kernel a k hm hp hodd₁ hodd₂

/-- The exact Chebyshev–Legendre connection formula and the parity restriction. -/
theorem connectionCoefficient_eq_fourierAverage {M n : ℕ} (hnM : n ≤ M) :
    connectionCoefficient M n = if (M : ℤ) ≡ (n : ℤ) [ZMOD 2] then
      (2 * (n : ℝ) + 1) * ∑ k ∈ legendreFourierSupport n, legendreFourierWeight n k *
        (((M : ℝ) + 1) / (((M : ℝ) + 1) ^ 2 - (k : ℝ) ^ 2)) else 0 := by
  rw [connectionCoefficient, chebyshevLegendre_inner_fourier]
  by_cases hmod : (M : ℤ) ≡ (n : ℤ) [ZMOD 2]
  · rw [ite_eq_left hmod]
    calc
      _ = (2 * (n : ℝ) + 1) * ((1 / 2 : ℝ) * ∑ k ∈ legendreFourierSupport n,
        2 * (legendreFourierWeight n k * (((M : ℝ) + 1) /
          (((M : ℝ) + 1) ^ 2 - (k : ℝ) ^ 2)))) := by
        congr 2
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        rw [integral_sin_cos_chebyshev_frequency hnM hk, ite_eq_left hmod]
        ring
      _ = _ := by rw [← Finset.mul_sum]; ring
  · rw [ite_eq_right hmod]
    have hz : (∑ k ∈ legendreFourierSupport n, legendreFourierWeight n k *
        ∫ θ in (0 : ℝ)..Real.pi, Real.sin (((M : ℝ) + 1) * θ) * Real.cos ((k : ℝ) * θ)) = 0 := by
      refine Finset.sum_eq_zero fun k hk ↦ ?_
      rw [integral_sin_cos_chebyshev_frequency hnM hk, ite_eq_right hmod, mul_zero]
    rw [hz, mul_zero, mul_zero]

/-- The connection coefficient vanishes whenever the degrees have unequal parity. -/
theorem connectionCoefficient_eq_zero_of_not_modEq (M n : ℕ)
    (h : ¬ (M : ℤ) ≡ (n : ℤ) [ZMOD 2]) : connectionCoefficient M n = 0 := by
  rcases le_or_gt n M with hnM | hnM
  · rw [connectionCoefficient_eq_fourierAverage hnM, ite_eq_right h]
  · exact connectionCoefficient_eq_zero_of_lt hnM

private lemma shiftedChebyshevU_coeff_degree (n : ℕ) :
    (shiftedChebyshevU n).coeff n = (-1 : ℝ) ^ n * (4 : ℝ) ^ n := by
  have hdegree : (shiftedChebyshevU n).natDegree = n :=
    natDegree_eq_of_degree_eq_some (degree_shiftedChebyshevU n)
  have haff : ((1 : ℝ[X]) - C (2 : ℝ) * X).natDegree = 1 :=
    natDegree_eq_of_degree_eq_some degree_affine
  have hlead : ((1 : ℝ[X]) - C (2 : ℝ) * X).leadingCoeff = -2 := by
    rw [← coeff_natDegree, haff, coeff_sub, coeff_C_mul_X]
    simp [coeff_one]
  calc
    _ = (shiftedChebyshevU n).leadingCoeff := by rw [← coeff_natDegree, hdegree]
    _ = (2 : ℝ) ^ n * (-2 : ℝ) ^ n := by
      rw [shiftedChebyshevU, leadingCoeff_comp (by rw [haff]; decide),
        Polynomial.Chebyshev.leadingCoeff_U_natCast, Polynomial.Chebyshev.natDegree_U_natCast, hlead]
    _ = _ := by rw [← mul_pow (2 : ℝ) (-2), ← mul_pow (-1 : ℝ) 4]; norm_num

private lemma shiftedLegendreReal_coeff_degree (n : ℕ) :
    (shiftedLegendreReal n).coeff n = (-1 : ℝ) ^ n * ((2 * n).choose n : ℝ) := by
  rw [shiftedLegendreReal, coeff_map, coeff_shiftedLegendre]
  simp [two_mul]

/-- The diagonal connection coefficient is the ratio of the two leading coefficients. -/
theorem connectionCoefficient_diagonal (n : ℕ) :
    connectionCoefficient n n = (4 : ℝ) ^ n / ((2 * n).choose n : ℝ) := by
  have h := congrArg (fun p : ℝ[X] ↦ p.coeff n) (shiftedChebyshevU_eq_legendre_sum n)
  change (shiftedChebyshevU n).coeff n =
    (∑ i ∈ range (n + 1), C (connectionCoefficient n i) * shiftedLegendreReal i).coeff n at h
  rw [finsetSum_coeff, Finset.sum_eq_single_of_mem n (mem_range.mpr (Nat.lt_succ_self n))] at h
  · rw [shiftedChebyshevU_coeff_degree, coeff_C_mul, shiftedLegendreReal_coeff_degree] at h
    have hchoose : ((2 * n).choose n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : n ≤ 2 * n)).ne'
    apply (eq_div_iff_mul_eq hchoose).mpr
    apply mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0))
    linear_combination -h
  · intro i hi hne
    have hlt : i < n := lt_of_le_of_ne (Nat.le_of_lt_succ (mem_range.mp hi)) hne
    have hz : (shiftedLegendreReal i).coeff n = 0 :=
      coeff_eq_zero_of_degree_lt (by rw [degree_shiftedLegendreReal]; exact_mod_cast hlt)
    rw [coeff_C_mul, hz, mul_zero]

/-- All entries of the triangular Chebyshev–Legendre connection matrix are nonnegative. -/
theorem connectionCoefficient_nonneg (M n : ℕ) : 0 ≤ connectionCoefficient M n := by
  rcases le_or_gt n M with hnM | hnM
  · rw [connectionCoefficient_eq_fourierAverage hnM]
    by_cases hp : (M : ℤ) ≡ (n : ℤ) [ZMOD 2]
    · rw [ite_eq_left hp]
      apply mul_nonneg (by positivity)
      refine Finset.sum_nonneg fun k hk ↦ mul_nonneg (legendreFourierWeight_nonneg n k) ?_
      have ha : (n : ℝ) < (M : ℝ) + 1 := by exact_mod_cast Nat.lt_succ_of_le hnM
      have ht := pow_lt_pow_left₀ ((abs_le_of_mem_legendreFourierSupport hk).trans_lt ha)
        (abs_nonneg (k : ℝ)) (by decide : (2 : ℕ) ≠ 0)
      rw [sq_abs] at ht
      exact div_nonneg (by positivity) (sub_nonneg.mpr ht.le)
    · rw [ite_eq_right hp]
  · rw [connectionCoefficient_eq_zero_of_lt hnM]

/-- The Chebyshev Laurent polynomial at the exact argument of the radial weights. -/
def chebyshevRadialLaurent (M : ℕ) (q : ℝ) : ℝ[T;T⁻¹] :=
  (Polynomial.Chebyshev.U ℝ (M : ℤ)).eval₂ LaurentPolynomial.C
    (LaurentPolynomial.C (1 - q) + LaurentPolynomial.C (q / 2) *
      (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)))

private lemma shiftedDiagonal_affine_argument (q : ℝ) :
    ((1 : ℝ[X]) - C (2 : ℝ) * X).eval₂ LaurentPolynomial.C (shiftedDiagonalArgument q) =
      LaurentPolynomial.C (1 - q) + LaurentPolynomial.C (q / 2) *
        (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) := by
  have hscale : LaurentPolynomial.C (2 : ℝ) * LaurentPolynomial.C (q / 4) =
      LaurentPolynomial.C (q / 2) := by
    rw [← map_mul]
    congr 1
    ring
  have hconst : 1 - LaurentPolynomial.C (q / 2) * 2 =
      (LaurentPolynomial.C (1 - q) : ℝ[T;T⁻¹]) := by
    calc
      _ = LaurentPolynomial.C (1 - (q / 2) * 2) := by simp only [map_sub, map_one, map_mul, map_ofNat]
      _ = _ := by congr 1; ring
  rw [eval₂_sub, eval₂_one, eval₂_mul, eval₂_C, eval₂_X, shiftedDiagonalArgument,
    ← mul_assoc, hscale]
  rw [show (1 : ℝ[T;T⁻¹]) - LaurentPolynomial.C (q / 2) *
      (2 - LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) =
    (1 - LaurentPolynomial.C (q / 2) * 2) + LaurentPolynomial.C (q / 2) *
      (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) by ring, hconst]

/-- Substitution gives the exact Chebyshev–Legendre expansion in the Laurent ring. -/
theorem chebyshevRadialLaurent_eq_legendre_sum (M : ℕ) (q : ℝ) :
    chebyshevRadialLaurent M q = ∑ n ∈ range (M + 1),
      LaurentPolynomial.C (connectionCoefficient M n) * diagonalLegendreLaurent n q := by
  have h := congrArg (fun p : ℝ[X] ↦ p.eval₂ LaurentPolynomial.C (shiftedDiagonalArgument q))
    (shiftedChebyshevU_eq_legendre_sum M)
  simpa only [shiftedChebyshevU, eval₂_comp, shiftedDiagonal_affine_argument,
    chebyshevRadialLaurent, eval₂_finsetSum, eval₂_mul, eval₂_C,
    shiftedLegendreReal, eval₂_map, diagonalLegendreLaurent] using h

/-- The coefficient identity for the common positive triangular basis. -/
theorem chebyshevRadialLaurent_coeff_eq_legendre_sum (M : ℕ) (q : ℝ) (k : ℤ) :
    (chebyshevRadialLaurent M q).coeff k = ∑ n ∈ range (M + 1),
      connectionCoefficient M n * (diagonalLegendreLaurent n q).coeff k := by
  rw [chebyshevRadialLaurent_eq_legendre_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  change (AddMonoidAlgebra.single 0 (connectionCoefficient M n) *
    diagonalLegendreLaurent n q).coeff k = _
  simpa only [zero_add] using AddMonoidAlgebra.coeff_single_mul_add
    (diagonalLegendreLaurent n q) (connectionCoefficient M n) (0 : ℤ) k

/-- The two-sided bounds for a Chebyshev–Legendre coefficient of matching parity. -/
theorem connectionCoefficient_bounds {M n : ℕ} (hnM : n ≤ M)
    (hpar : (M : ℤ) ≡ (n : ℤ) [ZMOD 2]) :
    (2 * (n : ℝ) + 1) / ((M : ℝ) + 1) ≤ connectionCoefficient M n ∧
      connectionCoefficient M n ≤ (2 * (n : ℝ) + 1) / ((M : ℝ) + 1 - n) := by
  rw [connectionCoefficient_eq_fourierAverage hnM, ite_eq_left hpar]
  simpa only [connectionAverage] using
    connectionAverage_bounds (legendreFourierSupport n) (legendreFourierWeight n) hnM
      (fun k _ ↦ legendreFourierWeight_nonneg n k) (sum_legendreFourierWeight n)
      (fun _ hk ↦ abs_le_of_mem_legendreFourierSupport hk)

/-- The upper bound for connection coefficients uniform in the upper degree. -/
theorem connectionCoefficient_le_two_sqrt (M n : ℕ) :
    connectionCoefficient M n ≤ 2 * Real.sqrt ((n : ℝ) + 1) := by
  by_cases hnM : n ≤ M
  · by_cases hpar : (M : ℤ) ≡ (n : ℤ) [ZMOD 2]
    · have hd := connectionCoefficient_diagonal n
      rw [connectionCoefficient_eq_fourierAverage le_rfl, ite_eq_left (Int.ModEq.refl _)] at hd
      rw [connectionCoefficient_eq_fourierAverage hnM, ite_eq_left hpar]
      simpa only [connectionAverage] using
        connectionAverage_le_two_sqrt_succ (legendreFourierSupport n) (legendreFourierWeight n) hnM
          (fun k _ ↦ legendreFourierWeight_nonneg n k)
          (fun _ hk ↦ abs_le_of_mem_legendreFourierSupport hk)
          (by simpa only [connectionAverage] using hd)
    · rw [connectionCoefficient_eq_zero_of_not_modEq _ _ hpar]
      positivity
  · rw [connectionCoefficient_eq_zero_of_lt (lt_of_not_ge hnM)]
    positivity

end Zalcman
