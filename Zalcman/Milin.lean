/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite Lebedev–Milin identities

The square-root and logarithmic coefficients enter this section through their derivative
recursion. The inequality for the Milin sums is a separate analytic input.
-/

@[expose] public section

noncomputable section

namespace Zalcman

open Finset
open scoped BigOperators ComplexConjugate

/-- Coefficients of a normalized Taylor series and its logarithmic derivative. -/
structure MilinCoefficients where
  /-- Coefficients of the normalized Taylor series. -/
  c : ℕ → ℂ
  /-- Coefficients of the logarithmic derivative multiplied by the series variable. -/
  t : ℕ → ℂ
  /-- The Taylor series has constant term one. -/
  c_zero : c 0 = 1
  /-- The coefficient identity obtained by multiplying the logarithmic derivative by the series. -/
  recursion (j : ℕ) : ∑ i ∈ range j, t (j - i) * c i = (j : ℂ) * c j

namespace MilinCoefficients

variable (d : MilinCoefficients)

/-- The first logarithmic derivative coefficient equals the first Taylor coefficient. -/
theorem t_one_eq_c_one : d.t 1 = d.c 1 := by
  simpa [d.c_zero] using d.recursion 1

/-- The squared mass of the first `j` Taylor coefficients. -/
def partialMass (j : ℕ) : ℝ := ∑ i ∈ range j, ‖d.c i‖ ^ 2

/-- The squared mass of the first `j` nonconstant logarithmic derivative coefficients. -/
def logMass (j : ℕ) : ℝ := ∑ i ∈ range j, ‖d.t (i + 1)‖ ^ 2

/-- The weighted deficit of the first logarithmic derivative coefficients.
The summand at `i = j - 1` has weight zero. -/
def milinSum (j : ℕ) : ℝ :=
  ∑ i ∈ range j, ((j : ℝ) / (i + 1) - 1) * (1 - ‖d.t (i + 1)‖ ^ 2)

/-- The least-squares remainder of the derivative recursion. -/
def remainder (j : ℕ) : ℝ :=
  d.logMass j - (j : ℝ) ^ 2 * ‖d.c j‖ ^ 2 / d.partialMass j

/-- The step parameter in the differences of logarithmic remainders. -/
def stepParameter (j : ℕ) : ℝ := (d.logMass j - j) / ((j : ℝ) * (j + 1))

/-- The difference between the logarithmic mass deficit and the normalized Milin sum. -/
def logRemainder (j : ℕ) : ℝ :=
  Real.log (j / d.partialMass j) - d.milinSum j / j

@[simp]
theorem partialMass_one : d.partialMass 1 = 1 := by
  simp [partialMass, d.c_zero]

theorem one_le_partialMass {j : ℕ} (hj : 0 < j) : 1 ≤ d.partialMass j := by
  rw [← d.partialMass_one]
  exact sum_le_sum_of_subset_of_nonneg
    (range_mono hj) (fun _ _ _ => sq_nonneg _)

theorem partialMass_pos {j : ℕ} (hj : 0 < j) : 0 < d.partialMass j :=
  zero_lt_one.trans_le (d.one_le_partialMass hj)

theorem partialMass_succ (j : ℕ) :
    d.partialMass (j + 1) = d.partialMass j + ‖d.c j‖ ^ 2 :=
  sum_range_succ _ _

theorem logMass_nonneg (j : ℕ) : 0 ≤ d.logMass j :=
  sum_nonneg (fun _ _ => sq_nonneg _)

@[simp]
theorem milinSum_one : d.milinSum 1 = 0 := by
  simp [milinSum]

@[simp]
theorem logRemainder_one : d.logRemainder 1 = 0 := by
  simp [logRemainder]

private theorem logMass_reverse (j : ℕ) :
    ∑ i ∈ range j, ‖d.t (j - i)‖ ^ 2 = d.logMass j := by
  calc
    _ = ∑ i ∈ range j, ‖d.t (j - 1 - i + 1)‖ ^ 2 := by
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      have heq : j - i = j - 1 - i + 1 := by omega
      rw [heq]
    _ = _ := sum_range_reflect (fun i => ‖d.t (i + 1)‖ ^ 2) j

private theorem sum_sub_conj_norm_sq (j : ℕ) (β : ℂ) :
    ∑ i ∈ range j, ‖d.t (j - i) - β * conj (d.c i)‖ ^ 2 =
      d.logMass j + ‖β‖ ^ 2 * d.partialMass j -
        2 * (conj β * ((j : ℂ) * d.c j)).re := by
  simp_rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_conj,
    map_mul, Complex.conj_conj]
  simp_rw [Complex.normSq_eq_norm_sq]
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← Complex.re_sum]
  rw [d.logMass_reverse, ← partialMass]
  congr 2
  rw [← d.recursion, mul_sum]
  apply congrArg Complex.re
  apply sum_congr rfl
  intro i _
  ring

private theorem sum_sub_real_mul_conj_norm_sq (j : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    ∑ i ∈ range j, ‖d.t (j - i) - ((v : ℂ) * d.c j) * conj (d.c i)‖ ^ 2 =
      d.logMass j + v ^ 2 * ‖d.c j‖ ^ 2 * d.partialMass j -
        2 * (v * j * ‖d.c j‖ ^ 2) := by
  rw [d.sum_sub_conj_norm_sq, norm_mul, Complex.norm_of_nonneg hv, mul_pow]
  have h : conj ((v : ℂ) * d.c j) * ((j : ℂ) * d.c j) =
      ((v * j * ‖d.c j‖ ^ 2 : ℝ) : ℂ) := by
    rw [map_mul, Complex.conj_ofReal]
    calc
      _ = (v : ℂ) * (j : ℂ) * (d.c j * conj (d.c j)) := by ring
      _ = _ := by simp [Complex.mul_conj, Complex.sq_norm]
  rw [h, Complex.ofReal_re]

/-- The norm-square representation of the least-squares remainder. -/
theorem remainder_eq_sum_norm_sq {j : ℕ} (hj : 0 < j) :
    d.remainder j = ∑ i ∈ range j,
      ‖d.t (j - i) - (((j / d.partialMass j : ℝ) : ℂ) * d.c j) * conj (d.c i)‖ ^ 2 := by
  have hmass := d.partialMass_pos hj
  rw [d.sum_sub_real_mul_conj_norm_sq _ _ (by positivity), remainder]
  field_simp
  ring

theorem remainder_nonneg {j : ℕ} (hj : 0 < j) : 0 ≤ d.remainder j := by
  rw [d.remainder_eq_sum_norm_sq hj]
  exact sum_nonneg (fun _ _ => sq_nonneg _)

theorem remainder_le_logMass {j : ℕ} (hj : 0 < j) : d.remainder j ≤ d.logMass j := by
  have hmass := d.partialMass_pos hj
  exact sub_le_self _ (by positivity)

private theorem milinSum_normalized {j : ℕ} (hj : 0 < j) :
    d.milinSum j / j = ∑ i ∈ range j,
      ((1 : ℝ) / (i + 1) - 1 / j) * (1 - ‖d.t (i + 1)‖ ^ 2) := by
  have hj' : (j : ℝ) ≠ 0 := by positivity
  simp only [milinSum, div_eq_mul_inv, sum_mul]
  apply sum_congr rfl
  intro i _
  have hi' : (i : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private theorem milinSum_normalized_sub_succ {j : ℕ} (hj : 0 < j) :
    d.milinSum j / j - d.milinSum (j + 1) / (j + 1) = d.stepParameter j := by
  have hj' : (j : ℝ) ≠ 0 := by positivity
  have hs : (j : ℝ) + 1 ≠ 0 := by positivity
  rw [d.milinSum_normalized hj,
    ← Nat.cast_succ (R := ℝ), d.milinSum_normalized (Nat.zero_lt_succ j), sum_range_succ,
    Nat.cast_succ, sub_self, zero_mul, add_zero, ← sum_sub_distrib]
  calc
    _ = ∑ i ∈ range j, (‖d.t (i + 1)‖ ^ 2 - 1) / ((j : ℝ) * (j + 1)) := by
      apply sum_congr rfl
      intro i _
      have hi' : (i : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    _ = _ := by
      simp only [stepParameter, logMass, div_eq_mul_inv, ← sum_mul, sum_sub_distrib,
        sum_const, card_range, nsmul_eq_mul, mul_one]

private theorem one_add_stepParameter {j : ℕ} (hj : 0 < j) :
    1 + d.stepParameter j = ((j : ℝ) ^ 2 + d.logMass j) / ((j : ℝ) * (j + 1)) := by
  have hj' : (j : ℝ) ≠ 0 := by positivity
  have hs : (j : ℝ) + 1 ≠ 0 := by positivity
  rw [stepParameter]
  field_simp
  ring

private theorem one_add_stepParameter_pos {j : ℕ} (hj : 0 < j) :
    0 < 1 + d.stepParameter j := by
  rw [d.one_add_stepParameter hj]
  have hlog := d.logMass_nonneg j
  positivity

private theorem remainder_ratio_lt_one {j : ℕ} (hj : 0 < j) :
    d.remainder j / ((j : ℝ) ^ 2 + d.logMass j) < 1 := by
  have hj' : 0 < (j : ℝ) := by positivity
  have hlog := d.logMass_nonneg j
  rw [div_lt_one (by positivity)]
  exact (d.remainder_le_logMass hj).trans_lt (by linarith [sq_pos_of_pos hj'])

/-- The change in logarithmic remainder as one coefficient is added. -/
theorem logRemainder_succ_sub {j : ℕ} (hj : 0 < j) :
    d.logRemainder (j + 1) - d.logRemainder j =
      (d.stepParameter j - Real.log (1 + d.stepParameter j)) -
        Real.log (1 - d.remainder j / ((j : ℝ) ^ 2 + d.logMass j)) := by
  have hj' : 0 < (j : ℝ) := by positivity
  have hs : 0 < (j : ℝ) + 1 := by positivity
  have hmass := d.partialMass_pos hj
  have hmass' := d.partialMass_pos (Nat.zero_lt_succ j)
  have hlog := d.logMass_nonneg j
  have hsquare : 0 < (j : ℝ) ^ 2 + d.logMass j := by positivity
  have hratio : 0 < 1 - d.remainder j / ((j : ℝ) ^ 2 + d.logMass j) :=
    sub_pos.mpr (d.remainder_ratio_lt_one hj)
  have hn : (d.partialMass (j + 1) / (j + 1)) / (d.partialMass j / j) =
      (1 + d.stepParameter j) * (1 - d.remainder j / ((j : ℝ) ^ 2 + d.logMass j)) := by
    rw [d.one_add_stepParameter hj, d.partialMass_succ, remainder]
    field_simp
    ring
  have hlogs := congrArg Real.log hn
  rw [Real.log_div (div_ne_zero hmass'.ne' hs.ne') (div_ne_zero hmass.ne' hj'.ne'),
    Real.log_div hmass'.ne' hs.ne', Real.log_div hmass.ne' hj'.ne',
    Real.log_mul (d.one_add_stepParameter_pos hj).ne' hratio.ne'] at hlogs
  have hstep := d.milinSum_normalized_sub_succ hj
  simp only [logRemainder, Nat.cast_succ]
  rw [Real.log_div hs.ne' hmass'.ne', Real.log_div hj'.ne' hmass.ne']
  linarith

theorem logRemainder_le_succ {j : ℕ} (hj : 0 < j) :
    d.logRemainder j ≤ d.logRemainder (j + 1) := by
  have hlog := d.logMass_nonneg j
  have hr := d.remainder_nonneg hj
  have hstep := Real.log_le_sub_one_of_pos (d.one_add_stepParameter_pos hj)
  have hratio : 0 ≤ d.remainder j / ((j : ℝ) ^ 2 + d.logMass j) := by positivity
  have hlogRatio := Real.log_nonpos (by linarith [d.remainder_ratio_lt_one hj] :
      0 ≤ 1 - d.remainder j / ((j : ℝ) ^ 2 + d.logMass j)) (by linarith)
  linarith [d.logRemainder_succ_sub hj]

theorem logRemainder_le_of_le {i j : ℕ} (hi : 0 < i) (hij : i ≤ j) :
    d.logRemainder i ≤ d.logRemainder j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    exact ih.trans (d.logRemainder_le_succ (hi.trans_le hk))

theorem logRemainder_nonneg {j : ℕ} (hj : 0 < j) : 0 ≤ d.logRemainder j := by
  simpa using d.logRemainder_le_of_le (show 0 < 1 by decide) hj

/-- Positivity of a Milin sum bounds the corresponding Taylor partial mass. -/
theorem partialMass_le_index {j : ℕ} (hj : 0 < j) (hT : 0 ≤ d.milinSum j) :
    d.partialMass j ≤ j := by
  have hmass := d.partialMass_pos hj
  have hj' : 0 < (j : ℝ) := by positivity
  have hdiv : 0 ≤ d.milinSum j / (j : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (j / d.partialMass j) := by
    have hL := d.logRemainder_nonneg hj
    rw [logRemainder] at hL
    linarith
  exact (one_le_div₀ hmass).mp ((Real.log_nonneg_iff (by positivity)).mp hlog)

/-- The unweighted Toeplitz error splits into the least-squares remainder and a mass deficit. -/
theorem toeplitz_row_norm_sq {j : ℕ} (hj : 0 < j) :
    ∑ i ∈ range j, ‖d.c j * conj (d.c i) - d.t (j - i)‖ ^ 2 =
      d.remainder j + ((j : ℝ) - d.partialMass j) ^ 2 / d.partialMass j * ‖d.c j‖ ^ 2 := by
  have hmass := d.partialMass_pos hj
  simp_rw [norm_sub_rev _ (d.t _)]
  convert d.sum_sub_real_mul_conj_norm_sq j 1 zero_le_one using 1
  · simp
  · rw [remainder]
    field_simp
    ring

/-- The Taylor coefficient of the normalized square, shifted by the leading variable. -/
def squareCoeff (j : ℕ) : ℂ :=
  ∑ i ∈ range j, d.c i * d.c (j - 1 - i)

/-- The second coefficient of the shifted square is twice the first logarithmic coefficient. -/
theorem squareCoeff_two : d.squareCoeff 2 = 2 * d.t 1 := by
  norm_num [squareCoeff, sum_range_succ, d.c_zero, d.t_one_eq_c_one, two_mul]

private theorem partialMass_reverse (j : ℕ) :
    ∑ i ∈ range j, ‖d.c (j - 1 - i)‖ ^ 2 = d.partialMass j :=
  sum_range_reflect (fun i => ‖d.c i‖ ^ 2) j

/-- The coefficients of the shifted square are bounded by the corresponding Taylor mass. -/
theorem norm_squareCoeff_le_partialMass (j : ℕ) : ‖d.squareCoeff j‖ ≤ d.partialMass j := by
  rw [squareCoeff]
  calc
    _ ≤ ∑ i ∈ range j, ‖d.c i * d.c (j - 1 - i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range j, (‖d.c i‖ ^ 2 + ‖d.c (j - 1 - i)‖ ^ 2) / 2 := by
      apply sum_le_sum
      intro i _
      rw [norm_mul]
      nlinarith [sq_nonneg (‖d.c i‖ - ‖d.c (j - 1 - i)‖)]
    _ = _ := by
      simp only [div_eq_mul_inv, ← sum_mul, sum_add_distrib]
      rw [d.partialMass_reverse, ← partialMass]
      ring

/-- The bound on a coefficient of the shifted square supplied by the Milin sum. -/
theorem norm_squareCoeff_le_index {j : ℕ} (hj : 0 < j) (hT : 0 ≤ d.milinSum j) :
    ‖d.squareCoeff j‖ ≤ j :=
  (d.norm_squareCoeff_le_partialMass j).trans (d.partialMass_le_index hj hT)

/-- A coefficient deficit controls the logarithmic remainder and the Milin sum. -/
theorem logRemainder_and_milinSum_le_of_deficit {n : ℕ} (hn : 6 ≤ n)
    (hT : 0 ≤ d.milinSum n) (hD : (n : ℝ) - ‖d.squareCoeff n‖ ≤ 3) :
    let D := (n : ℝ) - ‖d.squareCoeff n‖
    d.logRemainder n ≤ 2 * D / n ∧ d.milinSum n ≤ 2 * D := by
  dsimp only
  set D : ℝ := n - ‖d.squareCoeff n‖ with hDef
  have hn₀ : 0 < n := by omega
  have hn' : 0 < (n : ℝ) := by positivity
  have hn₆ : 6 ≤ (n : ℝ) := by exact_mod_cast hn
  have hD₀ : 0 ≤ D := sub_nonneg.mpr (d.norm_squareCoeff_le_index hn₀ hT)
  have hmass := d.partialMass_pos hn₀
  have hA : (n : ℝ) - D ≤ d.partialMass n := by
    rw [hDef, sub_sub_cancel]
    exact d.norm_squareCoeff_le_partialMass n
  let x : ℝ := D / n
  have hx₀ : 0 ≤ x := div_nonneg hD₀ hn'.le
  have hx₁ : x ≤ 1 / 2 := (div_le_iff₀ hn').2 (by linarith)
  have hy : 0 < 1 - x := by linarith
  have hAx : 1 - x ≤ d.partialMass n / n := by
    apply (le_div_iff₀ hn').2
    calc
      _ = (n : ℝ) - D := by rw [show x = D / n from rfl, sub_mul, one_mul,
        div_mul_cancel₀ D hn'.ne']
      _ ≤ _ := hA
  have hlog := Real.log_le_log hy hAx
  rw [Real.log_div hmass.ne' hn'.ne'] at hlog
  have hlog' : Real.log (n / d.partialMass n) ≤ -Real.log (1 - x) := by
    rw [Real.log_div hn'.ne' hmass.ne']
    linarith
  have hinv : (1 - x)⁻¹ - 1 ≤ 2 * x := by
    rw [inv_eq_one_div, div_sub_one hy.ne', div_le_iff₀ hy]
    nlinarith [mul_nonneg hx₀ (show 0 ≤ 1 - 2 * x by linarith)]
  have hlog'' : -Real.log (1 - x) ≤ 2 * x := by
    linarith [Real.one_sub_inv_le_log_of_pos hy]
  have hbound : d.logRemainder n + d.milinSum n / n ≤ 2 * D / n := by
    rw [logRemainder, sub_add_cancel]
    simpa only [x, mul_div_assoc] using hlog'.trans hlog''
  have hL₀ := d.logRemainder_nonneg hn₀
  have hT₀ : 0 ≤ d.milinSum n / n := div_nonneg hT hn'.le
  refine ⟨by linarith, (div_le_div_iff_of_pos_right hn').mp ?_⟩
  linarith

private theorem stepParameter_lt_one_of_logRemainder_lt {j n : ℕ} (hj : 0 < j) (hjn : j < n)
    (hL : d.logRemainder n < 1 - Real.log 2) : d.stepParameter j < 1 := by
  have hLj := d.logRemainder_nonneg hj
  have hLjn := d.logRemainder_le_of_le (Nat.zero_lt_succ j) hjn
  have hlog := d.logMass_nonneg j
  have hr := d.remainder_nonneg hj
  have hratio₀ : 0 ≤ d.remainder j / ((j : ℝ) ^ 2 + d.logMass j) := by positivity
  have hratio₁ : d.remainder j / ((j : ℝ) ^ 2 + d.logMass j) < 1 :=
    d.remainder_ratio_lt_one hj
  have hlogRatio := Real.log_nonpos (sub_nonneg.mpr hratio₁.le)
    (sub_le_self _ hratio₀)
  by_contra! hu
  have hy : 0 < (1 + d.stepParameter j) / 2 := by linarith
  have h := Real.log_le_sub_one_of_pos hy
  rw [Real.log_div (d.one_add_stepParameter_pos hj).ne' (by norm_num)] at h
  linarith [d.logRemainder_succ_sub hj]

private theorem remainder_ratio_le_logRemainder_succ_sub {j : ℕ} (hj : 0 < j)
    (hu : d.stepParameter j ≤ 1) :
    d.remainder j / (j : ℝ) ^ 2 ≤ 4 * (d.logRemainder (j + 1) - d.logRemainder j) := by
  have hj' : 0 < (j : ℝ) := by positivity
  have hj₁ : 1 ≤ (j : ℝ) := by
    exact_mod_cast (show 1 ≤ j from hj)
  have hlog := d.logMass_nonneg j
  have hR := d.remainder_nonneg hj
  let S : ℝ := (j : ℝ) ^ 2 + d.logMass j
  have hS : 0 < S := by dsimp [S]; positivity
  have hRatio₀ : 0 ≤ d.remainder j / S := div_nonneg hR hS.le
  have hRatio₁ : d.remainder j / S < 1 := d.remainder_ratio_lt_one hj
  have hRatioStep : d.remainder j / S ≤ d.logRemainder (j + 1) - d.logRemainder j := by
    change d.remainder j / ((j : ℝ) ^ 2 + d.logMass j) ≤ _
    have hlogRatio := Real.log_le_sub_one_of_pos (sub_pos.mpr hRatio₁)
    have hlogStep := Real.log_le_sub_one_of_pos (d.one_add_stepParameter_pos hj)
    dsimp only [S] at hlogRatio
    rw [d.logRemainder_succ_sub hj]
    linarith
  have hSle : S ≤ 4 * (j : ℝ) ^ 2 := calc
    _ ≤ 2 * ((j : ℝ) * (j + 1)) := by
      apply (div_le_iff₀ (show 0 < (j : ℝ) * (j + 1) by positivity)).mp
      change ((j : ℝ) ^ 2 + d.logMass j) / ((j : ℝ) * (j + 1)) ≤ 2
      rw [← d.one_add_stepParameter hj]
      linarith
    _ ≤ 2 * ((j : ℝ) * (2 * j)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hj'.le)
        (by norm_num)
    _ = _ := by ring
  calc
    d.remainder j / (j : ℝ) ^ 2 = d.remainder j / S * (S / (j : ℝ) ^ 2) := by
      field_simp
    _ ≤ d.remainder j / S * 4 :=
      mul_le_mul_of_nonneg_left ((div_le_iff₀ (sq_pos_of_pos hj')).2 hSle) hRatio₀
    _ ≤ _ := by linarith

/-- A sufficiently small logarithmic remainder bounds the weighted sum of the previous
least-squares remainders. The sum runs over indices `1` through `n - 1`. -/
theorem sum_remainder_ratio_le_of_logRemainder_lt {n : ℕ} (hn : 0 < n)
    (hL : d.logRemainder n < 1 - Real.log 2) :
    ∑ i ∈ range (n - 1), d.remainder (i + 1) / ((i : ℝ) + 1) ^ 2 ≤
      4 * d.logRemainder n := by
  have htel (m : ℕ) : ∑ i ∈ range m, (d.logRemainder (i + 2) - d.logRemainder (i + 1)) =
      d.logRemainder (m + 1) := by
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, ih]; ring
  calc
    _ ≤ ∑ i ∈ range (n - 1), 4 * (d.logRemainder (i + 2) - d.logRemainder (i + 1)) := by
      apply sum_le_sum
      intro i hi
      have hin : i + 1 < n := by have hi' := mem_range.mp hi; omega
      have hu := d.stepParameter_lt_one_of_logRemainder_lt (Nat.zero_lt_succ i) hin hL
      simpa only [Nat.cast_succ] using d.remainder_ratio_le_logRemainder_succ_sub
        (Nat.zero_lt_succ i) hu.le
    _ = _ := by rw [← mul_sum, htel, Nat.sub_add_cancel hn]

/-- The three coefficient-deficit estimates hold beyond one absolute index. -/
theorem exists_index_for_small_remainders :
    ∃ N : ℕ, 6 ≤ N ∧ ∀ (d : MilinCoefficients) (n : ℕ), N ≤ n → 0 ≤ d.milinSum n →
      (n : ℝ) - ‖d.squareCoeff n‖ ≤ 3 →
      let D := (n : ℝ) - ‖d.squareCoeff n‖
      d.logRemainder n ≤ 2 * D / n ∧ d.milinSum n ≤ 2 * D ∧
        ∑ i ∈ range (n - 1), d.remainder (i + 1) / ((i : ℝ) + 1) ^ 2 ≤ 8 * D / n := by
  have hg : 0 < 1 - Real.log 2 := by
    have h := Real.log_lt_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num) (by norm_num)
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (6 / (1 - Real.log 2))
  refine ⟨max 6 N, le_max_left _ _, ?_⟩
  intro d n hn hT hD
  have hn' : 6 ≤ n := (le_max_left _ _).trans hn
  have hn₀ : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by positivity
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (le_max_right 6 N).trans hn
  have hnGap : 6 / (n : ℝ) < 1 - Real.log 2 := by
    apply (div_lt_iff₀ hnR).2
    have h := (div_lt_iff₀ hg).1 (hN.trans_le hNn)
    simpa only [mul_comm] using h
  obtain ⟨hL, hT'⟩ := d.logRemainder_and_milinSum_le_of_deficit hn' hT hD
  have hLg : d.logRemainder n < 1 - Real.log 2 :=
    (hL.trans ((div_le_div_iff_of_pos_right hnR).2 (by linarith))).trans_lt hnGap
  dsimp only
  refine ⟨hL, hT', (d.sum_remainder_ratio_le_of_logRemainder_lt hn₀ hLg).trans ?_⟩
  calc
    4 * d.logRemainder n ≤ 4 * (2 * ((n : ℝ) - ‖d.squareCoeff n‖) / n) :=
      mul_le_mul_of_nonneg_left hL (by norm_num)
    _ = _ := by ring

/-- Saturation of the coefficient bound forces the first logarithmic coefficient to have unit norm. -/
theorem norm_firstLogCoeff_of_norm_squareCoeff_eq_index {j : ℕ} (hj : 2 ≤ j)
    (hT : 0 ≤ d.milinSum j) (heq : ‖d.squareCoeff j‖ = j) : ‖d.t 1‖ = 1 := by
  have hj' : 0 < j := by omega
  have hmass : d.partialMass j = j := by
    apply le_antisymm (d.partialMass_le_index hj' hT)
    simpa only [← heq] using d.norm_squareCoeff_le_partialMass j
  have hLn := d.logRemainder_nonneg hj'
  have hL : d.logRemainder j ≤ 0 := by
    rw [logRemainder, hmass, Real.log_div_self, zero_sub]
    exact neg_nonpos.mpr (by positivity)
  have hL2 := d.logRemainder_le_of_le (show 0 < 2 by decide) hj
  have hlogStep := d.logRemainder_succ_sub (j := 1) (by decide)
  rw [d.logRemainder_one, sub_zero] at hlogStep
  have hratio : 0 ≤ d.remainder 1 / ((1 : ℝ) ^ 2 + d.logMass 1) :=
    div_nonneg (d.remainder_nonneg (by decide)) (by positivity [d.logMass_nonneg 1])
  have hratio' : d.remainder 1 / ((1 : ℝ) ^ 2 + d.logMass 1) < 1 := by
    simpa using d.remainder_ratio_lt_one (j := 1) (by decide)
  have hlogRatio := Real.log_nonpos (sub_nonneg.mpr hratio'.le)
    (sub_le_self _ hratio)
  have hu : d.stepParameter 1 = 0 := by
    by_contra! hne
    have hstrict := Real.log_lt_sub_one_of_pos (d.one_add_stepParameter_pos (by decide))
      (show 1 + d.stepParameter 1 ≠ 1 from by exact fun h => hne (by linarith))
    norm_num at hlogStep
    linarith
  unfold stepParameter logMass at hu
  norm_num at hu
  nlinarith [norm_nonneg (d.t 1)]

/-- Saturation of the coefficient bound at any index at least two saturates its second index. -/
theorem norm_squareCoeff_two_of_norm_squareCoeff_eq_index {j : ℕ} (hj : 2 ≤ j)
    (hT : 0 ≤ d.milinSum j) (heq : ‖d.squareCoeff j‖ = j) : ‖d.squareCoeff 2‖ = 2 := by
  rw [d.squareCoeff_two, norm_mul,
    d.norm_firstLogCoeff_of_norm_squareCoeff_eq_index hj hT heq, Complex.norm_two, mul_one]

/-- The squared error in reflection of the first `j` coefficients. -/
theorem reflection_norm_sq (j : ℕ) {ω : ℂ} (hω : ‖ω‖ = 1) :
    ∑ i ∈ range j, ‖d.c i - ω * conj (d.c (j - 1 - i))‖ ^ 2 =
      2 * (d.partialMass j - (conj ω * d.squareCoeff j).re) := by
  simp_rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_conj,
    map_mul, Complex.conj_conj]
  simp_rw [Complex.normSq_eq_norm_sq, hω, one_pow, one_mul]
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← Complex.re_sum]
  rw [d.partialMass_reverse, ← partialMass, squareCoeff, mul_sum]
  have h : ∑ i ∈ range j, d.c i * (conj ω * d.c (j - 1 - i)) =
      ∑ i ∈ range j, conj ω * (d.c i * d.c (j - 1 - i)) := by
    exact sum_congr rfl (fun _ _ => by ring)
  rw [h]
  ring

end MilinCoefficients

end Zalcman
