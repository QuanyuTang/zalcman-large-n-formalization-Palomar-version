/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Milin
public import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Controlling initial Taylor coefficients from logarithmic coefficients

A positive comparison sequence solves the coefficient recursion with a constant
logarithmic coefficient bound. Its finite product is bounded by the exponential
of the harmonic sum.
-/

public section

namespace Zalcman.MilinCoefficients

open Finset

private noncomputable def prefixMajorant (ε : ℝ) (j : ℕ) : ℝ :=
  ∏ i ∈ range j, (1 + ε / ((i : ℝ) + 1))

private theorem prefixMajorant_recursion (ε : ℝ) (j : ℕ) :
    (j : ℝ) * prefixMajorant ε j = (1 + ε) * ∑ i ∈ range j, prefixMajorant ε i := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h₁ : prefixMajorant ε (j + 1) = prefixMajorant ε j * (1 + ε / ((j : ℝ) + 1)) :=
      prod_range_succ _ _
    rw [Nat.cast_succ, h₁, sum_range_succ, mul_add (1 + ε), ← ih]
    have hj : 0 < (j : ℝ) + 1 := by positivity
    field_simp
    ring

private theorem prefixMajorant_le_exp (ε : ℝ) (hε : 0 ≤ ε) (j : ℕ) :
    prefixMajorant ε j ≤ Real.exp (ε * (harmonic j : ℝ)) := by
  calc
    _ ≤ ∏ i ∈ range j, Real.exp (ε / ((i : ℝ) + 1)) := by
      apply prod_le_prod₀
      · exact fun i _ => by positivity
      · exact fun i _ => by simpa only [add_comm] using Real.add_one_le_exp (ε / ((i : ℝ) + 1))
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Nat.cast_succ, Rat.cast_add,
        Rat.cast_natCast, Rat.cast_one, div_eq_mul_inv, mul_sum]

/-- If the first logarithmic derivative coefficients are close to one, the corresponding
normalized Taylor coefficients are controlled by the harmonic majorant. -/
theorem norm_sub_one_le_exp_harmonic (d : MilinCoefficients) {ε : ℝ} (hε : 0 ≤ ε)
    {J : ℕ} (ht : ∀ k, 0 < k → k ≤ J → ‖d.t k - 1‖ ≤ ε) {j : ℕ} (hj : j ≤ J) :
    ‖d.c j - 1‖ ≤ Real.exp (ε * (harmonic j : ℝ)) - 1 := by
  have hComp (m : ℕ) (hm : m ≤ J) : ‖d.c m - 1‖ ≤ prefixMajorant ε m - 1 := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases hm₀ : m = 0
      · simp [hm₀, prefixMajorant, d.c_zero]
      have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm₀
      apply (mul_le_mul_iff_of_pos_left hmR).mp
      have hconv : (m : ℂ) * (d.c m - 1) = ∑ i ∈ range m, (d.t (m - i) * d.c i - 1) := by
        rw [mul_sub, mul_one, sum_sub_distrib, d.recursion]
        simp
      calc
        _ = ‖(m : ℂ) * (d.c m - 1)‖ := by rw [norm_mul, Complex.norm_natCast]
        _ ≤ ∑ i ∈ range m, ‖d.t (m - i) * d.c i - 1‖ := by
          rw [hconv]
          exact norm_sum_le _ _
        _ ≤ ∑ i ∈ range m, ((1 + ε) * prefixMajorant ε i - 1) := by
          apply sum_le_sum
          intro i hi
          have hi' := mem_range.mp hi
          have hx := ih i hi' (hi'.le.trans hm)
          have hxnorm : ‖d.c i‖ ≤ prefixMajorant ε i := by
            have htri := norm_sub_le (d.c i - 1) (-1 : ℂ)
            simp only [sub_neg_eq_add, sub_add_cancel, norm_neg, norm_one] at htri
            linarith
          have ht' := ht (m - i) (by omega) (by omega)
          calc
            _ = ‖(d.c i - 1) + (d.t (m - i) - 1) * d.c i‖ := by congr 1; ring
            _ ≤ ‖d.c i - 1‖ + ‖d.t (m - i) - 1‖ * ‖d.c i‖ := by
              simpa only [norm_mul] using norm_add_le (d.c i - 1) ((d.t (m - i) - 1) * d.c i)
            _ ≤ (prefixMajorant ε i - 1) + ε * prefixMajorant ε i := add_le_add hx
              (mul_le_mul ht' hxnorm (norm_nonneg _) hε)
            _ = _ := by ring
        _ = _ := by
          rw [sum_sub_distrib, ← mul_sum, ← prefixMajorant_recursion]
          simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
          ring
  exact (hComp j hj).trans (sub_le_sub_right (prefixMajorant_le_exp ε hε _) _)

/-- The low Taylor block controls the phase of a nearby constant approximation. -/
theorem norm_phase_sub_one_sq_le_of_log_prefix (d : MilinCoefficients) {n J : ℕ} (hJn : J < n)
    {ε E : ℝ} (hε : 0 ≤ ε) {α : ℂ}
    (hE : (∑ j ∈ range n, ‖d.c j - α‖ ^ 2) ≤ E)
    (ht : ∀ k, 0 < k → k ≤ J → ‖d.t k - 1‖ ≤ ε) :
    ‖α - 1‖ ^ 2 ≤ 2 * E / ((J : ℝ) + 1) +
      2 * (Real.exp (ε * (1 + Real.log (n : ℝ))) - 1) ^ 2 := by
  let S := Real.exp (ε * (1 + Real.log (n : ℝ))) - 1
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hc (j : ℕ) (hj : j ≤ J) : ‖d.c j - 1‖ ≤ S := by
    have hharm : (harmonic j : ℝ) ≤ 1 + Real.log (n : ℝ) := by
      cases j with
      | zero => simpa using (show 0 ≤ 1 + Real.log (n : ℝ) by linarith only [Real.log_nonneg hn])
      | succ j =>
        have hpos : (0 : ℝ) < (j + 1 : ℕ) := by positivity
        have hle : (↑(j + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show j + 1 ≤ n by omega)
        exact (harmonic_le_one_add_log (j + 1)).trans
          (add_le_add_right (Real.log_le_log hpos hle) _)
    exact (d.norm_sub_one_le_exp_harmonic hε ht hj).trans
      (sub_le_sub_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hharm hε)) _)
  have hbound (j : ℕ) (hj : j ∈ range (J + 1)) : ‖α - 1‖ ^ 2 ≤ 2 * ‖d.c j - α‖ ^ 2 + 2 * S ^ 2 := by
    have hj' : j ≤ J := Nat.le_of_lt_succ (mem_range.mp hj)
    have htriangle : ‖α - 1‖ ≤ ‖d.c j - α‖ + S := calc
      _ = ‖(α - d.c j) + (d.c j - 1)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖α - d.c j‖ + ‖d.c j - 1‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_sub_rev α]; exact add_le_add_right (hc j hj') _
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    nlinarith only [hsq, sq_nonneg (‖d.c j - α‖ - S)]
  have hs : (∑ j ∈ range (J + 1), ‖d.c j - α‖ ^ 2) ≤ E :=
    (sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun _ _ _ => sq_nonneg _)).trans hE
  have h := sum_le_sum (s := range (J + 1)) hbound
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul, Nat.cast_succ] at h
  have hJ : 0 < (J : ℝ) + 1 := by positivity
  change ‖α - 1‖ ^ 2 ≤ 2 * E / ((J : ℝ) + 1) + 2 * S ^ 2
  apply (mul_le_mul_iff_of_pos_left hJ).mp
  have heq : ((J : ℝ) + 1) * (2 * E / ((J : ℝ) + 1) + 2 * S ^ 2) =
      2 * E + ((J : ℝ) + 1) * (2 * S ^ 2) := by
    rw [mul_add, mul_div_cancel₀ _ hJ.ne']
  rw [heq]
  linarith only [h, hs]

/-- Once the harmonic exponent is at most one, the phase bound is quadratic in
the logarithmic coefficient error. -/
theorem norm_phase_sub_one_sq_le_of_small_log_prefix (d : MilinCoefficients) {n J : ℕ} (hJn : J < n)
    {ε E : ℝ} (hε : 0 ≤ ε) {α : ℂ}
    (hE : (∑ j ∈ range n, ‖d.c j - α‖ ^ 2) ≤ E)
    (ht : ∀ k, 0 < k → k ≤ J → ‖d.t k - 1‖ ≤ ε)
    (hsmall : ε * (1 + Real.log (n : ℝ)) ≤ 1) :
    ‖α - 1‖ ^ 2 ≤ 2 * E / ((J : ℝ) + 1) +
      8 * ε ^ 2 * (1 + Real.log (n : ℝ)) ^ 2 := by
  let x := ε * (1 + Real.log (n : ℝ))
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hx : 0 ≤ x := mul_nonneg hε (by linarith only [Real.log_nonneg hn])
  have hxExp : 0 ≤ Real.exp x - 1 := by
    have h := Real.exp_le_exp.mpr hx
    rwa [Real.exp_zero, ← sub_nonneg] at h
  have hE₁ := Real.abs_exp_sub_one_le (show |x| ≤ 1 by rwa [abs_of_nonneg hx])
  rw [abs_of_nonneg hxExp, abs_of_nonneg hx] at hE₁
  have hs := pow_le_pow_left₀ hxExp hE₁ 2
  have h := d.norm_phase_sub_one_sq_le_of_log_prefix hJn hε hE ht
  change ‖α - 1‖ ^ 2 ≤ 2 * E / ((J : ℝ) + 1) + 2 * (Real.exp x - 1) ^ 2 at h
  dsimp only [x] at hs
  nlinarith only [h, hs]

end Zalcman.MilinCoefficients
