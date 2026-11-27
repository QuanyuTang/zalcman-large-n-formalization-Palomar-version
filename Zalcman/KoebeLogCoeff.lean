/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.LogarithmicCoefficients
import Mathlib.Tactic.LinearCombination

/-!
# Normalized logarithmic coefficients of the Koebe function

The finite coefficient recursions determine both the square-root coefficients
and the logarithmic derivative coefficients from the Koebe Taylor series.
-/

public section

namespace Zalcman

open Finset
open scoped BigOperators ComplexConjugate

private lemma coeff_koebe_of_pos {n : ℕ} (hn : 0 < n) : coeff koebe n = n := by
  have hrotate : rotate (1 : ℂ) koebe = koebe := by
    funext z
    simp [rotate]
  simpa only [hrotate, one_pow, mul_one] using
    coeff_rotate_koebe (lam := (1 : ℂ)) (by simp) hn

private theorem rootCoeff_eq_one_of_koebe_coeffs {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    (hcoeff : ∀ n : ℕ, 0 < n → coeff f n = n) (n : ℕ) : rootCoeff hf n = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact rootCoeff_zero hf
    | succ k =>
      let c := rootCoeff hf
      have hmid : ∑ i ∈ range k, c (i + 1) * c (k + 1 - (i + 1)) = (k : ℂ) := by
        calc
          _ = ∑ _i ∈ range k, (1 : ℂ) := by
            refine sum_congr rfl fun i hi ↦ ?_
            have hi' := mem_range.mp hi
            change c (i + 1) * c (k + 1 - (i + 1)) = 1
            have ha : c (i + 1) = 1 := ih _ (by omega)
            have hb : c (k + 1 - (i + 1)) = 1 := ih _ (by omega)
            rw [ha, hb, mul_one]
          _ = _ := by simp
      have hRec := coeff_succ_eq_sum_rootCoeff hf (k + 1)
      change coeff f (k + 1 + 1) = ∑ i ∈ range (k + 1 + 1), c i * c (k + 1 - i) at hRec
      rw [hcoeff (k + 1 + 1) (by omega), sum_range_succ', sum_range_succ _ k, hmid] at hRec
      have hc0 : c 0 = 1 := rootCoeff_zero hf
      simp only [Nat.sub_self, Nat.sub_zero, hc0, mul_one, one_mul, Nat.cast_succ] at hRec
      change c (k + 1) = 1
      linear_combination (-1 / 2 : ℂ) * hRec

private theorem logCoeff_eq_one_of_koebe_coeffs {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    (hcoeff : ∀ n : ℕ, 0 < n → coeff f n = n) (n : ℕ) : logCoeff hf (n + 1) = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hRec := rootCoeff_succ_eq_sum_logCoeff hf n
    simp only [rootCoeff_eq_one_of_koebe_coeffs hf hcoeff, mul_one] at hRec
    rw [sum_range_succ'] at hRec
    have hmid : ∑ i ∈ range n, logCoeff hf (n + 1 - (i + 1)) = (n : ℂ) := by
      calc
        _ = ∑ _i ∈ range n, (1 : ℂ) := by
          refine sum_congr rfl fun i hi ↦ ?_
          have hi' := mem_range.mp hi
          have hidx : n + 1 - (i + 1) = (n - (i + 1)) + 1 := by omega
          rw [hidx, ih (n - (i + 1)) (by omega)]
        _ = _ := by simp
    rw [hmid, Nat.sub_zero] at hRec
    linear_combination -hRec

/-- The half-logarithm coefficients of a function agreeing with Koebe on the disk are
reciprocals of their positive degrees. -/
theorem coeff_half_normalizedLogarithm_eq_inv_of_eqOn_koebe {f : ℂ → ℂ}
    (hf : NormalizedUnivalent f) (heq : Set.EqOn f koebe unitDisk) (n : ℕ) :
    coeff (fun z ↦ normalizedLogarithm hf z / 2) (n + 1) =
      ((n : ℂ) + 1)⁻¹ := by
  have hcoeff (j : ℕ) (hj : 0 < j) : coeff f j = j :=
    (coeff_congr_on_unitDisk heq j).trans (coeff_koebe_of_pos hj)
  have h := logCoeff_eq_one_of_koebe_coeffs hf hcoeff n
  simp only [logCoeff, Nat.cast_add, Nat.cast_one] at h
  have hn : (n : ℂ) + 1 ≠ 0 := by
    rw [← Nat.cast_succ (R := ℂ)]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [← one_div, eq_div_iff hn, mul_comm]
  exact h

end Zalcman
