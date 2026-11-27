/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Backward stability of finite triangular coefficient estimates

After the integrating factor has been applied, the error at each degree is
controlled by an error in the data and integrals of lower-degree errors.
-/

public section

namespace Zalcman

open Finset Set MeasureTheory

private theorem add_mul_sum_geom (A B : ℝ) (n : ℕ) :
    A + B * (∑ i ∈ range n, A * (1 + B) ^ i) = A * (1 + B) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ← add_assoc, ih, pow_succ]
    ring

/-- Backward integral bounds of triangular form propagate a uniform error in the data. -/
theorem triangular_error_le_of_integral_inequality {d : ℕ → ℝ → ℝ} {T C ε : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hInt : ∀ j t, 0 ≤ t → t ≤ T → IntervalIntegrable (d j) volume t T)
    (h : ∀ n t, 0 ≤ t → t ≤ T → d n t ≤ ε + C * ∑ j ∈ range n, ∫ u in t..T, d j u)
    (n : ℕ) (t : ℝ) (ht₀ : 0 ≤ t) (htT : t ≤ T) : d n t ≤ ε * (1 + C * T) ^ n := by
  let B := C * T
  have hT : 0 ≤ T := ht₀.trans htT
  have hB : 0 ≤ B := mul_nonneg hC hT
  induction n using Nat.strong_induction_on generalizing t with
  | h n ih =>
    have hI (j : ℕ) (hj : j < n) : (∫ u in t..T, d j u) ≤ T * (ε * (1 + B) ^ j) := calc
      _ ≤ ∫ _u in t..T, ε * (1 + B) ^ j := by
        apply intervalIntegral.integral_mono_on htT (hInt j t ht₀ htT) intervalIntegrable_const
        intro u hu
        exact ih j hj u (ht₀.trans hu.1) hu.2
      _ = (T - t) * (ε * (1 + B) ^ j) := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_self _ ht₀) (by positivity)
    calc
      d n t ≤ ε + C * ∑ j ∈ range n, ∫ u in t..T, d j u := h n t ht₀ htT
      _ ≤ ε + C * ∑ j ∈ range n, T * (ε * (1 + B) ^ j) := by
        have hsum := sum_le_sum (s := range n) (fun j hj => hI j (mem_range.mp hj))
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsum hC)
      _ = ε + B * ∑ j ∈ range n, ε * (1 + B) ^ j := by rw [← mul_sum, ← mul_assoc]
      _ = _ := add_mul_sum_geom ε B n

end Zalcman
