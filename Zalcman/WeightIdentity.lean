/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Finite summation in the de Branges–Weinstein identity

These identities convert the coefficientwise derivatives of weighted squared norms
into a sum of squares when the weights obey the consecutive-difference relation.
Index `k` here corresponds to manuscript index `k + 1` for the weights.
-/

public section

namespace Zalcman

open scoped BigOperators

private theorem sum_weighted_differences_aux (w τ L : ℕ → ℝ)
    (hτ : ∀ k, τ k - τ (k + 1) = L k + L (k + 1)) (M : ℕ) :
    (∑ k ∈ Finset.range M, τ k * (w (k + 1) - w k)) =
      (∑ k ∈ Finset.range M, L k * (w (k + 1) + w k - 2 * w 0)) +
        (τ M + L M) * (w M - w 0) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    linear_combination (w (M + 1) - w 0) * hτ M

/-- The weighted summation-by-parts identity with the terminal weights set to zero. -/
theorem sum_weighted_differences (w τ L : ℕ → ℝ) (M : ℕ)
    (hτ : ∀ k < M, τ k - τ (k + 1) = L k + L (k + 1))
    (hτM : τ M = 0) (hLM : L M = 0) :
    (∑ k ∈ Finset.range M, τ k * (w (k + 1) - w k)) =
      ∑ k ∈ Finset.range M, L k * (w (k + 1) + w k - 2 * w 0) := by
  let τ' := fun k ↦ if k < M then τ k else 0
  let L' := fun k ↦ if k < M then L k else 0
  have hτ' (k : ℕ) (hk : k ≤ M) : τ' k = τ k := by
    rcases hk.lt_or_eq with h | rfl
    · simp [τ', h]
    · simp [τ', hτM]
  have hL' (k : ℕ) (hk : k ≤ M) : L' k = L k := by
    rcases hk.lt_or_eq with h | rfl
    · simp [L', h]
    · simp [L', hLM]
  have hrel (k : ℕ) : τ' k - τ' (k + 1) = L' k + L' (k + 1) := by
    by_cases hk : k < M
    · rw [hτ' k hk.le, hτ' (k + 1) hk, hL' k hk.le, hL' (k + 1) hk]
      exact hτ k hk
    · have hsucc : ¬k + 1 < M := by omega
      simp [τ', L', hk, hsucc]
  calc
    _ = ∑ k ∈ Finset.range M, τ' k * (w (k + 1) - w k) := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [hτ' k (Finset.mem_range.mp hk).le]
    _ = ∑ k ∈ Finset.range M, L' k * (w (k + 1) + w k - 2 * w 0) := by
      simpa [τ', L'] using sum_weighted_differences_aux w τ' L' hrel M
    _ = _ := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [hL' k (Finset.mem_range.mp hk).le]

private lemma norm_average_sq (a b : ℂ) :
    (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 - ‖(a - b) / 2‖ ^ 2 = ‖(a + b) / 2‖ ^ 2 := by
  simp only [norm_div, Complex.norm_ofNat, div_pow, Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

/-- The algebraic step in the de Branges–Weinstein energy calculation. -/
theorem weighted_coefficient_energy (v : ℕ → ℂ) (τ L : ℕ → ℝ) (M : ℕ)
    (hv : ‖v 0‖ = 1) (hτ : ∀ k < M, τ k - τ (k + 1) = L k + L (k + 1))
    (hτM : τ M = 0) (hLM : L M = 0) :
    (∑ k ∈ Finset.range M, (τ k * (‖v (k + 1)‖ ^ 2 - ‖v k‖ ^ 2) / 2 +
      L k * (1 - ‖(v (k + 1) - v k) / 2‖ ^ 2))) =
      ∑ k ∈ Finset.range M, L k * ‖(v (k + 1) + v k) / 2‖ ^ 2 := by
  simp only [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul]
  rw [sum_weighted_differences (fun k ↦ ‖v k‖ ^ 2) τ L M hτ hτM hLM,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [hv, one_pow]
  have h := norm_average_sq (v (k + 1)) (v k)
  simp only [div_eq_mul_inv] at h
  linear_combination L k * h

end Zalcman
