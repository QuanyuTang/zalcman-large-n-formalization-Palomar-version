/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Extending a geometric approximation across a controlled shift

If the first half is close to one geometric sequence and its phase agrees with
the half-block shift, it controls the remaining entries, including the extra
entry of an odd-length sequence.
-/

public section

namespace Zalcman

open Finset

/-- A geometric approximation on the first half extends using the half-block shift. -/
theorem geometric_error_le_of_half_block (c : ℕ → ℂ) {n H : ℕ} (hH : 0 < H)
    (hlo : 2 * H ≤ n) (hhi : n ≤ 2 * H + 1) {β lam v : ℂ} (hv : ‖v‖ = 1)
    (hpow : lam ^ H = v) {P E : ℝ}
    (hP : (∑ j ∈ range H, ‖c j - β * lam ^ j‖ ^ 2) ≤ P)
    (hE : (∑ j ∈ range (n - H), ‖c (j + H) - v * c j‖ ^ 2) ≤ E) :
    (∑ j ∈ range n, ‖c j - β * lam ^ j‖ ^ 2) ≤ 7 * P + 6 * E := by
  let W (j : ℕ) : ℂ := c j - β * lam ^ j
  let F (j : ℕ) : ℝ := ‖W j‖ ^ 2
  let R (j : ℕ) : ℝ := ‖c (j + H) - v * c j‖ ^ 2
  have hR₀ (j : ℕ) : 0 ≤ R j := sq_nonneg _
  have hF₀ (j : ℕ) : 0 ≤ F j := sq_nonneg _
  have hpoint (j : ℕ) : F (j + H) ≤ 2 * (R j + F j) := by
    have heq : W (j + H) = (c (j + H) - v * c j) + v * W j := by
      simp only [W, pow_add, hpow]
      ring
    have htri : ‖W (j + H)‖ ≤ ‖c (j + H) - v * c j‖ + ‖W j‖ := by
      rw [heq]
      simpa only [norm_mul, hv, one_mul] using norm_add_le (c (j + H) - v * c j) (v * W j)
    have hs := pow_le_pow_left₀ (norm_nonneg _) htri 2
    dsimp only [F, R]
    nlinarith only [hs, sq_nonneg (‖c (j + H) - v * c j‖ - ‖W j‖)]
  have h₀ : F 0 ≤ P :=
    (single_le_sum (fun j _ => hF₀ j) (mem_range.mpr hH)).trans hP
  have hR : R 0 ≤ E :=
    (single_le_sum (fun j _ => hR₀ j) (mem_range.mpr (by omega : 0 < n - H))).trans hE
  have hFH : F H ≤ 2 * (E + P) := by
    have hb : 2 * (R 0 + F 0) ≤ 2 * (E + P) := by linarith only [hR, h₀]
    simpa only [zero_add] using (hpoint 0).trans hb
  have hprefix : ∑ j ∈ range (n - H), F j ≤ 3 * P + 2 * E := calc
    _ ≤ ∑ j ∈ range (H + 1), F j :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun j _ _ => hF₀ j)
    _ = (∑ j ∈ range H, F j) + F H := sum_range_succ _ _
    _ ≤ _ := by linarith only [hP, hFH]
  change (∑ j ∈ range n, F j) ≤ _
  rw [← Nat.add_sub_of_le (show H ≤ n by omega), sum_range_add]
  have hnext : ∑ i ∈ range (n - H), F (H + i) ≤ 2 * (E + (3 * P + 2 * E)) := calc
    _ ≤ ∑ i ∈ range (n - H), 2 * (R i + F i) :=
      sum_le_sum (fun i _ => by simpa only [Nat.add_comm H i] using hpoint i)
    _ = 2 * ((∑ i ∈ range (n - H), R i) + ∑ i ∈ range (n - H), F i) := by
      rw [← mul_sum, sum_add_distrib]
    _ ≤ _ := by linarith only [hE, hprefix]
  linarith only [hP, hnext]

end Zalcman
