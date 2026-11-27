/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CoefficientContinuity
import Mathlib.Tactic.Ring

/-!
# Rotation of square-root coefficients

The convolution recursion and normalization give the exact rotation law.
-/

public section

namespace Zalcman

open Finset

/-- Rotating the normalized map multiplies each square-root coefficient by a power of the phase. -/
theorem rootCoeff_rotate {f : ℂ → ℂ} (hf : NormalizedUnivalent f) {lam : ℂ}
    (hUnit : ‖lam‖ = 1) (n : ℕ) :
    rootCoeff (rotate_normalizedUnivalent hf hUnit) n = lam ^ n * rootCoeff hf n := by
  let hg := rotate_normalizedUnivalent hf hUnit
  change rootCoeff hg n = lam ^ n * rootCoeff hf n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hsum : (∑ i ∈ range n, rootCoeff hg (i + 1) * rootCoeff hg (n - i)) =
          lam ^ (n + 1) * ∑ i ∈ range n, rootCoeff hf (i + 1) * rootCoeff hf (n - i) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i hi
        have hi' := mem_range.mp hi
        rw [ih (i + 1) (by omega), ih (n - i) (by omega)]
        calc
          _ = (lam ^ (i + 1) * lam ^ (n - i)) * (rootCoeff hf (i + 1) * rootCoeff hf (n - i)) := by ring
          _ = _ := by rw [← pow_add, show i + 1 + (n - i) = n + 1 by omega]
      rw [rootCoeff_succ_recursion hg, rootCoeff_succ_recursion hf, hsum,
        coeff_rotate f hUnit (show 1 ≤ n + 2 by omega)]
      rw [show n + 2 - 1 = n + 1 by omega]
      ring

end Zalcman
