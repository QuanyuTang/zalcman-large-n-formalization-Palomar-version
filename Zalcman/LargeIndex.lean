/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.FiniteQuartic
public import Zalcman.LargeIndexAssembly
public import Zalcman.QuarticDensity
import Mathlib.Tactic.NormNum

/-!
# The Zalcman inequality for sufficiently large indices
-/

public section

namespace Zalcman

/-- There is an absolute integer `N ≥ 3` such that every normalized univalent
map on the unit disk satisfies the Zalcman inequality at each `n ≥ N`.
Equality holds precisely for the rotations of the Koebe map. -/
theorem zalcman_large_n :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ f : ℂ → ℂ, NormalizedUnivalent f → ∀ n : ℕ, N ≤ n →
      ‖coeff f n ^ 2 - coeff f (2 * n - 1)‖ ≤ ((n : ℝ) - 1) ^ 2 ∧
      (‖coeff f n ^ 2 - coeff f (2 * n - 1)‖ = ((n : ℝ) - 1) ^ 2 ↔ IsKoebeRotation f) := by
  obtain ⟨N, hN, h⟩ := zalcman_large_n_of_quartic_bound
    (exists_quartic_bound_of_finite_driver_estimate (C := 3800) (by norm_num)
      milinSum_nonneg (fun P hP ↦ P.fourth_coeff_real_bound hP.le))
  exact ⟨N, hN, fun _ hf ↦ h hf⟩

end Zalcman
