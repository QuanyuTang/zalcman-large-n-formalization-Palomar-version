/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.PointDriverDensity
public import Zalcman.PrefixStability
public import Zalcman.RadialMassAssembly
public import Zalcman.RadialPropagation

/-!
# Assembly of the large-index Zalcman bound

The common Milin representation supplies the prefix estimates and
coefficient rigidity. The low-degree real-part estimate supplies the
remaining diameter input.
-/

public section

namespace Zalcman

open Finset

/-- Milin nonnegativity for the full normalized univalent class. -/
theorem milinSum_nonneg {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ) :
    0 ≤ (milinCoefficients hf).milinSum n := by
  cases n with
  | zero => simp [MilinCoefficients.milinSum]
  | succ n =>
    obtain ⟨ρ, _, hρ, hEq⟩ := exists_nonnegative_milin_representation hf
    rw [← hEq n]
    exact sum_nonneg (fun j _ ↦ mul_nonneg (connectionCoefficient_nonneg n j) (hρ j))

/-- The full large-index conclusion follows from the low-degree real-part estimate. -/
theorem zalcman_large_n_of_quartic_bound
    (hQuartic : ∃ C > 0, ∀ {f : ℂ → ℂ}, NormalizedUnivalent f →
      |(coeff f 4 - 2 * coeff f 2).re| ≤ C * (3 - (coeff f 3).re)) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ {f : ℂ → ℂ}, NormalizedUnivalent f → ∀ n : ℕ, N ≤ n →
      ‖coeff f n ^ 2 - coeff f (2 * n - 1)‖ ≤ ((n : ℝ) - 1) ^ 2 ∧
      (‖coeff f n ^ 2 - coeff f (2 * n - 1)‖ = ((n : ℝ) - 1) ^ 2 ↔ IsKoebeRotation f) := by
  obtain ⟨C, hC, hLow⟩ := hQuartic
  obtain ⟨K, hK, B, hB, hRadial⟩ := exists_radial_deficit_propagation_of_low_degree milinSum_nonneg hC.le hLow
  obtain ⟨A, hA, P, hP, N, hPrefix⟩ := exists_rotated_initial_prefix_estimates milinSum_nonneg
  refine eventually_zalcman_of_representation_prefix_and_propagation
    (N₀ := N) (fun hf ↦ ?_) hK hB.le (Real.tanh_lt_one (2 : ℝ)) hA.le hP.le hRadial hPrefix
  obtain ⟨ρ, _, hρ, hEq⟩ := exists_nonnegative_milin_representation hf
  exact ⟨ρ, hρ, hEq⟩

end Zalcman
