/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Area
public import Zalcman.CoefficientBound
public import Zalcman.Reduction

/-!
# Assembly of the analytic inputs for the large-index bound
-/

public section

open scoped ComplexConjugate

namespace Zalcman

/-- The analytic inputs for the eventual Zalcman bound are Milin positivity and phase transfer. -/
theorem eventually_zalcman_of_milin_nonnegative_and_phase_transfer
    (hMilin : ∀ {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ),
      0 ≤ (milinCoefficients hf).milinSum n)
    {C : ℝ} {N₀ : ℕ} (hC : 0 < C)
    (hTransfer : ∀ {f : ℂ → ℂ}, NormalizedUnivalent f → ∀ n : ℕ, N₀ ≤ n →
      (n : ℝ) - ‖coeff f n‖ ≤ 3 →
        (↑(2 * n - 1 : ℕ) : ℝ) -
          (conj (coeff f n / (‖coeff f n‖ : ℂ)) ^ 2 * coeff f (2 * n - 1)).re ≤
          C * ((n : ℝ) - ‖coeff f n‖) * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ 2) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ {f : ℂ → ℂ}, NormalizedUnivalent f → ∀ n : ℕ, N ≤ n →
      ‖coeff f n ^ 2 - coeff f (2 * n - 1)‖ ≤ ((n : ℝ) - 1) ^ 2 ∧
      (‖coeff f n ^ 2 - coeff f (2 * n - 1)‖ = ((n : ℝ) - 1) ^ 2 ↔ IsKoebeRotation f) := by
  obtain ⟨N, hN, h⟩ := eventually_zalcman_of_phase_transfer
    (F := {f : ℂ → ℂ // NormalizedUnivalent f}) (fun f => coeff f.val)
    (fun f => IsKoebeRotation f.val)
    (fun f n => norm_coeff_le_of_milinSum_nonneg f.property (hMilin f.property n))
    (fun f n hn heq => isKoebeRotation_of_norm_coeff_two_eq f.property
      (norm_coeff_two_eq_of_norm_coeff_eq f.property hn (hMilin f.property n) heq))
    (fun _ hf => hf.coefficients) hC
    (fun f n hn hD => hTransfer f.property n hn hD)
  exact ⟨N, hN, fun hf n hn => h ⟨_, hf⟩ n hn⟩

end Zalcman
