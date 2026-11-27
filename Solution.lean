module

public import Zalcman.LargeIndex

public section

namespace Zalcman

open scoped ComplexConjugate

/-- The large-index Zalcman inequality, with its equality characterization. -/
theorem main_result :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ f : ℂ → ℂ,
      DifferentiableOn ℂ f unitDisk → Set.InjOn f unitDisk →
      f 0 = 0 → deriv f 0 = 1 → ∀ n : ℕ, N ≤ n →
      ‖coeff f n ^ 2 - coeff f (2 * n - 1)‖ ≤ ((n : ℝ) - 1) ^ 2 ∧
      (‖coeff f n ^ 2 - coeff f (2 * n - 1)‖ = ((n : ℝ) - 1) ^ 2 ↔
        ∃ lam : ℂ, ‖lam‖ = 1 ∧ Set.EqOn f (fun z ↦ conj lam * koebe (lam * z)) unitDisk) := by
  obtain ⟨N, hN, h⟩ := zalcman_large_n
  refine ⟨N, hN, ?_⟩
  intro f hf hi h₀ h₁ n hn
  exact h f ⟨hf, hi, h₀, h₁⟩ n hn

end Zalcman
