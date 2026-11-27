module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# The Zalcman inequality for sufficiently large indices

The hypotheses express that the restriction of `f` to the open unit disk is
holomorphic and injective, with Taylor series starting with `z`. One threshold
works for the entire class, and equality characterizes the rotations of Koebe
on that disk.
-/

@[expose] public section

namespace Zalcman

open scoped ComplexConjugate

/-- The open unit disk in the complex plane. -/
def unitDisk : Set ℂ := Metric.ball 0 1

/-- The coefficient of `z ^ n` in the Taylor expansion at zero. -/
noncomputable def coeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

/-- The Koebe function. -/
noncomputable def koebe (z : ℂ) : ℂ := z / (1 - z) ^ 2

/-- The large-index Zalcman inequality, with its equality characterization. -/
theorem main_result :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ f : ℂ → ℂ,
      DifferentiableOn ℂ f unitDisk → Set.InjOn f unitDisk →
      f 0 = 0 → deriv f 0 = 1 → ∀ n : ℕ, N ≤ n →
      ‖coeff f n ^ 2 - coeff f (2 * n - 1)‖ ≤ ((n : ℝ) - 1) ^ 2 ∧
      (‖coeff f n ^ 2 - coeff f (2 * n - 1)‖ = ((n : ℝ) - 1) ^ 2 ↔
        ∃ lam : ℂ, ‖lam‖ = 1 ∧ Set.EqOn f (fun z ↦ conj lam * koebe (lam * z)) unitDisk) := by
  sorry

end Zalcman
