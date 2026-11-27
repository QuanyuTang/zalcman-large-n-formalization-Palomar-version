/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.WeightTime
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# The Milin representation from logarithmic coefficient paths

The finite weights are fixed by the Chebyshev formula. The analytic input is an
absolutely continuous path of logarithmic coefficients satisfying the radial
equations almost everywhere and with the Koebe endpoint values.
-/

public section

noncomputable section

namespace Zalcman

open Finset MeasureTheory
open scoped BigOperators

/-- A radial logarithmic coefficient path ending at the Koebe values gives the common
nonnegative triangular representation of all the Milin sums of its initial function. -/
theorem exists_nonnegative_triangular_milin_representation_of_logCoeffChain
    (c : MilinCoefficients) (γ : ℕ → ℝ → ℂ) (κ : ℝ → ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hγ₀ : ∀ k, c.t (k + 1) = ((k : ℂ) + 1) * γ k 0)
    (hγT : ∀ k, γ k T = ((k : ℂ) + 1)⁻¹)
    (hAC : ∀ k, AbsolutelyContinuousOnInterval (γ k) 0 T)
    (hODE : ∀ᵐ u : ℝ ∂volume, u ∈ Set.Ioc 0 T → ‖κ u‖ = 1 ∧
      ∀ k, HasDerivAt (γ k)
        ((κ u) ^ (k + 1) + ((k : ℂ) + 1) * γ k u +
          2 * ∑ j ∈ range k, ((j : ℂ) + 1) * γ j u * (κ u) ^ (k - j)) u) :
    ∃ rho : ℕ → ℝ, rho 0 = 0 ∧ (∀ n, 0 ≤ rho n) ∧ ∀ M,
      (∑ n ∈ range (M + 1), connectionCoefficient M n * rho n) = c.milinSum (M + 1) := by
  let d (k : ℕ) : ℝ → ℂ := deriv (γ k)
  refine exists_nonnegative_triangular_milin_representation_of_weightedLogEnergy c γ d
    radialWeightTau hT (fun _ _ hk ↦ radialWeightTau_zero hk.le) hγ₀ hγT ?_ ?_ ?_
  · intro M
    exact absolutelyContinuousOnInterval_weightedLogEnergy γ (radialWeightTau M) M
      (fun k _ ↦ hAC k) (fun _ hk ↦ absolutelyContinuousOnInterval_radialWeightTau hk.le 0 T)
  · intro M
    filter_upwards [hODE] with u hu hmem
    obtain ⟨hκ, hγ⟩ := hu hmem
    have hWeight := hasDerivAt_weightedLogEnergy γ (radialWeightTau M)
      (fun k ↦ radialWeightLambda M k u) (fun k ↦ d k u) hκ M
      (fun k _ ↦ (hγ k).differentiableAt.hasDerivAt) (fun k _ ↦ (hγ k).deriv)
      (fun _ hk ↦ hasDerivAt_radialWeightTau hk.le u)
      (fun k _ ↦ radialWeightTau_succ_sub M k u)
      (radialWeightTau_eq_zero_of_le le_rfl u) (radialWeightLambda_eq_zero_of_le le_rfl u)
    simpa only [chebyshevEnergyRow, radialWeightLambda] using hWeight
  · intro n
    exact (measurable_legendreEnergyColumn d (fun k ↦ measurable_deriv (γ k)) n).aestronglyMeasurable

end Zalcman
