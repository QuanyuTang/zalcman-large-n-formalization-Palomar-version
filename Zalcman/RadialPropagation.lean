/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.DiameterPropagation
public import Zalcman.PositiveRadiusPropagation
import Mathlib.Tactic.Positivity

/-!
# Common radial propagation constants
-/

public section

namespace Zalcman

/-- Given the low-degree coefficient bounds, both analytic radial deficits
propagate with the same constants. -/
theorem exists_radial_deficit_propagation_of_low_degree
    (hm : ∀ {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ), 0 ≤ (milinCoefficients hf).milinSum n)
    {C : ℝ} (hC : 0 ≤ C)
    (hLow : ∀ {f : ℂ → ℂ}, NormalizedUnivalent f →
      |(coeff f 4 - 2 * coeff f 2).re| ≤ C * (3 - (coeff f 3).re)) :
    ∃ K : ℝ, 0 < K ∧ ∃ B : ℝ, 0 < B ∧
      ∀ {f : ℂ → ℂ}, NormalizedUnivalent f → ∀ {γ : ℂ}, ‖γ‖ = 1 →
      ∀ {r s : ℝ}, Real.tanh 2 ≤ r → 0 < r → r ≤ s → s < 1 →
        radialPhaseDeficit f γ s ≤ K * ((1 - r) / (1 - s)) ^ B * radialPhaseDeficit f γ r ∧
        oddRadialPhaseDeficit f γ s ≤ K * ((1 - r) / (1 - s)) ^ B * oddRadialPhaseDeficit f γ r := by
  obtain ⟨K₁, hK₁, B₁, hB₁, hPos⟩ := exists_positive_radius_deficit_propagation
  obtain ⟨K₂, hK₂, B₂, hB₂, hOdd⟩ := exists_odd_radius_deficit_propagation_of_low_degree hm hC hLow
  let K := max K₁ K₂
  let B := max B₁ B₂
  have hK : 0 < K := hK₁.trans_le (le_max_left _ _)
  refine ⟨K, hK, B, hB₁.trans_le (le_max_left _ _), ?_⟩
  intro f hf γ hγ r s hr₀ hr hrs hs
  have hCoeff (n : ℕ) := norm_coeff_le_of_milinSum_nonneg hf (hm hf n)
  let a := (1 - r) / (1 - s)
  have ha : 1 ≤ a := (le_div_iff₀ (sub_pos.mpr hs)).mpr (by simpa using sub_le_sub_left hrs 1)
  have hUpper (k b : ℝ) (hk : k ≤ K) (hb : b ≤ B) :
      k * a ^ b ≤ K * a ^ B :=
    mul_le_mul hk (Real.rpow_le_rpow_of_exponent_le ha hb)
      (Real.rpow_nonneg (zero_le_one.trans ha) _) hK.le
  have hr₁ : r < 1 := hrs.trans_lt hs
  have hPos₀ := radialPhaseDeficit_nonneg hf hγ hCoeff hr hr₁
  have hOdd₀ : 0 ≤ oddRadialPhaseDeficit f γ r := by
    rw [oddRadialPhaseDeficit_eq_series hf γ hr hr₁]
    apply mul_nonneg (zero_le_one.trans (oddRadialPhaseDeficit_prefactor_bounds hr hr₁).1)
    apply radialDeficitSeries_nonneg _ hr.le
    intro j
    unfold oddCoefficientDeficits
    split
    · exact (radialCoefficientDeficit_bounds hγ hCoeff j).1
    · exact le_rfl
  exact ⟨(hPos hf hCoeff hγ hr₀ hr hrs hs).trans
      (mul_le_mul_of_nonneg_right (hUpper K₁ B₁ (le_max_left _ _) (le_max_left _ _)) hPos₀),
    (hOdd hf hγ hr₀ hr hrs hs).trans
      (mul_le_mul_of_nonneg_right (hUpper K₂ B₂ (le_max_right _ _) (le_max_right _ _)) hOdd₀)⟩

end Zalcman
