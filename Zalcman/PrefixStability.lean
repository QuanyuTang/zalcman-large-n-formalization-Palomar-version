/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CyclicReduction
public import Zalcman.Gram
public import Zalcman.PrefixPhaseEstimate
public import Zalcman.RotatedBlock
import Zalcman.CoefficientBound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A rotated initial block with controlled phase

Shift stability gives one geometric mode. Rotating makes it a constant
mode, and the logarithmic coefficients then control its phase.
-/

public section

namespace Zalcman

open Filter Finset
open scoped ComplexConjugate

/-- Nearly saturated coefficients have the rotated block and phase bounds. -/
theorem exists_rotated_initial_prefix_estimates
    (hm : ∀ {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (j : ℕ), 0 ≤ (milinCoefficients hf).milinSum j) :
    ∃ A > 0, ∃ P > 0, ∃ N : ℕ, ∀ {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ), N ≤ n →
      let D := (n : ℝ) - ‖coeff f n‖
      D ≤ 3 → ∃ (lam : ℂ) (hlam : ‖lam‖ = 1) (α : ℂ), ‖α‖ = 1 ∧
        let g := rotate lam f
        let dg := milinCoefficients (rotate_normalizedUnivalent hf hlam)
        let ω := coeff g n / (‖coeff g n‖ : ℂ)
        dg.blockError α n ≤ A * D ∧
          ‖1 - α‖ ^ 2 + ‖ω - α ^ 2‖ ^ 2 ≤ P * D * Real.log (n : ℝ) ^ 2 / Real.sqrt (n : ℝ) := by
  let S : ℝ := 1152 * 8 * 6920
  let G : ℝ := 34 * S
  let A : ℝ := 1 + 2 * G
  let R : ℝ := 4 * (1 + G)
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  obtain ⟨N₁, hN₁, hShift⟩ := MilinCoefficients.exists_index_for_shift_stability
  obtain ⟨Q, hQ, N₂, hAlpha⟩ := MilinCoefficients.exists_prefix_phase_bound hA.le
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)))
  obtain ⟨N₃, hN₃⟩ := exists_nat_ge x₀
  obtain ⟨N₄, hN₄⟩ := exists_nat_gt (3 * (1 + G))
  refine ⟨A, hA, Q + 3 * R ^ 2, by positivity, max N₁ (max N₂ (max N₃ N₄)), ?_⟩
  intro f hf n hn D hD
  have hn₀ : 6 ≤ n := hN₁.trans (by omega)
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hn₁R : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn₆R : (6 : ℝ) ≤ n := by exact_mod_cast hn₀
  have hD₀ : 0 ≤ D := sub_nonneg.mpr (norm_coeff_le_of_milinSum_nonneg hf (hm hf n))
  have hnLarge : 3 * (1 + G) < (n : ℝ) := hN₄.trans_le (by exact_mod_cast (show N₄ ≤ n by omega))
  have hLog := hx₀ (n : ℝ) (hN₃.trans (by exact_mod_cast (show N₃ ≤ n by omega)))
  let d := milinCoefficients hf
  have hD' : (n : ℝ) - ‖d.squareCoeff n‖ = D := by
    rw [milinCoefficients_squareCoeff hf]
  have hAll (j : ℕ) (hj : j ≤ n / 2) : ∃ v : ℂ, ‖v‖ = 1 ∧
      (∑ i ∈ range (n - j), ‖d.c (i + j) - v * d.c i‖ ^ 2) ≤ S * D := by
    cases j with
    | zero =>
      refine ⟨1, norm_one, ?_⟩
      simpa using mul_nonneg hS hD₀
    | succ j =>
      obtain ⟨v, hv, he⟩ := hShift d n (j + 1) (by omega) (by omega) hj (hm hf)
        (hD'.trans_le hD)
      exact ⟨v, hv, by simpa only [hD', S] using he⟩
  obtain ⟨β, lam, hlam, hGeom⟩ := exists_geometric_approximation_of_shifts d.c
    (n := n) (H := n / 2) (by omega) (by omega) (by omega) (mul_nonneg hS hD₀) hAll
  have hGeom' : (∑ j ∈ range n, ‖rootCoeff hf j - β * lam ^ j‖ ^ 2) ≤ G * D :=
    hGeom.trans_eq (by dsimp only [G]; ring)
  have hNear : D + G * D < (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hD (show 0 ≤ 1 + G by positivity)
    nlinarith only [h, hnLarge]
  obtain ⟨α, hα, hBlock, hOmega⟩ := exists_reference_phase_of_geometric_approx hf hlam hnpos
    hGeom' hNear (by linarith only [hD, hn₆R]) (fun hg ↦ hm hg n)
  have hlam' : ‖conj lam‖ = 1 := by simpa only [Complex.norm_conj] using hlam
  let g := rotate (conj lam) f
  let hg := rotate_normalizedUnivalent hf hlam'
  let dg := milinCoefficients hg
  let ω := coeff g n / (‖coeff g n‖ : ℂ)
  have hEqD : (n : ℝ) - ‖dg.squareCoeff n‖ = D := by
    rw [show dg.squareCoeff n = coeff (rotate (conj lam) f) n from
      milinCoefficients_squareCoeff hg n, coeff_rotate f hlam' (show 1 ≤ n by omega),
      norm_mul, norm_pow, hlam', one_pow, one_mul]
  have hBlock' : dg.blockError α n ≤ A * D := hBlock.trans_eq (by dsimp only [A]; ring)
  have hAlpha' := hAlpha dg n (by omega) (hm hg) hα (hEqD.trans_le hD) (by
    rw [← dg.blockError_eq_sum_norm_sub hα, hEqD]
    exact hBlock')
  rw [hEqD] at hAlpha'
  have hΩ : ‖ω - α ^ 2‖ ≤ R * D / n :=
    hOmega.trans_eq (by dsimp only [R]; ring)
  have hΩ₂ := pow_le_pow_left₀ (norm_nonneg _) hΩ 2
  let X := Real.sqrt (n : ℝ)
  have hX : 0 < X := Real.sqrt_pos_of_pos hnR
  have hXn : X ≤ (n : ℝ) ^ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le hn₁R (by norm_num : (1 / 2 : ℝ) ≤ 2)
    simpa only [← Real.sqrt_eq_rpow, Real.rpow_two] using h
  have hD₂ : D ^ 2 ≤ 3 * D := by nlinarith only [mul_nonneg hD₀ (sub_nonneg.mpr hD)]
  have hΩ' : ‖ω - α ^ 2‖ ^ 2 ≤ 3 * R ^ 2 * D * Real.log (n : ℝ) ^ 2 / X := by
    calc
      _ ≤ R ^ 2 * D ^ 2 / (n : ℝ) ^ 2 := hΩ₂.trans_eq (by rw [div_pow, mul_pow])
      _ ≤ (3 * R ^ 2 * D) / (n : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        nlinarith only [mul_le_mul_of_nonneg_left hD₂ (sq_nonneg R)]
      _ ≤ (3 * R ^ 2 * D) / X := div_le_div_of_nonneg_left (by positivity) hX hXn
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hX.le
        have hLogSq : 1 ≤ Real.log (n : ℝ) ^ 2 := by
          nlinarith only [hLog, sq_nonneg (Real.log (n : ℝ) - 1)]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hLogSq (show 0 ≤ 3 * R ^ 2 * D by positivity)
  exact ⟨conj lam, hlam', α, hα, hBlock', (add_le_add hAlpha' hΩ').trans_eq (by ring)⟩

end Zalcman
