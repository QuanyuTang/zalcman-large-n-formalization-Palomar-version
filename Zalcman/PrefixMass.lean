/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CoefficientBlocks
public import Zalcman.MilinComparison
public import Zalcman.MilinStability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite phase-deficit sums on the initial block

The reflection formula bounds all deficits through the partial masses. On the
matching parity class, the Milin row comparison improves the dependence on the
coefficient deficit from square-root to linear.
-/

public section

namespace Zalcman.MilinCoefficients

open Finset

variable (d : MilinCoefficients)

private theorem milin_nonnegative_of_rows {ρ : ℕ → ℝ} (hρ : ∀ l, 0 ≤ ρ l)
    (hrep : ∀ M, positiveMilinRow ρ M = d.milinSum (M + 1)) (j : ℕ) : 0 ≤ d.milinSum j := by
  cases j with
  | zero => simp [milinSum]
  | succ M =>
    rw [← hrep, positiveMilinRow]
    exact sum_nonneg fun l _ => mul_nonneg (connectionCoefficient_nonneg M l) (hρ l)

/-- The matching-parity initial deficits have a linear bound in the initial coefficient deficit. -/
theorem sum_phaseDeficit_sameParity_le {α : ℂ} (hα : ‖α‖ = 1) {ρ : ℕ → ℝ} (hρ : ∀ l, 0 ≤ ρ l)
    (hrep : ∀ M, positiveMilinRow ρ M = d.milinSum (M + 1)) {N : ℕ} (hN : 6 ≤ N + 1)
    (hD : ((N + 1 : ℕ) : ℝ) - ‖d.squareCoeff (N + 1)‖ ≤ 3) :
    let n : ℝ := (N + 1 : ℕ)
    let D := n - ‖d.squareCoeff (N + 1)‖
    (∑ M ∈ (range (N + 1)).filter (fun M : ℕ => (M : ℤ) ≡ (N : ℤ) [ZMOD 2]),
      d.phaseDeficit α (M + 1)) ≤
      n * ((4 + 2 * Real.log n) * D + 2 * d.blockError α (N + 1)) := by
  let n : ℝ := (N + 1 : ℕ)
  let D := n - ‖d.squareCoeff (N + 1)‖
  let E := d.blockError α (N + 1)
  let s := (range (N + 1)).filter (fun M : ℕ => (M : ℤ) ≡ (N : ℤ) [ZMOD 2])
  change (∑ M ∈ s, d.phaseDeficit α (M + 1)) ≤ n * ((4 + 2 * Real.log n) * D + 2 * E)
  have hT := d.milin_nonnegative_of_rows hρ hrep
  have hD₀ : 0 ≤ D := sub_nonneg.mpr (d.norm_squareCoeff_le_index (by omega) (hT (N + 1)))
  have hE₀ : 0 ≤ E := d.blockError_nonneg α _
  have hn₀ : 0 < n := by dsimp [n]; positivity
  have hslack := d.logRemainder_and_milinSum_le_of_deficit hN (hT _) hD
  change d.logRemainder (N + 1) ≤ 2 * D / n ∧ d.milinSum (N + 1) ≤ 2 * D at hslack
  have hbound (M : ℕ) (hM : M ∈ s) : d.phaseDeficit α (M + 1) ≤
      d.milinSum (M + 1) + (2 * D + 2 * E) := by
    have hM' := mem_range.mp (mem_filter.mp hM).1
    have hLpos : 0 ≤ d.logRemainder (M + 1) := d.logRemainder_nonneg (by omega)
    have hLM := d.logRemainder_le_of_le (i := M + 1) (j := N + 1) (by omega) (by omega)
    have hL : (↑(M + 1 : ℕ) : ℝ) * d.logRemainder (M + 1) ≤ 2 * D := calc
      _ ≤ n * d.logRemainder (N + 1) := mul_le_mul (by dsimp [n]; exact_mod_cast (show M + 1 ≤ N + 1 by omega))
        hLM hLpos hn₀.le
      _ ≤ n * (2 * D / n) := mul_le_mul_of_nonneg_left hslack.1 hn₀.le
      _ = _ := by field_simp
    have hE := d.blockError_mono α (show M + 1 ≤ N + 1 by omega)
    have hh := d.phaseDeficit_le_milinSum_add_logRemainder_add_blockError hα (j := M + 1) (by omega)
    linarith only [hL, hE, hh]
  have hcomp := sum_positiveMilinRow_sameParity_le hρ N
  simp only [hrep, ← Nat.cast_succ] at hcomp
  change (∑ M ∈ s, d.milinSum (M + 1)) ≤ n * (1 + Real.log n) * d.milinSum (N + 1) at hcomp
  have hcount : (s.card : ℝ) ≤ n := by
    have hs : s ⊆ range (N + 1) := filter_subset _ _
    change (s.card : ℝ) ≤ ((N + 1 : ℕ) : ℝ)
    exact_mod_cast (card_le_card hs).trans_eq (card_range _)
  have hnlog : 0 ≤ n * (1 + Real.log n) := by
    have hn₁ : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ N + 1 by omega)
    exact mul_nonneg hn₀.le (by linarith only [Real.log_nonneg hn₁])
  calc
    _ ≤ ∑ M ∈ s, (d.milinSum (M + 1) + (2 * D + 2 * E)) := sum_le_sum hbound
    _ = (∑ M ∈ s, d.milinSum (M + 1)) + (s.card : ℝ) * (2 * D + 2 * E) := by
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul]
      ring
    _ ≤ n * (1 + Real.log n) * (2 * D) + n * (2 * D + 2 * E) :=
      add_le_add (hcomp.trans (mul_le_mul_of_nonneg_left hslack.2 hnlog))
        (mul_le_mul_of_nonneg_right hcount (by positivity))
    _ = _ := by ring

/-- The total initial phase deficit is controlled by the partial mass estimates. -/
theorem sum_phaseDeficit_prefix_le {α : ℂ} (hα : ‖α‖ = 1) (hT : ∀ j, 0 ≤ d.milinSum j)
    {n : ℕ} (hn : 6 ≤ n) (hD : (n : ℝ) - ‖d.squareCoeff n‖ ≤ 3) :
    (∑ i ∈ range n, d.phaseDeficit α (i + 1)) ≤
      (n : ℝ) * (Real.sqrt (24 * n * ((n : ℝ) - ‖d.squareCoeff n‖)) + 2 * d.blockError α n) := by
  let D : ℝ := n - ‖d.squareCoeff n‖
  have hD₀ : 0 ≤ D := sub_nonneg.mpr (d.norm_squareCoeff_le_index (by omega) (hT n))
  calc
    _ ≤ ∑ _i ∈ range n, (Real.sqrt (24 * n * D) + 2 * d.blockError α n) := by
      apply sum_le_sum
      intro i hi
      have hi' := mem_range.mp hi
      have hsq := d.partialMass_deficit_sq_le hT hn (show i + 1 ≤ n by omega) hD
      have hcast : (↑(i + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show i + 1 ≤ n by omega)
      have hsq' : ((↑(i + 1 : ℕ) : ℝ) - d.partialMass (i + 1)) ^ 2 ≤ 24 * n * D :=
        hsq.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcast (by norm_num)) hD₀)
      have hbound : (↑(i + 1 : ℕ) : ℝ) - d.partialMass (i + 1) ≤ Real.sqrt (24 * n * D) := by
        have hs := Real.sqrt_le_sqrt hsq'
        rw [Real.sqrt_sq_eq_abs] at hs
        exact (le_abs_self _).trans hs
      have hblock := d.blockError_mono α (show i + 1 ≤ n by omega)
      have hh := d.phaseDeficit_le_massDeficit_add_blockError hα (i + 1)
      linarith only [hh, hbound, hblock]
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul, D]

end Zalcman.MilinCoefficients
