/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CoefficientBlocks
public import Zalcman.CoefficientSelection
public import Zalcman.MilinComparison
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The real-part coefficient deficit at twice the initial index

A positive Milin representation compares the logarithmic deficit terms, while reflection
extends the initial block. This file combines those estimates with the odd-index mass bound.
-/

public section

namespace Zalcman.MilinCoefficients

open Finset
open scoped ComplexConjugate

variable (d : MilinCoefficients)

/-- A small phase deficit bounds both logarithmic quantities at the same index. -/
theorem milinSum_and_mul_logRemainder_le_of_phaseDeficit {α : ℂ} (hα : ‖α‖ = 1)
    {j : ℕ} (hj : 0 < j) (hT : 0 ≤ d.milinSum j)
    (hsmall : d.phaseDeficit α j ≤ (j : ℝ) / 2) :
    d.milinSum j ≤ 2 * d.phaseDeficit α j ∧
      (j : ℝ) * d.logRemainder j ≤ 2 * d.phaseDeficit α j := by
  let A := d.partialMass j
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hApos : 0 < A := d.partialMass_pos hj
  have hAle : A ≤ j := d.partialMass_le_index hj hT
  have hmass : (j : ℝ) - A ≤ d.phaseDeficit α j := by
    rw [d.phaseDeficit_eq_reflection hα]
    have hsum : 0 ≤ ∑ i ∈ range j,
        ‖d.phasedCoeff α i - conj (d.phasedCoeff α (j - 1 - i))‖ ^ 2 :=
      sum_nonneg (fun _ _ => sq_nonneg _)
    dsimp only [A]
    linarith
  have hAhalf : (j : ℝ) / 2 ≤ A := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hj' hApos)
  have hjratio : (j : ℝ) / A ≤ 2 := (div_le_iff₀ hApos).mpr (by linarith)
  have hbound : (j : ℝ) * Real.log (j / A) ≤ 2 * d.phaseDeficit α j := calc
    _ ≤ (j : ℝ) * ((j : ℝ) / A - 1) := mul_le_mul_of_nonneg_left hlog hj'.le
    _ = ((j : ℝ) / A) * ((j : ℝ) - A) := by field_simp
    _ ≤ 2 * ((j : ℝ) - A) := mul_le_mul_of_nonneg_right hjratio (sub_nonneg.mpr hAle)
    _ ≤ _ := by gcongr
  have hsum : d.milinSum j + (j : ℝ) * d.logRemainder j = (j : ℝ) * Real.log (j / A) := by
    dsimp [A, logRemainder]
    field_simp
    ring
  have hL : 0 ≤ (j : ℝ) * d.logRemainder j := mul_nonneg hj'.le (d.logRemainder_nonneg hj)
  exact ⟨by linarith only [hbound, hsum, hL], by linarith only [hbound, hsum, hT]⟩

/-- The mass, initial block, and triangular representation control the target phase deficit. -/
theorem phaseDeficit_target_le {α : ℂ} (hα : ‖α‖ = 1) {ρ : ℕ → ℝ}
    (hρ : ∀ l, 0 ≤ ρ l) (hrep : ∀ M, positiveMilinRow ρ M = d.milinSum (M + 1))
    {n : ℕ} (hn : 32 ≤ n) {M : ℝ} (hM : 0 ≤ M) (hMsmall : 64 * M ≤ n)
    (hblock : d.blockError α n ≤ M)
    (hmass : (∑ j ∈ (range (4 * n + 1)).filter Odd, d.phaseDeficit α j) ≤ (n : ℝ) * M) :
    d.phaseDeficit α (2 * n - 1) ≤ 1100 * Real.sqrt (n : ℝ) * M := by
  have hrow {j : ℕ} (hj : 0 < j) : positiveMilinRow ρ (j - 1) = d.milinSum j := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ j by omega)] using hrep (j - 1)
  have hT (j : ℕ) (hj : 0 < j) : 0 ≤ d.milinSum j := by
    rw [← hrow hj, positiveMilinRow]
    exact sum_nonneg (fun i _ => mul_nonneg (connectionCoefficient_nonneg _ _) (hρ i))
  have hsign (j : ℕ) : 0 ≤ d.phaseDeficit α j := by
    by_cases hj : 0 < j
    · rw [d.phaseDeficit_eq_reflection hα]
      exact add_nonneg (sub_nonneg.mpr (d.partialMass_le_index hj (hT j hj)))
        (div_nonneg (sum_nonneg (fun _ _ => sq_nonneg _)) (by norm_num))
    · have : j = 0 := by omega
      simp [this, phaseDeficit, squareCoeff]
  obtain ⟨j₁, j₂, j₃, _, _, hj₃, h₁lo, h₁hi, h₂lo, h₂hi, h₃lo, h₃hi, hδ₁, hδ₂, hδ₃⟩ :=
    exists_small_odd_deficits (d.phaseDeficit α) hsign hn hM hmass
  let m := 2 * n - 1
  have hm : 0 < m := by dsimp [m]; omega
  have hj₁ : 0 < j₁ := by omega
  have hj₂ : 0 < j₂ := by omega
  have hj₃' : 0 < j₃ := by omega
  have hnear (j : ℕ) (hj : n ≤ j) (hδ : d.phaseDeficit α j ≤ 32 * M) :
      d.phaseDeficit α j ≤ (j : ℝ) / 2 := by
    have hj' : (n : ℝ) ≤ j := by exact_mod_cast hj
    linarith only [hδ, hMsmall, hj']
  have h₂ := d.milinSum_and_mul_logRemainder_le_of_phaseDeficit hα hj₂ (hT j₂ hj₂)
    (hnear j₂ (by omega) hδ₂)
  have h₃ := d.milinSum_and_mul_logRemainder_le_of_phaseDeficit hα hj₃' (hT j₃ hj₃')
    (hnear j₃ (by omega) hδ₃)
  have hmj : m ≤ j₂ := by dsimp only [m]; omega
  have hmj' : (m : ℝ) ≤ j₂ := by exact_mod_cast hmj
  have hL : (m : ℝ) * d.logRemainder m ≤ 64 * M := calc
    _ ≤ (j₂ : ℝ) * d.logRemainder j₂ := mul_le_mul hmj'
      (d.logRemainder_le_of_le hm hmj) (d.logRemainder_nonneg hm) (by positivity)
    _ ≤ _ := by linarith only [h₂.2, hδ₂]
  have hTc := positiveMilinRow_target_le hρ (n := n) (by omega) h₃lo h₃hi hj₃
  rw [show 2 * n - 2 = m - 1 by dsimp [m]; omega, hrow hm, hrow hj₃'] at hTc
  have hTm : d.milinSum m ≤ 512 * Real.sqrt (n : ℝ) * M := calc
    _ ≤ 8 * Real.sqrt (n : ℝ) * d.milinSum j₃ := hTc
    _ ≤ 8 * Real.sqrt (n : ℝ) * (64 * M) :=
      mul_le_mul_of_nonneg_left (by linarith only [h₃.1, hδ₃]) (by positivity)
    _ = _ := by ring
  have hE := d.blockError_le_of_cover hα (n := n) (j₁ := j₁) (j₂ := j₂) (m := m)
    (by omega) (by omega) (by omega) (by omega) (by dsimp [m]; omega)
    (d.partialMass_le_index hj₁ (hT j₁ hj₁)) (d.partialMass_le_index hj₂ (hT j₂ hj₂))
  have hEm : d.blockError α m ≤ 261 * M := by linarith only [hE, hblock, hδ₁, hδ₂]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := by simpa using Real.sqrt_le_sqrt hn'
  have htarget := d.phaseDeficit_le_milinSum_add_logRemainder_add_blockError hα hm
  change d.phaseDeficit α m ≤ _
  nlinarith only [htarget, hL, hTm, hEm, mul_nonneg (sub_nonneg.mpr hsqrt) hM, hM]

end Zalcman.MilinCoefficients
