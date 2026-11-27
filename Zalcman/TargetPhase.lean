/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.PhaseAlignment
public import Zalcman.TargetDeficit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Phase transfer from initial coefficient stability and the radial mass estimate

The initial block, the two prefix phase errors, and the odd-index mass bound
are the estimates needed to finish the target phase comparison.
-/

public section

namespace Zalcman.MilinCoefficients

open Finset
open scoped ComplexConjugate

/-- The real-part deficit at `2 * n - 1` after changing to the observed unit phase. -/
theorem phase_transfer_of_prefix_mass (d : MilinCoefficients) {α ω : ℂ}
    (hα : ‖α‖ = 1) (hω : ‖ω‖ = 1) {ρ : ℕ → ℝ} (hρ : ∀ l, 0 ≤ ρ l)
    (hrep : ∀ M, positiveMilinRow ρ M = d.milinSum (M + 1)) {n : ℕ} (hn : 32 ≤ n)
    (hlog : 1 ≤ Real.log (n : ℝ)) {M : ℝ} (hM : 0 ≤ M) (hMsmall : 64 * M ≤ n)
    (hblock : d.blockError α n ≤ M)
    (hmass : (∑ j ∈ (range (4 * n + 1)).filter Odd, d.phaseDeficit α j) ≤ (n : ℝ) * M)
    (hphase : ‖1 - α‖ ^ 2 + ‖ω - α ^ 2‖ ^ 2 ≤ M * Real.log (n : ℝ) / Real.sqrt (n : ℝ)) :
    (↑(2 * n - 1 : ℕ) : ℝ) - (conj ω ^ 2 * d.squareCoeff (2 * n - 1)).re ≤
      2216 * Real.sqrt (n : ℝ) * M * Real.log (n : ℝ) := by
  let m : ℕ := 2 * n - 1
  let L := Real.log (n : ℝ)
  let Q := Real.sqrt (n : ℝ)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hQ : 0 < Q := Real.sqrt_pos_of_pos hn0
  have hL : 1 ≤ L := hlog
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hm : 0 < m := by dsimp [m]; omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hT : 0 ≤ d.milinSum m := by
    rw [← Nat.sub_add_cancel (show 1 ≤ m by omega), ← hrep, positiveMilinRow]
    exact sum_nonneg fun l _ => mul_nonneg (connectionCoefficient_nonneg _ _) (hρ l)
  have htarget := d.phaseDeficit_target_le hα hρ hrep hn hM hMsmall hblock hmass
  change d.phaseDeficit α m ≤ 1100 * Q * M at htarget
  have hchange := phase_deficit_le_of_change hm0 (d.norm_squareCoeff_le_index hm hT) hα hω
  change (m : ℝ) - (conj ω ^ 2 * d.squareCoeff m).re ≤
    2 * d.phaseDeficit α m + (m : ℝ) * ‖1 - α ^ 2 * conj ω ^ 2‖ ^ 2 at hchange
  have hsq := (norm_one_sub_phaseAdjustment_sq_le hα hω).trans
    (mul_le_mul_of_nonneg_left hphase (by norm_num))
  change ‖1 - α ^ 2 * conj ω ^ 2‖ ^ 2 ≤ 8 * (M * L / Q) at hsq
  have hml : (m : ℝ) ≤ 2 * n := by
    exact_mod_cast (show m ≤ 2 * n by dsimp [m]; omega)
  have hq2 : Q ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hcost : (m : ℝ) * ‖1 - α ^ 2 * conj ω ^ 2‖ ^ 2 ≤ 16 * Q * M * L := calc
    _ ≤ (m : ℝ) * (8 * (M * L / Q)) := mul_le_mul_of_nonneg_left hsq hm0.le
    _ ≤ (2 * (n : ℝ)) * (8 * (M * L / Q)) := mul_le_mul_of_nonneg_right hml (by positivity)
    _ = _ := by rw [← hq2]; field_simp; ring
  have hlogFactor : Q * M ≤ Q * M * L := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hL (mul_nonneg hQ.le hM)
  change (m : ℝ) - (conj ω ^ 2 * d.squareCoeff m).re ≤ 2216 * Q * M * L
  linarith only [hchange, hcost, htarget, hlogFactor]

end Zalcman.MilinCoefficients
