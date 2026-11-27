/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.PrefixScale
public import Zalcman.PrefixLogEstimate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The reference phase approaches one

The small-deficit Milin estimates and a nearly constant block bound all low
logarithmic coefficients. The harmonic majorant then estimates its unit phase.
-/

public section

namespace Zalcman.MilinCoefficients

open Filter Finset

/-- A unit constant approximating a nearly saturated Taylor block is close to one. -/
theorem exists_prefix_phase_bound {C : ℝ} (hC : 0 ≤ C) :
    ∃ K > 0, ∃ N : ℕ, ∀ (d : MilinCoefficients) (n : ℕ), N ≤ n →
      (∀ j, 0 ≤ d.milinSum j) → ∀ {α : ℂ}, ‖α‖ = 1 →
      let D := (n : ℝ) - ‖d.squareCoeff n‖
      D ≤ 3 → (∑ j ∈ range n, ‖d.c j - α‖ ^ 2) ≤ C * D →
      ‖1 - α‖ ^ 2 ≤ K * D * Real.log (n : ℝ) ^ 2 / Real.sqrt (n : ℝ) := by
  let B := 1 + Real.sqrt (3 * C)
  let A := 64 + 6 * (B ^ 4 * (6912 * 288) + (B ^ 2 + 1) * C)
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨N₁, hN₁, hrems⟩ := exists_index_for_small_remainders
  obtain ⟨N₂, hN₂, hsmall⟩ := exists_prefix_smallExponent_threshold hA
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)))
  obtain ⟨N₃, hN₃⟩ := exists_nat_ge x₀
  refine ⟨4 * C + 64 * A, by positivity, max N₁ (max N₂ N₃), ?_⟩
  intro d n hn hT α hα D hD hClose
  have hn₁ : N₁ ≤ n := by omega
  have hn₂ : N₂ ≤ n := by omega
  have hn₃ : N₃ ≤ n := by omega
  have hn₀ : 6 ≤ n := hN₁.trans hn₁
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD₀ : 0 ≤ D := sub_nonneg.mpr (d.norm_squareCoeff_le_index (by omega) (hT n))
  let J := n.sqrt
  obtain ⟨hJ, hJn, hJ₂, hJlo⟩ := prefix_sqrt_bounds (hN₂.trans hn₂)
  change 0 < J at hJ
  change 2 * J ≤ n at hJn
  change J ^ 2 ≤ n at hJ₂
  change Real.sqrt (n : ℝ) / 2 ≤ (J : ℝ) at hJlo
  have hJR : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hQ : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos_of_pos hnr
  have hLog : 1 ≤ Real.log (n : ℝ) := hx₀ (n : ℝ) (hN₃.trans (by exact_mod_cast hn₃))
  have hCoeff (i : ℕ) (hi : i < n) : ‖d.c i‖ ≤ B := by
    have hSq := (single_le_sum (f := fun j => ‖d.c j - α‖ ^ 2)
      (fun j _ => sq_nonneg _) (mem_range.mpr hi)).trans hClose
    have hLe : ‖d.c i - α‖ ≤ Real.sqrt (3 * C) := by
      apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
      exact hSq.trans (by nlinarith only [mul_le_mul_of_nonneg_left hD hC])
    have hNorm := norm_sub_le (d.c i - α) (-α)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg, hα] at hNorm
    dsimp only [B]
    linarith
  have hS := sum_remainder_Ico_le hJ hJn hJ₂ (hrems d n hn₁ (hT n) hD).2.2
  have hR := sum_partialMass_ratio_error_Ico_le hn₀ hJ hJn hT hD
  let ε := Real.sqrt (A * D / (J : ℝ))
  have hε : 0 ≤ ε := Real.sqrt_nonneg _
  have hε₂ : ε ^ 2 = A * D / (J : ℝ) := Real.sq_sqrt (by positivity)
  have ht (k : ℕ) (hk : 0 < k) (hkJ : k ≤ J) : ‖d.t k - 1‖ ≤ ε := by
    have h := mul_norm_logCoeff_sub_one_sq_le hJn hk hkJ hα hCoeff hClose hR hS
    have h' : (J : ℝ) * ‖d.t k - 1‖ ^ 2 ≤ A * D :=
      h.trans_eq (by dsimp only [A]; ring)
    have hsq := (le_div_iff₀ hJR).mpr (by simpa only [mul_comm (J : ℝ)] using h')
    rw [← hε₂] at hsq
    exact (sq_le_sq₀ (norm_nonneg _) hε).mp hsq
  have hsmall' : ε * (1 + Real.log (n : ℝ)) ≤ 1 := hsmall n hn₂ D hD₀ hD
  have hαbound := d.norm_phase_sub_one_sq_le_of_small_log_prefix (by omega : J < n)
    hε hClose ht hsmall'
  rw [hε₂] at hαbound
  have hQJ : Real.sqrt (n : ℝ) / 2 ≤ (J : ℝ) + 1 := by linarith
  have hLogSq : (1 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
    nlinarith only [hLog, sq_nonneg (Real.log (n : ℝ) - 1)]
  have h1 : 2 * (C * D) / ((J : ℝ) + 1) ≤
      (4 * C * D) * Real.log (n : ℝ) ^ 2 / Real.sqrt (n : ℝ) := calc
    _ ≤ 2 * (C * D) / (Real.sqrt (n : ℝ) / 2) := by gcongr
    _ = (4 * C * D) / Real.sqrt (n : ℝ) := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hQ.le
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hLogSq (show 0 ≤ 4 * C * D by positivity)
  have h2 : 8 * (A * D / (J : ℝ)) * (1 + Real.log (n : ℝ)) ^ 2 ≤
      64 * A * D * Real.log (n : ℝ) ^ 2 / Real.sqrt (n : ℝ) := calc
    _ ≤ 8 * (A * D / (Real.sqrt (n : ℝ) / 2)) * (2 * Real.log (n : ℝ)) ^ 2 := by
      gcongr <;> linarith
    _ = _ := by ring
  rw [norm_sub_rev 1]
  calc
    _ ≤ _ := hαbound
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

end Zalcman.MilinCoefficients
