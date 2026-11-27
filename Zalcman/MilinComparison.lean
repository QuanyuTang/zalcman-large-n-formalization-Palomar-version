/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.ConnectionFormula
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Comparison of rows of the positive Milin representation

The connection-coefficient bounds give a harmonic estimate for the sum of earlier rows
of matching parity and a square-root estimate comparing the target row to a later one.
-/

public section

namespace Zalcman

open Finset

/-- The row indexed by `M` represents the Milin sum at index `M + 1`. -/
@[expose] noncomputable def positiveMilinRow (ρ : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ l ∈ range (M + 1), connectionCoefficient M l * ρ l

private theorem positiveMilinRow_eq_sum_range (ρ : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    positiveMilinRow ρ M = ∑ l ∈ range (N + 1), connectionCoefficient M l * ρ l := by
  apply sum_subset (range_mono (Nat.succ_le_succ hMN))
  intro l _ hl
  have hMl : M < l := by simp only [mem_range, not_lt] at hl; omega
  rw [connectionCoefficient_eq_zero_of_lt hMl, zero_mul]

private theorem sum_connectionCoefficient_sameParity_le (N l : ℕ) :
    (∑ M ∈ (range (N + 1)).filter (fun M : ℕ => (M : ℤ) ≡ (N : ℤ) [ZMOD 2]),
      connectionCoefficient M l) ≤
      ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) * connectionCoefficient N l := by
  by_cases hpar : (N : ℤ) ≡ (l : ℤ) [ZMOD 2]
  · by_cases hlN : l ≤ N
    · let w := 2 * (l : ℝ) + 1
      let s := (range (N + 1)).filter (fun M : ℕ => (M : ℤ) ≡ (N : ℤ) [ZMOD 2])
      have hsum : (∑ M ∈ s, connectionCoefficient M l) ≤
          ∑ M ∈ Ico l (N + 1), w / ((M : ℝ) + 1 - l) := by
        calc
          _ = ∑ M ∈ s.filter (fun M => l ≤ M), connectionCoefficient M l := by
            symm
            apply sum_subset (filter_subset _ _)
            intro M hM hM'
            have hMl : M < l := lt_of_not_ge (fun h => hM' (mem_filter.mpr ⟨hM, h⟩))
            exact connectionCoefficient_eq_zero_of_lt hMl
          _ ≤ ∑ M ∈ s.filter (fun M => l ≤ M), w / ((M : ℝ) + 1 - l) := by
            apply sum_le_sum
            intro M hM
            obtain ⟨hM, hlM⟩ := mem_filter.mp hM
            exact (connectionCoefficient_bounds hlM ((mem_filter.mp hM).2.trans hpar)).2
          _ ≤ _ := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro M hM
              obtain ⟨hM, hlM⟩ := mem_filter.mp hM
              exact mem_Ico.mpr ⟨hlM, mem_range.mp (mem_filter.mp hM).1⟩
            · intro M hM _
              have hlM : (l : ℝ) ≤ M := by exact_mod_cast (mem_Ico.mp hM).1
              exact div_nonneg (by dsimp [w]; positivity) (by linarith)
      have hsum_harmonic : (∑ M ∈ Ico l (N + 1), w / ((M : ℝ) + 1 - l)) ≤
          w * (1 + Real.log ((N : ℝ) + 1)) := by
        rw [sum_Ico_eq_sum_range]
        have heq (i : ℕ) : w / ((↑(l + i : ℕ) : ℝ) + 1 - l) = w * ((i : ℝ) + 1)⁻¹ := by
          rw [show (↑(l + i : ℕ) : ℝ) + 1 - l = (i : ℝ) + 1 by push_cast; ring, div_eq_mul_inv]
        simp only [heq, ← mul_sum]
        have hmono := sum_le_sum_of_subset_of_nonneg
          (f := fun i : ℕ => ((i : ℝ) + 1)⁻¹)
          (range_mono (show N + 1 - l ≤ N + 1 by omega)) (fun _ _ _ => by positivity)
        have hlog := harmonic_le_one_add_log (N + 1)
        simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Nat.cast_succ, Rat.cast_add,
          Rat.cast_natCast, Rat.cast_one] at hlog
        exact mul_le_mul_of_nonneg_left (hmono.trans hlog) (by dsimp [w]; positivity)
      have hw : w ≤ ((N : ℝ) + 1) * connectionCoefficient N l := by
        have h := (connectionCoefficient_bounds hlN hpar).1
        simpa only [mul_comm ((N : ℝ) + 1)] using
          (div_le_iff₀ (by positivity : 0 < (N : ℝ) + 1)).mp h
      have hlog0 : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ (N : ℝ) + 1 by
          linarith only [Nat.cast_nonneg (α := ℝ) N])
        linarith
      calc
        _ ≤ w * (1 + Real.log ((N : ℝ) + 1)) := hsum.trans hsum_harmonic
        _ ≤ (((N : ℝ) + 1) * connectionCoefficient N l) * (1 + Real.log ((N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hw hlog0
        _ = _ := by ring
    · rw [connectionCoefficient_eq_zero_of_lt (by omega : N < l), mul_zero]
      apply le_of_eq
      apply sum_eq_zero
      intro M hM
      have hMN := mem_range.mp (mem_filter.mp hM).1
      exact connectionCoefficient_eq_zero_of_lt (by omega)
  · rw [connectionCoefficient_eq_zero_of_not_modEq _ _ hpar, mul_zero]
    apply le_of_eq
    apply sum_eq_zero
    intro M hM
    exact connectionCoefficient_eq_zero_of_not_modEq _ _
      (fun hMl => hpar ((mem_filter.mp hM).2.symm.trans hMl))

/-- The sum of earlier rows of matching parity has a harmonic upper bound. -/
theorem sum_positiveMilinRow_sameParity_le {ρ : ℕ → ℝ} (hρ : ∀ l, 0 ≤ ρ l) (N : ℕ) :
    (∑ M ∈ (range (N + 1)).filter (fun M : ℕ => (M : ℤ) ≡ (N : ℤ) [ZMOD 2]),
      positiveMilinRow ρ M) ≤
      ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) * positiveMilinRow ρ N := by
  rw [show (∑ M ∈ (range (N + 1)).filter (fun M : ℕ => (M : ℤ) ≡ (N : ℤ) [ZMOD 2]),
      positiveMilinRow ρ M) =
      ∑ M ∈ (range (N + 1)).filter (fun M : ℕ => (M : ℤ) ≡ (N : ℤ) [ZMOD 2]),
        ∑ l ∈ range (N + 1), connectionCoefficient M l * ρ l by
    exact sum_congr rfl (fun M hM => positiveMilinRow_eq_sum_range ρ
      (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hM).1)))]
  rw [sum_comm, positiveMilinRow, mul_sum]
  exact sum_le_sum fun l _ => by
    rw [← sum_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (sum_connectionCoefficient_sameParity_le N l) (hρ l)

private theorem connectionCoefficient_target_le {n j l : ℕ} (hn : 1 ≤ n)
    (hjlo : 3 * n ≤ j) (hjhi : j ≤ 4 * n)
    (hpar : (↑(2 * n - 2 : ℕ) : ℤ) ≡ (↑(j - 1 : ℕ) : ℤ) [ZMOD 2]) :
    connectionCoefficient (2 * n - 2) l ≤
      (8 * Real.sqrt (n : ℝ)) * connectionCoefficient (j - 1) l := by
  have hnonneg := connectionCoefficient_nonneg (j - 1) l
  by_cases hl : l ≤ 2 * n - 2
  · by_cases hlt : (↑(2 * n - 2 : ℕ) : ℤ) ≡ (l : ℤ) [ZMOD 2]
    · have hlj : l ≤ j - 1 := by omega
      have hlow := (connectionCoefficient_bounds hlj (hpar.symm.trans hlt)).1
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hjhi' : (j : ℝ) ≤ 4 * n := by exact_mod_cast hjhi
      have hN : (↑(2 * n - 2 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      have hJ : (↑(j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [hJ] at hlow
      have hJpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
      have hmul := (div_le_iff₀ hJpos).mp hlow
      have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := by simpa using Real.sqrt_le_sqrt hn'
      by_cases hsmall : l < n
      · have hsmall' : (l : ℝ) + 1 ≤ n := by exact_mod_cast (show l + 1 ≤ n by omega)
        have hupp := (connectionCoefficient_bounds hl hlt).2
        rw [hN] at hupp
        have hden : (n : ℝ) ≤ 2 * n - 1 - l := by linarith
        have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn'
        have hprod := mul_nonneg (sub_nonneg.mpr hjhi') hnonneg
        have hupper : connectionCoefficient (2 * n - 2) l ≤ 4 * connectionCoefficient (j - 1) l := by
          calc
            _ ≤ (2 * (l : ℝ) + 1) / (2 * n - 1 - l) := hupp
            _ ≤ (2 * (l : ℝ) + 1) / n := by gcongr
            _ ≤ _ := (div_le_iff₀ hnpos).mpr (by nlinarith only [hmul, hprod])
        exact hupper.trans (mul_le_mul_of_nonneg_right (by linarith) hnonneg)
      · have hl' : (n : ℝ) ≤ l := by exact_mod_cast (show n ≤ l by omega)
        have hbase : 1 / 2 ≤ connectionCoefficient (j - 1) l := by
          refine le_trans ?_ hlow
          apply (le_div_iff₀ hJpos).mpr
          linarith
        have hle : (l : ℝ) + 1 ≤ 2 * n := by exact_mod_cast (show l + 1 ≤ 2 * n by omega)
        have hsqrt' : Real.sqrt ((l : ℝ) + 1) ≤ 2 * Real.sqrt (n : ℝ) := calc
          _ ≤ Real.sqrt (2 * (n : ℝ)) := Real.sqrt_le_sqrt hle
          _ = Real.sqrt 2 * Real.sqrt (n : ℝ) := Real.sqrt_mul (by norm_num) _
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            rw [Real.sqrt_le_iff]
            norm_num
        calc
          _ ≤ 2 * Real.sqrt ((l : ℝ) + 1) := connectionCoefficient_le_two_sqrt _ _
          _ ≤ 4 * Real.sqrt (n : ℝ) := by linarith
          _ ≤ _ := by nlinarith only [mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (sub_nonneg.mpr hbase)]
    · rw [connectionCoefficient_eq_zero_of_not_modEq _ _ hlt]
      positivity
  · rw [connectionCoefficient_eq_zero_of_lt (by omega : 2 * n - 2 < l)]
    positivity

/-- The target Milin row is bounded by a square-root factor times a later odd-indexed sum. -/
theorem positiveMilinRow_target_le {ρ : ℕ → ℝ} (hρ : ∀ l, 0 ≤ ρ l) {n j : ℕ}
    (hn : 1 ≤ n) (hjlo : 3 * n ≤ j) (hjhi : j ≤ 4 * n) (hj : Odd j) :
    positiveMilinRow ρ (2 * n - 2) ≤ (8 * Real.sqrt (n : ℝ)) * positiveMilinRow ρ (j - 1) := by
  have hpar : (↑(2 * n - 2 : ℕ) : ℤ) ≡ (↑(j - 1 : ℕ) : ℤ) [ZMOD 2] := by
    obtain ⟨k, hk⟩ := hj
    unfold Int.ModEq
    omega
  rw [positiveMilinRow_eq_sum_range ρ (show 2 * n - 2 ≤ j - 1 by omega), positiveMilinRow,
    mul_sum]
  apply sum_le_sum
  intro l _
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (connectionCoefficient_target_le hn hjlo hjhi hpar) (hρ l)

end Zalcman
