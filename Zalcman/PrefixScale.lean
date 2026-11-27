/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.LogPrefixRecurrence
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Choosing the initial logarithmic window

The window of natural length `sqrt n` satisfies the finite index bounds.
The domination of the logarithm by the fourth root gives a uniform threshold
for the small-exponent argument.
-/

public section

namespace Zalcman

open Filter

/-- The natural square-root window has the required size and lies in the initial block. -/
theorem prefix_sqrt_bounds {n : ℕ} (hn : 4 ≤ n) :
    0 < n.sqrt ∧ 2 * n.sqrt ≤ n ∧ n.sqrt ^ 2 ≤ n ∧
      Real.sqrt (n : ℝ) / 2 ≤ (n.sqrt : ℝ) := by
  have hJ : 2 ≤ n.sqrt := Nat.le_sqrt.mpr (by simpa using hn)
  have hJ₂ : n.sqrt ^ 2 ≤ n := Nat.sqrt_le' n
  have hTwo : 2 * n.sqrt ≤ n.sqrt ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right n.sqrt hJ
  have hJr : (2 : ℝ) ≤ n.sqrt := by exact_mod_cast hJ
  have hroot : Real.sqrt (n : ℝ) < (n.sqrt : ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  exact ⟨by omega, hTwo.trans hJ₂, hJ₂, by linarith only [hroot, hJr]⟩

/-- The small-exponent estimate holds uniformly for deficits bounded by three. -/
theorem exists_prefix_smallExponent_threshold {A : ℝ} (hA : 0 < A) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ D : ℝ, 0 ≤ D → D ≤ 3 →
      Real.sqrt (A * D / (n.sqrt : ℝ)) * (1 + Real.log (n : ℝ)) ≤ 1 := by
  let C := 2 * Real.sqrt (6 * A)
  have hC : 0 < C := by dsimp [C]; positivity
  have hLog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hSm := (isLittleO_log_rpow_atTop (r := (1 / 4 : ℝ)) (by norm_num)).def
    (show 0 < 1 / C by positivity)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hLog.and hSm)
  obtain ⟨L, hL⟩ := exists_nat_ge x₀
  refine ⟨max 4 L, le_max_left _ _, fun n hn D hD₀ hD ↦ ?_⟩
  have hFour : 4 ≤ n := by omega
  obtain ⟨hJ, _, _, hJlo⟩ := prefix_sqrt_bounds hFour
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hJpos : (0 : ℝ) < n.sqrt := by exact_mod_cast hJ
  have hx := hx₀ (n : ℝ) (hL.trans (by exact_mod_cast (show L ≤ n by omega)))
  have hlog₀ : 0 ≤ Real.log (n : ℝ) := zero_le_one.trans hx.1
  have hsm := hx.2
  rw [Real.norm_of_nonneg hlog₀, Real.norm_of_nonneg (Real.rpow_nonneg hnR.le _),
    div_mul_eq_mul_div, le_div_iff₀ hC] at hsm
  simp only [one_mul] at hsm
  have hroot : Real.sqrt (Real.sqrt (n : ℝ)) = (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hnR.le]
    congr 1
    norm_num
  have hε : Real.sqrt (A * D / (n.sqrt : ℝ)) ≤
      Real.sqrt (6 * A) / (n : ℝ) ^ (1 / 4 : ℝ) := calc
    _ ≤ Real.sqrt ((3 * A) / (Real.sqrt (n : ℝ) / 2)) := by
      apply Real.sqrt_le_sqrt
      have hAD : A * D ≤ 3 * A := by
        simpa only [mul_comm A 3] using mul_le_mul_of_nonneg_left hD hA.le
      have hsqrt : 0 < Real.sqrt (n : ℝ) / 2 := by positivity
      exact (div_le_div_of_nonneg_right hAD hJpos.le).trans
        (div_le_div_of_nonneg_left (by positivity) hsqrt hJlo)
    _ = Real.sqrt ((6 * A) / Real.sqrt (n : ℝ)) := by congr 1; ring
    _ = _ := by rw [Real.sqrt_div (show 0 ≤ 6 * A by positivity), hroot]
  have hnroot : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hnR _
  calc
    _ ≤ (Real.sqrt (6 * A) / (n : ℝ) ^ (1 / 4 : ℝ)) * (2 * Real.log (n : ℝ)) :=
      mul_le_mul hε (by linarith only [hx.1]) (by positivity) (by positivity)
    _ = Real.log (n : ℝ) * C / (n : ℝ) ^ (1 / 4 : ℝ) := by dsimp [C]; ring
    _ ≤ _ := (div_le_one hnroot).mpr hsm

end Zalcman
