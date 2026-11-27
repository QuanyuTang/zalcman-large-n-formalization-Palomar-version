/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Choosing small coefficient deficits from the mass bound

Each of the three intervals used in coefficient transfer contains a positive proportion of
odd indices. Averaging supplies an index with small deficit in each interval.
-/

public section

namespace Zalcman

open Finset

private theorem exists_small_deficit_on_odd_progression (δ : ℕ → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    {n a : ℕ} {M : ℝ} (hn : 32 ≤ n) (hM : 0 ≤ M)
    (ha : ∀ k < n / 16, 2 * (a + k) + 1 ≤ 4 * n)
    (hmass : (∑ i ∈ (range (4 * n + 1)).filter Odd, δ i) ≤ (n : ℝ) * M) :
    ∃ k < n / 16, δ (2 * (a + k) + 1) ≤ 32 * M := by
  let f (k : ℕ) : ℕ := 2 * (a + k) + 1
  have hf : Function.Injective f := by intro i j hij; dsimp [f] at hij; omega
  have hsub : (range (n / 16)).image f ⊆ (range (4 * n + 1)).filter Odd := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hi
    exact mem_filter.mpr ⟨mem_range.mpr (by have := ha k (mem_range.mp hk); dsimp [f]; omega),
      ⟨a + k, rfl⟩⟩
  have hsum := sum_le_sum_of_subset_of_nonneg (f := δ) hsub fun i _ _ => hδ i
  rw [sum_image hf.injOn] at hsum
  have hcount : (n : ℝ) ≤ 32 * ((n / 16 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 32 * (n / 16) by omega)
  have hconst : (∑ _i ∈ range (n / 16), 32 * M) = ((n / 16 : ℕ) : ℝ) * (32 * M) := by
    simp [nsmul_eq_mul]
  have hcompare : (∑ i ∈ range (n / 16), δ (f i)) ≤ ∑ _i ∈ range (n / 16), 32 * M := calc
    _ ≤ (n : ℝ) * M := hsum.trans hmass
    _ ≤ (32 * ((n / 16 : ℕ) : ℝ)) * M := mul_le_mul_of_nonneg_right hcount hM
    _ = _ := by rw [hconst]; ring
  obtain ⟨k, hk, hk'⟩ := exists_le_of_sum_le (s := range (n / 16))
    (nonempty_range_iff.mpr (by omega)) hcompare
  exact ⟨k, mem_range.mp hk, hk'⟩

/-- An upper bound on the total odd deficit supplies three well-separated odd indices. -/
theorem exists_small_odd_deficits (δ : ℕ → ℝ) (hδ : ∀ i, 0 ≤ δ i) {n : ℕ} {M : ℝ}
    (hn : 32 ≤ n) (hM : 0 ≤ M)
    (hmass : (∑ i ∈ (range (4 * n + 1)).filter Odd, δ i) ≤ (n : ℝ) * M) :
    ∃ j₁ j₂ j₃ : ℕ,
      Odd j₁ ∧ Odd j₂ ∧ Odd j₃ ∧
      3 * n ≤ 2 * j₁ ∧ 4 * j₁ ≤ 7 * n ∧ 2 * n ≤ j₂ ∧ 4 * j₂ ≤ 9 * n ∧
      3 * n ≤ j₃ ∧ j₃ ≤ 4 * n ∧ δ j₁ ≤ 32 * M ∧ δ j₂ ≤ 32 * M ∧ δ j₃ ≤ 32 * M := by
  let a₁ := (3 * n + 2) / 4
  let a₂ := n
  let a₃ := (3 * n) / 2
  obtain ⟨k₁, hk₁, h₁⟩ := exists_small_deficit_on_odd_progression δ hδ hn hM
    (a := a₁) (by intro k hk; dsimp [a₁]; omega) hmass
  obtain ⟨k₂, hk₂, h₂⟩ := exists_small_deficit_on_odd_progression δ hδ hn hM
    (a := a₂) (by intro k hk; dsimp [a₂]; omega) hmass
  obtain ⟨k₃, hk₃, h₃⟩ := exists_small_deficit_on_odd_progression δ hδ hn hM
    (a := a₃) (by intro k hk; dsimp [a₃]; omega) hmass
  refine ⟨2 * (a₁ + k₁) + 1, 2 * (a₂ + k₂) + 1, 2 * (a₃ + k₃) + 1,
    ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, h₁, h₂, h₃⟩ <;>
    dsimp [a₁, a₂, a₃] <;> omega

end Zalcman
