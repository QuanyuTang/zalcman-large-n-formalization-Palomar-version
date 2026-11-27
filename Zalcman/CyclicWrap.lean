/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

namespace Zalcman

open Finset
open scoped ComplexConjugate

/-- Compensating for the half-block phase makes the initial block periodic. -/
@[expose] def cyclicPrefix {H : ℕ} (c : ℕ → ℂ) (τ : ℂ) (j : ZMod H) : ℂ := conj τ ^ j.val * c j.val

private theorem conj_unit_mul {v : ℂ} (hv : ‖v‖ = 1) : conj v * v = 1 := by
  rw [Complex.conj_mul', hv]
  norm_num

private theorem norm_sq_sub_bound (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  nlinarith only [hh, sq_nonneg (‖a‖ - ‖b‖)]

/-- The shift error after wraparound is controlled by the original two shift errors. -/
theorem cyclicPrefix_shift_le {H : ℕ} [NeZero H] (c : ℕ → ℂ) {τ v vH : ℂ}
    (hτ : ‖τ‖ = 1) (hτH : τ ^ H = vH) (h : ZMod H) {j : ℕ} (hj : j < H) :
    ‖cyclicPrefix c τ ((j : ZMod H) + h) - (conj τ ^ h.val * v) * cyclicPrefix c τ (j : ZMod H)‖ ^ 2 ≤
      2 * (‖c (j + h.val) - v * c j‖ ^ 2 + if H ≤ j + h.val then
        ‖c (j + h.val) - vH * c (j + h.val - H)‖ ^ 2 else 0) := by
  have hj' : (j : ZMod H).val = j := ZMod.val_natCast_of_lt hj
  have hnorm (p : ℕ) : ‖conj τ ^ p‖ = 1 := by simp [norm_pow, hτ]
  by_cases hw : H ≤ j + h.val
  · have hval : ((j : ZMod H) + h).val = j + h.val - H := by
      rw [ZMod.val_add_of_le (by rw [hj']; exact hw), hj']
    have hf : conj τ ^ (j + h.val) * vH = conj τ ^ (j + h.val - H) := calc
      _ = (conj τ ^ (j + h.val - H) * conj τ ^ H) * vH := by rw [← pow_add, Nat.sub_add_cancel hw]
      _ = _ := by rw [mul_assoc, ← hτH, ← mul_pow, conj_unit_mul hτ, one_pow, mul_one]
    have hb : cyclicPrefix c τ ((j : ZMod H) + h) - (conj τ ^ h.val * v) * cyclicPrefix c τ (j : ZMod H) =
        conj τ ^ (j + h.val) * ((c (j + h.val) - v * c j) - (c (j + h.val) - vH * c (j + h.val - H))) := by
      simp only [cyclicPrefix, hval, hj', ← hf, pow_add]
      ring
    rw [hb, norm_mul, hnorm, one_mul, ite_eq_left hw]
    exact norm_sq_sub_bound _ _
  · have hval : ((j : ZMod H) + h).val = j + h.val := by
      rw [ZMod.val_add_of_lt (by rw [hj']; omega), hj']
    have hb : cyclicPrefix c τ ((j : ZMod H) + h) - (conj τ ^ h.val * v) * cyclicPrefix c τ (j : ZMod H) =
        conj τ ^ (j + h.val) * (c (j + h.val) - v * c j) := by
      simp only [cyclicPrefix, hval, hj', pow_add]
      ring
    rw [hb, norm_mul, hnorm, one_mul, ite_eq_right hw, add_zero]
    exact le_mul_of_one_le_left (sq_nonneg _) (by norm_num)

private def valEquivFin (m : ℕ) [NeZero m] : ZMod m ≃ Fin m where
  toFun j := ⟨j.val, ZMod.val_lt _⟩
  invFun j := (j.val : ZMod m)
  left_inv j := ZMod.natCast_zmod_val j
  right_inv j := Fin.ext (ZMod.val_natCast_of_lt j.isLt)

/-- A sum over residue classes is the sum over their natural representatives. -/
theorem sum_zmod_eq_sum_range {m : ℕ} [NeZero m] {R : Type*} [AddCommMonoid R]
    (f : ZMod m → R) : ∑ j, f j = ∑ i ∈ range m, f (i : ZMod m) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (valEquivFin m) _ _ (fun j => congrArg f (ZMod.natCast_zmod_val j).symm)

/-- Summing cyclic shift errors only costs the original shift and one half-block shift. -/
theorem sum_cyclicPrefix_shift_le {H n : ℕ} [NeZero H] (c : ℕ → ℂ) (hHn : 2 * H ≤ n)
    {τ v vH : ℂ} (hτ : ‖τ‖ = 1) (hτH : τ ^ H = vH) (h : ZMod H) {E : ℝ}
    (he : (∑ j ∈ range (n - h.val), ‖c (j + h.val) - v * c j‖ ^ 2) ≤ E)
    (heH : (∑ j ∈ range (n - H), ‖c (j + H) - vH * c j‖ ^ 2) ≤ E) :
    (∑ j : ZMod H, ‖cyclicPrefix c τ (j + h) - (conj τ ^ h.val * v) * cyclicPrefix c τ j‖ ^ 2) ≤ 4 * E := by
  let l := h.val
  have hl : l < H := ZMod.val_lt h
  let R (j : ℕ) : ℝ := ‖c (j + l) - v * c j‖ ^ 2
  let RH (j : ℕ) : ℝ := ‖c (j + H) - vH * c j‖ ^ 2
  have hBase : (∑ j ∈ range H, R j) ≤ E :=
    (sum_le_sum_of_subset_of_nonneg (range_mono (by omega : H ≤ n - l)) (fun _ _ _ => sq_nonneg _)).trans he
  have hWrap : (∑ j ∈ range H, if H ≤ j + l then RH (j + l - H) else 0) ≤ E := by
    rw [← sum_filter]
    let s := (range H).filter (fun j => H ≤ j + l)
    have hsub : s.image (fun j => j + l - H) ⊆ range (n - H) := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      have hj' := mem_range.mp (mem_filter.mp hj).1
      exact mem_range.mpr (by omega)
    have hinj : Set.InjOn (fun j => j + l - H) (↑s : Set ℕ) := by
      intro i hi j hj hh
      have h₁ := (mem_filter.mp (mem_coe.mp hi)).2
      have h₂ := (mem_filter.mp (mem_coe.mp hj)).2
      change i + l - H = j + l - H at hh
      omega
    have hh := (sum_le_sum_of_subset_of_nonneg (f := RH) hsub (fun _ _ _ => sq_nonneg _)).trans heH
    rwa [sum_image hinj] at hh
  rw [sum_zmod_eq_sum_range]
  have hpoint (j : ℕ) (hj : j ∈ range H) :
      ‖cyclicPrefix c τ ((j : ZMod H) + h) - (conj τ ^ h.val * v) * cyclicPrefix c τ (j : ZMod H)‖ ^ 2 ≤
        2 * (R j + if H ≤ j + l then RH (j + l - H) else 0) := by
    by_cases hw : H ≤ j + h.val
    · simpa only [R, RH, l, ite_eq_left hw, Nat.sub_add_cancel hw] using
        cyclicPrefix_shift_le c hτ hτH h (mem_range.mp hj)
    · simpa only [R, l, ite_eq_right hw] using
        cyclicPrefix_shift_le c hτ hτH h (mem_range.mp hj)
  have hh := sum_le_sum (s := range H) hpoint
  simp only [← mul_sum, sum_add_distrib] at hh
  linarith only [hh, hBase, hWrap]

end Zalcman
