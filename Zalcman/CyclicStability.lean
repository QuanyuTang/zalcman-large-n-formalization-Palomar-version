/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concentration on a single cyclic Fourier mode

If every cyclic autocorrelation is close in modulus to the norm squared,
one Fourier mode has almost all of the mass.
-/

public section

namespace Zalcman

open Finset
open scoped ComplexConjugate

variable {N : ℕ} [NeZero N]

private theorem stdAddChar_conj (j : ZMod N) :
    ZMod.stdAddChar (-j) = conj (ZMod.stdAddChar j) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
    AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

private theorem stdAddChar_norm (j : ZMod N) : ‖ZMod.stdAddChar j‖ = 1 := by
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

private theorem conj_dft_eq_sum (b : ZMod N → ℂ) (k : ZMod N) :
    conj (ZMod.dft b k) = ∑ j : ZMod N, ZMod.stdAddChar (j * k) * conj (b j) := by
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul, stdAddChar_conj, Complex.conj_conj]

private theorem dft_inversion_mul (b : ZMod N → ℂ) (j : ZMod N) :
    (N : ℂ) * b j = ∑ k : ZMod N, ZMod.stdAddChar (k * j) * ZMod.dft b k := by
  have h := congrFun (ZMod.dft_dft b) (-j)
  rw [ZMod.dft_apply] at h
  simpa only [mul_neg, neg_neg, smul_eq_mul] using h.symm

/-- Parseval's identity in the unnormalized transform convention. -/
theorem sum_dft_norm_sq (b : ZMod N → ℂ) :
    (∑ k : ZMod N, ‖ZMod.dft b k‖ ^ 2) = (N : ℝ) * ∑ j : ZMod N, ‖b j‖ ^ 2 := by
  have h : (N : ℂ) * (∑ j : ZMod N, b j * conj (b j)) =
      ∑ k : ZMod N, ZMod.dft b k * conj (ZMod.dft b k) := calc
    _ = ∑ j : ZMod N, (∑ k : ZMod N, ZMod.stdAddChar (k * j) * ZMod.dft b k) * conj (b j) := by
      rw [mul_sum]
      exact sum_congr rfl (fun j _ => by rw [← mul_assoc, dft_inversion_mul])
    _ = ∑ k : ZMod N, ZMod.dft b k * (∑ j : ZMod N, ZMod.stdAddChar (j * k) * conj (b j)) := by
      simp only [sum_mul, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl (fun k _ => sum_congr rfl (fun j _ => by rw [mul_comm k j]; ring))
    _ = _ := by simp only [← conj_dft_eq_sum]
  have hre := congrArg Complex.re h.symm
  simp only [Complex.re_sum, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_natCast, Complex.re_ofReal_mul] at hre
  exact hre

/-- The unnormalized cyclic autocorrelation. -/
@[expose] noncomputable def cyclicCorrelation (b : ZMod N → ℂ) (h : ZMod N) : ℂ :=
  ∑ j : ZMod N, b (j + h) * conj (b j)

private theorem sum_char_translate (b : ZMod N → ℂ) (j k : ZMod N) :
    (∑ h : ZMod N, ZMod.stdAddChar (-(h * k)) * b (j + h)) =
      ZMod.stdAddChar (j * k) * ZMod.dft b k := by
  rw [ZMod.dft_apply, mul_sum]
  simp only [smul_eq_mul]
  apply Fintype.sum_equiv (Equiv.addLeft j)
  intro h
  change ZMod.stdAddChar (-(h * k)) * b (j + h) =
    ZMod.stdAddChar (j * k) * (ZMod.stdAddChar (-((j + h) * k)) * b (j + h))
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- The finite transform of a cyclic autocorrelation is the squared transform modulus. -/
theorem dft_cyclicCorrelation (b : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (cyclicCorrelation b) k = ZMod.dft b k * conj (ZMod.dft b k) := calc
  _ = ∑ h : ZMod N, ∑ j : ZMod N,
      (ZMod.stdAddChar (-(h * k)) * b (j + h)) * conj (b j) := by
    simp only [ZMod.dft_apply, smul_eq_mul, cyclicCorrelation, mul_sum, mul_assoc]
  _ = ∑ j : ZMod N, (∑ h : ZMod N, ZMod.stdAddChar (-(h * k)) * b (j + h)) * conj (b j) := by
    rw [sum_comm]
    simp only [sum_mul]
  _ = _ := by
    simp only [sum_char_translate, mul_comm (ZMod.stdAddChar _) (ZMod.dft _ _)]
    simp only [mul_assoc, ← mul_sum, conj_dft_eq_sum]

private theorem sum_mode_error (b : ZMod N → ℂ) (k : ZMod N) {β : ℂ} :
    (∑ j : ZMod N, ‖b j - β * ZMod.stdAddChar (j * k)‖ ^ 2) =
      (∑ j : ZMod N, ‖b j‖ ^ 2) + (N : ℝ) * ‖β‖ ^ 2 -
        2 * (conj β * ZMod.dft b k).re := by
  have hterm (j : ZMod N) :
      ‖b j - β * ZMod.stdAddChar (j * k)‖ ^ 2 = ‖b j‖ ^ 2 + ‖β‖ ^ 2 -
        2 * (conj β * (ZMod.stdAddChar (-(j * k)) * b j)).re := by
    have hcross : b j * conj (β * ZMod.stdAddChar (j * k)) =
        conj β * (ZMod.stdAddChar (-(j * k)) * b j) := by
      rw [map_mul, stdAddChar_conj]
      ring
    rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      norm_mul, stdAddChar_norm, mul_one, hcross]
  simp only [hterm, sum_sub_distrib, sum_add_distrib, ← mul_sum, ← Complex.re_sum, ZMod.dft_apply,
    smul_eq_mul, sum_const, card_univ, ZMod.card, nsmul_eq_mul]

private theorem sum_mode_error_projection (b : ZMod N → ℂ) (k : ZMod N) :
    (∑ j : ZMod N, ‖b j - (ZMod.dft b k / (N : ℂ)) * ZMod.stdAddChar (j * k)‖ ^ 2) =
      (∑ j : ZMod N, ‖b j‖ ^ 2) - ‖ZMod.dft b k‖ ^ 2 / (N : ℝ) := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [sum_mode_error, norm_div, Complex.norm_natCast, map_div₀, Complex.conj_natCast]
  rw [show conj (ZMod.dft b k) / (N : ℂ) * ZMod.dft b k =
      ZMod.dft b k * conj (ZMod.dft b k) / (N : ℂ) by ring,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_natCast, Complex.div_ofReal_re,
    Complex.ofReal_re]
  field_simp
  ring

/-- A uniform lower bound for the autocorrelations gives a mode with small squared residual. -/
theorem exists_mode_error_le (b : ZMod N → ℂ) {E : ℝ} (hE : 0 ≤ E)
    (h : ∀ t : ZMod N, (∑ j : ZMod N, ‖b j‖ ^ 2) - E ≤ ‖cyclicCorrelation b t‖) :
    ∃ (k : ZMod N) (β : ℂ),
      (∑ j : ZMod N, ‖b j - β * ZMod.stdAddChar (j * k)‖ ^ 2) ≤ 2 * E := by
  let B : ℝ := ∑ j : ZMod N, ‖b j‖ ^ 2
  have hB : 0 ≤ B := sum_nonneg fun _ _ => sq_nonneg _
  have hN : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  by_cases hBz : B = 0
  · exact ⟨0, 0, by simp only [zero_mul, sub_zero]; dsimp [B] at hBz; rw [hBz]; positivity⟩
  obtain ⟨k, _, hk⟩ := exists_max_image (univ : Finset (ZMod N))
    (fun k => ‖ZMod.dft b k‖ ^ 2) ⟨0, mem_univ _⟩
  let p := ‖ZMod.dft b k‖ ^ 2
  have hCorr : (N : ℝ) * (B ^ 2 - 2 * B * E) ≤ ∑ t : ZMod N, ‖cyclicCorrelation b t‖ ^ 2 := calc
    _ = ∑ _t : ZMod N, (B ^ 2 - 2 * B * E) := by
      simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    _ ≤ _ := by
      apply sum_le_sum
      intro t _
      have ht := mul_le_mul_of_nonneg_left (h t) (show 0 ≤ 2 * B by positivity)
      change 2 * B * (B - E) ≤ 2 * B * ‖cyclicCorrelation b t‖ at ht
      nlinarith only [ht, sq_nonneg (‖cyclicCorrelation b t‖ - B)]
  have hParseval := sum_dft_norm_sq (cyclicCorrelation b)
  simp only [dft_cyclicCorrelation, norm_mul, Complex.norm_conj, ← pow_two] at hParseval
  have hP : (∑ j : ZMod N, (‖ZMod.dft b j‖ ^ 2) ^ 2) ≤ p * ((N : ℝ) * B) := calc
    _ ≤ ∑ j : ZMod N, p * ‖ZMod.dft b j‖ ^ 2 := by
      apply sum_le_sum
      intro j _
      rw [pow_two (‖ZMod.dft b j‖ ^ 2)]
      exact mul_le_mul_of_nonneg_right (hk j (mem_univ _)) (sq_nonneg _)
    _ = _ := by rw [← mul_sum, sum_dft_norm_sq]
  rw [hParseval] at hP
  have hNB : 0 < (N : ℝ) * B := mul_pos hN (lt_of_le_of_ne hB (Ne.symm (show B ≠ 0 from hBz)))
  have hProd := (mul_le_mul_of_nonneg_left hCorr hN.le).trans hP
  have hLo : (N : ℝ) * (B - 2 * E) ≤ p := by
    apply (mul_le_mul_iff_of_pos_right hNB).mp
    nlinarith only [hProd]
  refine ⟨k, ZMod.dft b k / (N : ℂ), ?_⟩
  rw [sum_mode_error_projection]
  have hh : B - 2 * E ≤ p / (N : ℝ) := (le_div_iff₀ hN).mpr (by
    rw [mul_comm]
    exact hLo)
  change B - p / (N : ℝ) ≤ 2 * E
  linarith

end Zalcman
