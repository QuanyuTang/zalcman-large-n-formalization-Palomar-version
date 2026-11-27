/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite estimates for the Chebyshev–Legendre connection formula

The kernel average is the finite expression supplied by the Fourier expansion and
Legendre orthogonality. Its bounds use positivity and normalization of the weights.
The diagonal estimate uses the recurrence for central binomial coefficients.
-/

@[expose] public section

noncomputable section

namespace Zalcman

open Finset
open scoped BigOperators

private lemma connectionDen_pos {a v : ℝ} (h : |v| < a) : 0 < a ^ 2 - v ^ 2 := by
  have hs := pow_lt_pow_left₀ h (abs_nonneg v) (by decide : (2 : ℕ) ≠ 0)
  rw [sq_abs] at hs
  exact sub_pos.mpr hs

private lemma connectionKernel_bounds {a v L : ℝ} (hv : |v| ≤ L) (hL : L < a) :
    1 / a ≤ a / (a ^ 2 - v ^ 2) ∧ a / (a ^ 2 - v ^ 2) ≤ 1 / (a - L) := by
  have hL₀ : 0 ≤ L := (abs_nonneg v).trans hv
  have ha : 0 < a := hL₀.trans_lt hL
  have hd := connectionDen_pos (hv.trans_lt hL)
  constructor
  · apply (div_le_div_iff₀ ha hd).2
    nlinarith only [sq_nonneg v]
  · apply (div_le_div_iff₀ hd (sub_pos.mpr hL)).2
    have hs := pow_le_pow_left₀ (abs_nonneg v) hv 2
    rw [sq_abs] at hs
    nlinarith only [hs, mul_le_mul_of_nonneg_right hL.le hL₀]

private lemma connectionKernel_antitone {a b v : ℝ} (ha : |v| < a) (hab : a ≤ b) :
    b / (b ^ 2 - v ^ 2) ≤ a / (a ^ 2 - v ^ 2) := by
  have ha' : 0 < a := (abs_nonneg v).trans_lt ha
  have hb' : 0 < b := ha'.trans_le hab
  apply (div_le_div_iff₀ (connectionDen_pos (ha.trans_le hab)) (connectionDen_pos ha)).2
  have hsum : 0 ≤ a * b + v ^ 2 := by positivity
  nlinarith only [mul_nonneg (sub_nonneg.mpr hab) hsum]

/-- The probability-weighted expression for a connection coefficient of admissible parity. -/
def connectionAverage (s : Finset ℤ) (p : ℤ → ℝ) (M ℓ : ℕ) : ℝ :=
  (2 * (ℓ : ℝ) + 1) * ∑ v ∈ s, p v * (((M : ℝ) + 1) / (((M : ℝ) + 1) ^ 2 - (v : ℝ) ^ 2))

/-- The elementary lower and upper bounds for the connection average. -/
theorem connectionAverage_bounds (s : Finset ℤ) (p : ℤ → ℝ) {M ℓ : ℕ} (hℓM : ℓ ≤ M)
    (hp : ∀ v ∈ s, 0 ≤ p v) (hp_sum : ∑ v ∈ s, p v = 1)
    (hs : ∀ v ∈ s, |(v : ℝ)| ≤ (ℓ : ℝ)) :
    (2 * (ℓ : ℝ) + 1) / ((M : ℝ) + 1) ≤ connectionAverage s p M ℓ ∧
      connectionAverage s p M ℓ ≤ (2 * (ℓ : ℝ) + 1) / ((M : ℝ) + 1 - ℓ) := by
  let a : ℝ := (M : ℝ) + 1
  have hℓa : (ℓ : ℝ) < a := by
    dsimp only [a]
    exact_mod_cast Nat.lt_succ_of_le hℓM
  have hlow : 1 / a ≤ ∑ v ∈ s, p v * (a / (a ^ 2 - (v : ℝ) ^ 2)) := calc
    _ = ∑ v ∈ s, p v * (1 / a) := by rw [← sum_mul, hp_sum, one_mul]
    _ ≤ _ := sum_le_sum fun v hv ↦
      mul_le_mul_of_nonneg_left (connectionKernel_bounds (hs v hv) hℓa).1 (hp v hv)
  have hupp : ∑ v ∈ s, p v * (a / (a ^ 2 - (v : ℝ) ^ 2)) ≤ 1 / (a - (ℓ : ℝ)) := calc
    _ ≤ ∑ v ∈ s, p v * (1 / (a - (ℓ : ℝ))) := sum_le_sum fun v hv ↦
      mul_le_mul_of_nonneg_left (connectionKernel_bounds (hs v hv) hℓa).2 (hp v hv)
    _ = _ := by rw [← sum_mul, hp_sum, one_mul]
  have hfactor : 0 ≤ 2 * (ℓ : ℝ) + 1 := by positivity
  exact ⟨by simpa only [connectionAverage, a, div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hlow hfactor,
    by simpa only [connectionAverage, a, div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hupp hfactor⟩

/-- The connection average decreases with its first degree, with the weights fixed. -/
theorem connectionAverage_antitone (s : Finset ℤ) (p : ℤ → ℝ) {ℓ M N : ℕ}
    (hℓM : ℓ ≤ M) (hMN : M ≤ N) (hp : ∀ v ∈ s, 0 ≤ p v)
    (hs : ∀ v ∈ s, |(v : ℝ)| ≤ (ℓ : ℝ)) :
    connectionAverage s p N ℓ ≤ connectionAverage s p M ℓ := by
  have hℓM' : (ℓ : ℝ) < (M : ℝ) + 1 := by exact_mod_cast Nat.lt_succ_of_le hℓM
  have hMN' : (M : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hMN
  unfold connectionAverage
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine sum_le_sum fun v hv ↦ ?_
  exact mul_le_mul_of_nonneg_left
    (connectionKernel_antitone ((hs v hv).trans_lt hℓM') hMN') (hp v hv)

private def centralBinomialRatio (n : ℕ) : ℝ :=
  (4 : ℝ) ^ n / (n.centralBinom : ℝ)

private lemma centralBinomialRatio_succ (n : ℕ) :
    centralBinomialRatio (n + 1) =
      ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1)) * centralBinomialRatio n := by
  have ha : (n.centralBinom : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.centralBinom_ne_zero n)
  have hb : (Nat.centralBinom (n + 1) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.centralBinom_ne_zero (n + 1))
  have hd : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  have hrec : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * (n : ℝ) + 1) * (n.centralBinom : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  simp only [centralBinomialRatio, pow_succ]
  field_simp [ha, hb, hd]
  linear_combination -2 * hrec

private lemma centralBinomialRatio_sq_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    centralBinomialRatio ℓ ^ 2 ≤ 4 * (ℓ : ℝ) := by
  induction ℓ, hℓ using Nat.le_induction with
  | base => norm_num [centralBinomialRatio, Nat.centralBinom, Nat.choose_one_right]
  | succ n hn ih =>
    rw [centralBinomialRatio_succ, mul_pow, Nat.cast_succ]
    refine (mul_le_mul_of_nonneg_left ih (sq_nonneg _)).trans ?_
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith only [show 0 ≤ (n : ℝ) + 1 by positivity]

/-- The diagonal ratio is at most twice the square root of its positive degree. -/
theorem four_pow_div_choose_le_two_sqrt {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (4 : ℝ) ^ ℓ / ((2 * ℓ).choose ℓ : ℝ) ≤ 2 * Real.sqrt ℓ := by
  change centralBinomialRatio ℓ ≤ 2 * Real.sqrt (ℓ : ℝ)
  have hq : 0 ≤ centralBinomialRatio ℓ := by unfold centralBinomialRatio; positivity
  have hr : 0 ≤ 2 * Real.sqrt (ℓ : ℝ) := by positivity
  apply (pow_le_pow_iff_left₀ hq hr (by decide : (2 : ℕ) ≠ 0)).1
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg ℓ)]
  simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using centralBinomialRatio_sq_le hℓ

/-- Given the diagonal formula, the connection average is bounded uniformly in the upper degree. -/
theorem connectionAverage_le_two_sqrt_succ (s : Finset ℤ) (p : ℤ → ℝ) {M ℓ : ℕ}
    (hℓM : ℓ ≤ M) (hp : ∀ v ∈ s, 0 ≤ p v) (hs : ∀ v ∈ s, |(v : ℝ)| ≤ (ℓ : ℝ))
    (hdiag : connectionAverage s p ℓ ℓ = (4 : ℝ) ^ ℓ / ((2 * ℓ).choose ℓ : ℝ)) :
    connectionAverage s p M ℓ ≤ 2 * Real.sqrt ((ℓ : ℝ) + 1) := by
  apply (connectionAverage_antitone s p le_rfl hℓM hp hs).trans
  rw [hdiag]
  by_cases hℓ : 1 ≤ ℓ
  · exact (four_pow_div_choose_le_two_sqrt hℓ).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_add_of_nonneg_right zero_le_one))
        (by norm_num))
  · have h : ℓ = 0 := by omega
    norm_num [h]

end Zalcman
