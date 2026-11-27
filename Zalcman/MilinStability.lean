/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Milin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Stability of Taylor masses and Toeplitz rows

Reflection at a nearly saturated coefficient bounds each shorter squared mass.
Combining this bound with the Lebedev–Milin remainders controls the sum of
squared errors in the lower triangular part of the coefficient Gram matrix.
-/

public section

namespace Zalcman.MilinCoefficients

open Finset
open scoped BigOperators ComplexConjugate

variable (d : MilinCoefficients)

private theorem partialMass_nonneg (j : ℕ) : 0 ≤ d.partialMass j :=
  sum_nonneg (fun _ _ => sq_nonneg _)

private theorem partialMass_le_of_milin_nonneg (hT : ∀ j, 0 ≤ d.milinSum j) (j : ℕ) :
    d.partialMass j ≤ j := by
  by_cases hj : j = 0
  · simp [hj, partialMass]
  · exact d.partialMass_le_index (Nat.pos_of_ne_zero hj) (hT j)

private theorem exists_norm_one_phase {a : ℂ} (ha : a ≠ 0) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ (conj ω * a).re = ‖a‖ := by
  have hA : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hA' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA
  refine ⟨a / (‖a‖ : ℂ), ?_, ?_⟩
  · rw [norm_div, Complex.norm_of_nonneg (norm_nonneg a), div_self hA]
  · have he : conj (a / (‖a‖ : ℂ)) * a = (‖a‖ : ℂ) := by
      rw [map_div₀, Complex.conj_ofReal]
      calc
        _ = a * conj a / (‖a‖ : ℂ) := by ring
        _ = _ := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow,
            pow_two, mul_div_cancel_right₀ _ hA']
    simpa using congrArg Complex.re he

private theorem sqrt_sum_sq_sub_sq_le {j : ℕ} (x y : ℕ → ℂ) :
    (Real.sqrt (∑ i ∈ range j, ‖x i‖ ^ 2) -
      Real.sqrt (∑ i ∈ range j, ‖y i‖ ^ 2)) ^ 2 ≤
      ∑ i ∈ range j, ‖x i - y i‖ ^ 2 := by
  have hx : (Real.sqrt (∑ i ∈ range j, ‖x i‖ ^ 2)) ^ 2 =
      ∑ i ∈ range j, ‖x i‖ ^ 2 :=
    Real.sq_sqrt (sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hy : (Real.sqrt (∑ i ∈ range j, ‖y i‖ ^ 2)) ^ 2 =
      ∑ i ∈ range j, ‖y i‖ ^ 2 :=
    Real.sq_sqrt (sum_nonneg fun _ _ ↦ sq_nonneg _)
  have h := Real.sum_mul_le_sqrt_mul_sqrt (range j) (fun i ↦ ‖x i‖) (fun i ↦ ‖y i‖)
  calc
    _ ≤ (∑ i ∈ range j, ‖x i‖ ^ 2) + (∑ i ∈ range j, ‖y i‖ ^ 2) -
        2 * ∑ i ∈ range j, ‖x i‖ * ‖y i‖ := by nlinarith only [hx, hy, h]
    _ = ∑ i ∈ range j, (‖x i‖ - ‖y i‖) ^ 2 := by
      simp only [sub_sq, sum_add_distrib, sum_sub_distrib, mul_assoc, ← mul_sum]
      ring
    _ ≤ _ := by
      refine sum_le_sum fun i _ ↦ ?_
      simpa only [sq_abs] using
        pow_le_pow_left₀ (abs_nonneg _) (abs_norm_sub_norm_le (x i) (y i)) 2

private theorem tail_partialMass_eq {j n : ℕ} (hjn : j ≤ n) :
    ∑ i ∈ range j, ‖d.c (n - 1 - i)‖ ^ 2 = d.partialMass n - d.partialMass (n - j) := by
  have hsum := sum_range_add (fun i ↦ ‖d.c i‖ ^ 2) (n - j) j
  rw [Nat.sub_add_cancel hjn, ← partialMass, ← partialMass] at hsum
  calc
    _ = ∑ i ∈ range j, ‖d.c ((n - j) + (j - 1 - i))‖ ^ 2 := by
      refine sum_congr rfl fun i hi ↦ ?_
      have hi' := mem_range.mp hi
      have he : n - 1 - i = (n - j) + (j - 1 - i) := by omega
      rw [he]
    _ = ∑ i ∈ range j, ‖d.c ((n - j) + i)‖ ^ 2 :=
      sum_range_reflect (fun i ↦ ‖d.c ((n - j) + i)‖ ^ 2) j
    _ = _ := by linarith

/-- Reflection at the coefficient with index `n` controls the squared deficit of every
initial Taylor mass through index `n`. -/
theorem partialMass_deficit_sq_le (hT : ∀ j, 0 ≤ d.milinSum j)
    {j n : ℕ} (hn : 6 ≤ n) (hjn : j ≤ n) (hD : (n : ℝ) - ‖d.squareCoeff n‖ ≤ 3) :
    ((j : ℝ) - d.partialMass j) ^ 2 ≤ 24 * j * ((n : ℝ) - ‖d.squareCoeff n‖) := by
  set D : ℝ := n - ‖d.squareCoeff n‖ with hDef
  have hD₀ : 0 ≤ D := sub_nonneg.mpr (d.norm_squareCoeff_le_index (by omega) (hT n))
  have hnR : 6 ≤ (n : ℝ) := by exact_mod_cast hn
  have han : d.squareCoeff n ≠ 0 := by
    intro ha
    have hD' : (n : ℝ) - ‖d.squareCoeff n‖ ≤ 3 := hD
    rw [ha, norm_zero, sub_zero] at hD'
    linarith
  obtain ⟨ω, hω, hωre⟩ := exists_norm_one_phase han
  have href := d.reflection_norm_sq n hω
  rw [hωre] at href
  have hpj : d.partialMass j ≤ (j : ℝ) := d.partialMass_le_of_milin_nonneg hT j
  have hpn : d.partialMass n ≤ (n : ℝ) := d.partialMass_le_of_milin_nonneg hT n
  have herror : ∑ i ∈ range j, ‖d.c i - ω * conj (d.c (n - 1 - i))‖ ^ 2 ≤ 2 * D := by
    calc
      _ ≤ ∑ i ∈ range n, ‖d.c i - ω * conj (d.c (n - 1 - i))‖ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (range_mono hjn) (fun _ _ _ ↦ sq_nonneg _)
      _ ≤ _ := by rw [href, hDef]; linarith
  have htail : ∑ i ∈ range j, ‖ω * conj (d.c (n - 1 - i))‖ ^ 2 =
      d.partialMass n - d.partialMass (n - j) := by
    simp_rw [norm_mul, hω, one_mul, Complex.norm_conj]
    exact d.tail_partialMass_eq hjn
  have htail₀ : 0 ≤ d.partialMass n - d.partialMass (n - j) := by
    rw [← htail]
    exact sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have htail_lower : (j : ℝ) - D ≤ d.partialMass n - d.partialMass (n - j) := by
    have hA := d.norm_squareCoeff_le_partialMass n
    have hB := d.partialMass_le_of_milin_nonneg hT (n - j)
    rw [Nat.cast_sub hjn] at hB
    rw [hDef]
    linarith
  let x : ℝ := Real.sqrt (d.partialMass j)
  let y : ℝ := Real.sqrt (d.partialMass n - d.partialMass (n - j))
  let z : ℝ := Real.sqrt j
  have hclose : (x - y) ^ 2 ≤ 2 * D := by
    have h := sqrt_sum_sq_sub_sq_le (j := j) d.c (fun i ↦ ω * conj (d.c (n - 1 - i)))
    rw [← partialMass, htail] at h
    exact h.trans herror
  have hx₀ : 0 ≤ x := Real.sqrt_nonneg _
  have hy₀ : 0 ≤ y := Real.sqrt_nonneg _
  have hz₀ : 0 ≤ z := Real.sqrt_nonneg _
  have hxsq : x ^ 2 = d.partialMass j := Real.sq_sqrt (d.partialMass_nonneg j)
  have hysq : y ^ 2 = d.partialMass n - d.partialMass (n - j) := Real.sq_sqrt htail₀
  have hzsq : z ^ 2 = (j : ℝ) := Real.sq_sqrt (by positivity)
  have hxz : x ≤ z := Real.sqrt_le_sqrt hpj
  have hgap : (z - x) ^ 2 ≤ 6 * D := by
    rcases le_total y z with hyz | hzy
    · have hzyD : (z - y) ^ 2 ≤ D := by
        nlinarith only [htail_lower, hysq, hzsq, mul_nonneg (sub_nonneg.mpr hyz) hy₀]
      calc
        _ ≤ 2 * (z - y) ^ 2 + 2 * (x - y) ^ 2 := by
          nlinarith only [sq_nonneg (z - y - (y - x))]
        _ ≤ _ := by linarith only [hzyD, hclose]
    · calc
        _ ≤ (y - x) ^ 2 := pow_le_pow_left₀ (sub_nonneg.mpr hxz) (sub_le_sub_right hzy x) 2
        _ = (x - y) ^ 2 := by ring
        _ ≤ _ := hclose.trans (by linarith)
  have hsum : (z + x) ^ 2 ≤ 4 * (j : ℝ) := by
    have h := pow_le_pow_left₀ (add_nonneg hz₀ hx₀) (show z + x ≤ 2 * z by linarith) 2
    nlinarith only [h, hzsq]
  have hprod : (z - x) * (z + x) = (j : ℝ) - d.partialMass j := by
    nlinarith only [hxsq, hzsq]
  calc
    _ = (z - x) ^ 2 * (z + x) ^ 2 := by rw [← hprod, mul_pow]
    _ ≤ (6 * D) * (4 * j) := mul_le_mul hgap hsum (sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- The mass of each positive initial block is bounded below by an absolute
multiple of its length in the regime of small coefficient deficit. -/
theorem index_le_mul_partialMass (hT : ∀ j, 0 ≤ d.milinSum j)
    {j n : ℕ} (hn : 6 ≤ n) (hj : 0 < j) (hjn : j ≤ n)
    (hD : (n : ℝ) - ‖d.squareCoeff n‖ ≤ 3) : (j : ℝ) ≤ 288 * d.partialMass j := by
  have hA := d.one_le_partialMass hj
  have hj' : 0 < (j : ℝ) := by positivity
  by_cases h : (j : ℝ) ≤ 288
  · linarith
  · have hsq := d.partialMass_deficit_sq_le hT hn hjn hD
    have hsq' : ((j : ℝ) - d.partialMass j) ^ 2 ≤ 72 * j :=
      hsq.trans (by nlinarith only [mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 24 * (j : ℝ))])
    have hA' : (j : ℝ) / 2 ≤ d.partialMass j := by
      by_contra! hl
      have hgap : (j : ℝ) / 2 < (j : ℝ) - d.partialMass j := by linarith
      have hlt := pow_lt_pow_left₀ hgap (by positivity) (by decide : (2 : ℕ) ≠ 0)
      have hlarge : 72 * (j : ℝ) ≤ ((j : ℝ) / 2) ^ 2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr (le_of_not_ge h)) hj'.le]
      exact hlt.not_ge (hsq'.trans hlarge)
    linarith

/-- The squared mass deficit divided by the Taylor mass is bounded by the original deficit. -/
theorem partialMass_deficit_sq_div_le (hT : ∀ j, 0 ≤ d.milinSum j)
    {j n : ℕ} (hn : 6 ≤ n) (hj : 0 < j) (hjn : j ≤ n)
    (hD : (n : ℝ) - ‖d.squareCoeff n‖ ≤ 3) :
    ((j : ℝ) - d.partialMass j) ^ 2 / d.partialMass j ≤ 6912 * ((n : ℝ) - ‖d.squareCoeff n‖) := by
  set D : ℝ := n - ‖d.squareCoeff n‖
  have hD₀ : 0 ≤ D := sub_nonneg.mpr (d.norm_squareCoeff_le_index (by omega) (hT n))
  apply (div_le_iff₀ (d.partialMass_pos hj)).2
  calc
    _ ≤ 24 * j * D := d.partialMass_deficit_sq_le hT hn hjn hD
    _ ≤ 24 * (288 * d.partialMass j) * D :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (d.index_le_mul_partialMass hT hn hj hjn hD) (by norm_num)) hD₀
    _ = _ := by ring

/-- Every individual squared Taylor coefficient in the initial block grows at most as the
square root of the length of the block when the coefficient deficit is at most three. -/
theorem norm_sq_le_sqrt_index (hT : ∀ j, 0 ≤ d.milinSum j)
    {i n : ℕ} (hn : 6 ≤ n) (hin : i < n) (hD : (n : ℝ) - ‖d.squareCoeff n‖ ≤ 3) :
    ‖d.c i‖ ^ 2 ≤ 10 * Real.sqrt n := by
  have hA := d.partialMass_le_of_milin_nonneg hT i
  have hnR : 1 ≤ (n : ℝ) := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hroot : 1 ≤ Real.sqrt (n : ℝ) := by
    simpa using Real.sqrt_le_sqrt hnR
  have hsq := d.partialMass_deficit_sq_le hT hn hin.le hD
  have hgap : (i : ℝ) - d.partialMass i ≤ 9 * Real.sqrt n := by
    apply (pow_le_pow_iff_left₀ (sub_nonneg.mpr hA) (by positivity) (by decide : (2 : ℕ) ≠ 0)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ))]
    have hiR : (i : ℝ) ≤ n := by exact_mod_cast hin.le
    have hD' := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 24 * (i : ℝ))
    linarith only [hsq, hD', hiR, hnR]
  have hsucc := d.partialMass_le_of_milin_nonneg hT (i + 1)
  rw [d.partialMass_succ, Nat.cast_succ] at hsucc
  linarith

/-- Squared errors against the logarithmic Toeplitz coefficients strictly below the diagonal. -/
@[expose] noncomputable def toeplitzError (n : ℕ) : ℝ :=
  ∑ j ∈ range (n - 1), ∑ i ∈ range (j + 1), ‖d.c (j + 1) * conj (d.c i) - d.t (j + 1 - i)‖ ^ 2

/-- An absolute linear bound on the squared Toeplitz error in the length times the deficit. -/
theorem exists_index_for_toeplitzError :
    ∃ N : ℕ, 6 ≤ N ∧ ∀ (d : MilinCoefficients) (n : ℕ), N ≤ n →
      (∀ j, 0 ≤ d.milinSum j) → (n : ℝ) - ‖d.squareCoeff n‖ ≤ 3 →
      d.toeplitzError n ≤ 6920 * n * ((n : ℝ) - ‖d.squareCoeff n‖) := by
  obtain ⟨N, hN, hsmall⟩ := exists_index_for_small_remainders
  refine ⟨N, hN, ?_⟩
  intro d n hn hT hD
  have hn₆ := hN.trans hn
  have hn' : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by positivity
  set D : ℝ := n - ‖d.squareCoeff n‖
  have hD₀ : 0 ≤ D := sub_nonneg.mpr (d.norm_squareCoeff_le_index hn' (hT n))
  have hRsum := (hsmall d n hn (hT n) hD).2.2
  have hR : ∑ i ∈ range (n - 1), d.remainder (i + 1) ≤ 8 * (n : ℝ) * D := calc
    _ ≤ ∑ i ∈ range (n - 1), (n : ℝ) ^ 2 * (d.remainder (i + 1) / ((i : ℝ) + 1) ^ 2) := by
      refine sum_le_sum fun i hi ↦ ?_
      have hi' : i + 1 ≤ n := by have hi := mem_range.mp hi; omega
      have hiR : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi'
      have hR₀ := d.remainder_nonneg (Nat.zero_lt_succ i)
      have hRdiv₀ : 0 ≤ d.remainder (i + 1) / ((i : ℝ) + 1) ^ 2 := by positivity
      calc
        _ = ((i : ℝ) + 1) ^ 2 * (d.remainder (i + 1) / ((i : ℝ) + 1) ^ 2) := by
          rw [mul_comm, div_mul_cancel₀ _ (by positivity)]
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hiR 2) hRdiv₀
    _ = (n : ℝ) ^ 2 * ∑ i ∈ range (n - 1), d.remainder (i + 1) / ((i : ℝ) + 1) ^ 2 := by
      rw [mul_sum]
    _ ≤ (n : ℝ) ^ 2 * (8 * D / n) := mul_le_mul_of_nonneg_left hRsum (sq_nonneg _)
    _ = _ := by field_simp
  have hc : ∑ i ∈ range (n - 1), ‖d.c (i + 1)‖ ^ 2 ≤ (n : ℝ) := by
    have hsum : d.partialMass n = 1 + ∑ i ∈ range (n - 1), ‖d.c (i + 1)‖ ^ 2 := calc
      _ = d.partialMass (1 + (n - 1)) := by congr 1; omega
      _ = d.partialMass 1 + ∑ i ∈ range (n - 1), ‖d.c (1 + i)‖ ^ 2 :=
        sum_range_add (fun i ↦ ‖d.c i‖ ^ 2) 1 (n - 1)
      _ = _ := by simp only [d.partialMass_one, Nat.add_comm 1]
    have hA := d.partialMass_le_of_milin_nonneg hT n
    rw [hsum] at hA
    linarith
  let k : ℕ → ℝ := fun i ↦ ((i : ℝ) + 1 - d.partialMass (i + 1)) ^ 2 / d.partialMass (i + 1)
  have hk : ∑ i ∈ range (n - 1), k i * ‖d.c (i + 1)‖ ^ 2 ≤ 6912 * (n : ℝ) * D := calc
    _ ≤ ∑ i ∈ range (n - 1), (6912 * D) * ‖d.c (i + 1)‖ ^ 2 := by
      refine sum_le_sum fun i hi ↦ ?_
      have hi' : i + 1 ≤ n := by have hi := mem_range.mp hi; omega
      have hki := d.partialMass_deficit_sq_div_le hT hn₆ (Nat.zero_lt_succ i) hi' hD
      simp only [Nat.cast_succ] at hki
      exact mul_le_mul_of_nonneg_right hki (sq_nonneg _)
    _ = (6912 * D) * ∑ i ∈ range (n - 1), ‖d.c (i + 1)‖ ^ 2 := by rw [mul_sum]
    _ ≤ (6912 * D) * n := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring
  calc
    d.toeplitzError n = ∑ i ∈ range (n - 1), (d.remainder (i + 1) + k i * ‖d.c (i + 1)‖ ^ 2) := by
      refine sum_congr rfl fun i _ ↦ ?_
      simpa only [k, Nat.cast_succ] using d.toeplitz_row_norm_sq (Nat.zero_lt_succ i)
    _ = (∑ i ∈ range (n - 1), d.remainder (i + 1)) +
        ∑ i ∈ range (n - 1), k i * ‖d.c (i + 1)‖ ^ 2 := sum_add_distrib
    _ ≤ 8 * (n : ℝ) * D + 6912 * (n : ℝ) * D := add_le_add hR hk
    _ = _ := by ring

end Zalcman.MilinCoefficients
