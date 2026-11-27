/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.MilinStability
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Phase alignment and rank-one Gram matrices

Near agreement of two rank-one Gram matrices gives near agreement of their
generating vectors after multiplication by a unit phase.
-/

public section

namespace Zalcman

open Finset
open scoped BigOperators ComplexConjugate

private theorem gram_entry_norm_sq (a b c d : ℂ) :
    ‖a * conj b - c * conj d‖ ^ 2 =
      ‖a‖ ^ 2 * ‖b‖ ^ 2 + ‖c‖ ^ 2 * ‖d‖ ^ 2 -
        2 * (conj (c * conj a) * (d * conj b)).re := by
  have h : (a * conj b) * conj (c * conj d) = conj (c * conj a) * (d * conj b) := by
    simp only [map_mul, Complex.conj_conj]
    ring
  simp only [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_conj, h]

private theorem sum_gram_cross_re (z : ℕ → ℂ) (m : ℕ) :
    ∑ i ∈ range m, ∑ j ∈ range m, (conj (z i) * z j).re =
      ‖∑ i ∈ range m, z i‖ ^ 2 := by
  simp only [← Complex.re_sum, ← mul_sum, ← sum_mul, ← map_sum]
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The squared Hilbert–Schmidt norm of the difference of the two Gram matrices. -/
theorem gramDifference_norm_sq (x y : ℕ → ℂ) (m : ℕ) :
    ∑ i ∈ range m, ∑ j ∈ range m,
      ‖x i * conj (x j) - y i * conj (y j)‖ ^ 2 =
        (∑ i ∈ range m, ‖x i‖ ^ 2) ^ 2 + (∑ i ∈ range m, ‖y i‖ ^ 2) ^ 2 -
          2 * ‖∑ i ∈ range m, y i * conj (x i)‖ ^ 2 := by
  have hdiag (v : ℕ → ℂ) :
      ∑ i ∈ range m, ∑ j ∈ range m, ‖v i‖ ^ 2 * ‖v j‖ ^ 2 =
        (∑ i ∈ range m, ‖v i‖ ^ 2) ^ 2 := by
    simp only [← mul_sum, ← sum_mul, pow_two]
  have hcross :
      ∑ i ∈ range m, ∑ j ∈ range m, 2 * (conj (y i * conj (x i)) * (y j * conj (x j))).re =
        2 * ‖∑ i ∈ range m, y i * conj (x i)‖ ^ 2 := by
    simp only [← mul_sum, sum_gram_cross_re]
  simp only [gram_entry_norm_sq, sum_add_distrib, sum_sub_distrib, hdiag, hcross]

private theorem normSq_sub_smul_eq (x y ω : ℂ) (hω : ‖ω‖ = 1) :
    ‖y - ω * x‖ ^ 2 = ‖y‖ ^ 2 + ‖x‖ ^ 2 - 2 * (conj ω * (y * conj x)).re := by
  have h : y * conj (ω * x) = conj ω * (y * conj x) := by
    rw [map_mul]
    ring
  have hω' : Complex.normSq ω = 1 := by simp [Complex.normSq_eq_norm_sq, hω]
  simp only [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_mul, hω', one_mul, h]

/-- Expansion of the squared distance from a phase multiple of a fixed vector. -/
theorem phaseError_norm_sq (x y : ℕ → ℂ) (m : ℕ) {ω : ℂ} (hω : ‖ω‖ = 1) :
    ∑ i ∈ range m, ‖y i - ω * x i‖ ^ 2 =
      (∑ i ∈ range m, ‖x i‖ ^ 2) + (∑ i ∈ range m, ‖y i‖ ^ 2) -
        2 * (conj ω * ∑ i ∈ range m, y i * conj (x i)).re := by
  simp only [normSq_sub_smul_eq _ _ _ hω, sum_sub_distrib, sum_add_distrib, ← mul_sum,
    ← Complex.re_sum]
  ring

/-- For a phase attaining the modulus of the scalar product, the Gram error controls
the phase-aligned squared distance weighted by the smaller squared mass. -/
theorem min_mass_mul_phaseError_le_gramDifference (x y : ℕ → ℂ) (m : ℕ)
    {ω : ℂ} (hω : ‖ω‖ = 1)
    (hphase : (conj ω * ∑ i ∈ range m, y i * conj (x i)).re =
      ‖∑ i ∈ range m, y i * conj (x i)‖) :
    min (∑ i ∈ range m, ‖x i‖ ^ 2) (∑ i ∈ range m, ‖y i‖ ^ 2) *
        (∑ i ∈ range m, ‖y i - ω * x i‖ ^ 2) ≤
      ∑ i ∈ range m, ∑ j ∈ range m, ‖x i * conj (x j) - y i * conj (y j)‖ ^ 2 := by
  let s : ℝ := ∑ i ∈ range m, ‖x i‖ ^ 2
  let t : ℝ := ∑ i ∈ range m, ‖y i‖ ^ 2
  let r : ℝ := ‖∑ i ∈ range m, y i * conj (x i)‖
  let e : ℝ := ∑ i ∈ range m, ‖y i - ω * x i‖ ^ 2
  change min s t * e ≤ _
  rw [gramDifference_norm_sq]
  change min s t * e ≤ s ^ 2 + t ^ 2 - 2 * r ^ 2
  have he₀ : 0 ≤ e := sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have he : e = s + t - 2 * r := by
    simpa only [e, s, t, r, hphase] using phaseError_norm_sq x y m hω
  have hmin : min s t ≤ (s + t + 2 * r) / 2 := by
    linarith only [min_le_left s t, min_le_right s t, norm_nonneg (∑ i ∈ range m, y i * conj (x i))]
  calc
    _ ≤ ((s + t + 2 * r) / 2) * e := mul_le_mul_of_nonneg_right hmin he₀
    _ ≤ (s - t) ^ 2 / 2 + ((s + t + 2 * r) / 2) * e :=
      le_add_of_nonneg_left (by positivity)
    _ = _ := by rw [he]; ring

private theorem sum_symmetric_square (F : ℕ → ℕ → ℝ) (hF : ∀ i j, F i j = F j i) (m : ℕ) :
    ∑ i ∈ range m, ∑ j ∈ range m, F i j =
      (∑ i ∈ range m, F i i) + 2 * ∑ i ∈ range m, ∑ j ∈ range i, F i j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ (fun i ↦ ∑ j ∈ range (m + 1), F i j),
      sum_range_succ (fun i ↦ F i i), sum_range_succ (fun i ↦ ∑ j ∈ range i, F i j)]
    have hRow (i : ℕ) : ∑ j ∈ range (m + 1), F i j = (∑ j ∈ range m, F i j) + F i m :=
      sum_range_succ (F i) m
    have hsym : ∑ i ∈ range m, F i m = ∑ i ∈ range m, F m i :=
      sum_congr rfl (fun i _ ↦ hF i m)
    simp only [hRow, sum_add_distrib, ih, hsym]
    ring

private theorem norm_sq_sub_le (a b c : ℂ) :
    ‖a - b‖ ^ 2 ≤ 2 * (‖a - c‖ ^ 2 + ‖b - c‖ ^ 2) := by
  have htri : ‖a - b‖ ≤ ‖a - c‖ + ‖b - c‖ := calc
    _ = ‖(a - c) + (c - b)‖ := by congr 1; ring
    _ ≤ ‖a - c‖ + ‖c - b‖ := norm_add_le _ _
    _ = _ := by rw [norm_sub_rev c b]
  have hs := pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith only [hs, sq_nonneg (‖a - c‖ - ‖b - c‖)]

private theorem gram_diagonal_le (x y ω : ℂ) {M : ℝ} (hω : ‖ω‖ = 1)
    (hx : ‖x‖ ^ 2 ≤ M) (hy : ‖y‖ ^ 2 ≤ M) :
    ‖x * conj x - y * conj y‖ ^ 2 ≤ 4 * M * ‖y - ω * x‖ ^ 2 := by
  have h := abs_norm_sub_norm_le y (ω * x)
  rw [norm_mul, hω, one_mul] at h
  have hd := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at hd
  have hs : (‖x‖ + ‖y‖) ^ 2 ≤ 4 * M := by
    nlinarith only [hx, hy, sq_nonneg (‖x‖ - ‖y‖)]
  have hM : 0 ≤ M := (sq_nonneg _).trans hx
  calc
    _ = (‖x‖ ^ 2 - ‖y‖ ^ 2) ^ 2 := by
      rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        sq_abs]
    _ = (‖x‖ + ‖y‖) ^ 2 * (‖y‖ - ‖x‖) ^ 2 := by ring
    _ ≤ _ := mul_le_mul hs hd (sq_nonneg _) (by positivity)

private theorem gram_hermitian_norm (x y : ℕ → ℂ) (i j : ℕ) :
    ‖x i * conj (x j) - y i * conj (y j)‖ ^ 2 =
      ‖x j * conj (x i) - y j * conj (y i)‖ ^ 2 := by
  have h : conj (x i * conj (x j) - y i * conj (y j)) =
      x j * conj (x i) - y j * conj (y i) := by
    simp only [map_sub, map_mul, Complex.conj_conj, mul_comm]
  rw [← h, Complex.norm_conj]

private theorem sum_shift_le (a b : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ range b, f (i + a) ≤ ∑ i ∈ range (a + b), f i := by
  rw [sum_range_add]
  simp only [Nat.add_comm a]
  exact le_add_of_nonneg_left (sum_nonneg fun i _ ↦ hf i)

namespace MilinCoefficients

variable (d : MilinCoefficients)

private theorem toeplitzError_eq_sum_lower (m : ℕ) :
    d.toeplitzError m = ∑ i ∈ range m, ∑ j ∈ range i,
      ‖d.c i * conj (d.c j) - d.t (i - j)‖ ^ 2 := by
  cases m with
  | zero => simp [toeplitzError]
  | succ m =>
    rw [sum_range_succ']
    simp [toeplitzError]

private theorem sum_off_diagonal_le {n h m : ℕ} (hn : h + m = n) :
    ∑ i ∈ range m, ∑ j ∈ range i,
      ‖d.c i * conj (d.c j) - d.c (i + h) * conj (d.c (j + h))‖ ^ 2 ≤
      4 * d.toeplitzError n := by
  let F : ℕ → ℕ → ℝ := fun i j ↦ ‖d.c i * conj (d.c j) - d.t (i - j)‖ ^ 2
  have hF (i j : ℕ) : 0 ≤ F i j := sq_nonneg _
  have hm : m ≤ n := by omega
  have h1 : ∑ i ∈ range m, ∑ j ∈ range i, F i j ≤ d.toeplitzError n := by
    rw [d.toeplitzError_eq_sum_lower]
    exact sum_le_sum_of_subset_of_nonneg (range_mono hm)
      (fun i _ _ ↦ sum_nonneg (fun j _ ↦ hF i j))
  have h2 : ∑ i ∈ range m, ∑ j ∈ range i, F (i + h) (j + h) ≤ d.toeplitzError n := calc
    _ ≤ ∑ i ∈ range m, ∑ j ∈ range (h + i), F (i + h) j := by
      exact sum_le_sum (fun i _ ↦ sum_shift_le h i (F (i + h)) (hF (i + h)))
    _ = ∑ i ∈ range m, (fun k ↦ ∑ j ∈ range k, F k j) (i + h) := by
      simp only [Nat.add_comm h]
    _ ≤ d.toeplitzError n := by
      rw [d.toeplitzError_eq_sum_lower, ← hn]
      exact sum_shift_le h m (fun k ↦ ∑ j ∈ range k, F k j)
        (fun i ↦ sum_nonneg (fun j _ ↦ hF i j))
  calc
    _ ≤ ∑ i ∈ range m, ∑ j ∈ range i, 2 * (F i j + F (i + h) (j + h)) := by
      refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
      simpa only [F, Nat.add_sub_add_right] using
        norm_sq_sub_le (d.c i * conj (d.c j)) (d.c (i + h) * conj (d.c (j + h))) (d.t (i - j))
    _ = 2 * (∑ i ∈ range m, ∑ j ∈ range i, F i j) +
        2 * (∑ i ∈ range m, ∑ j ∈ range i, F (i + h) (j + h)) := by
      simp only [mul_add, sum_add_distrib, ← mul_sum]
    _ ≤ _ := by linarith

private theorem shift_mass_eq_sub {h m n : ℕ} (hn : h + m = n) :
    ∑ i ∈ range m, ‖d.c (i + h)‖ ^ 2 = d.partialMass n - d.partialMass h := by
  have hsum := sum_range_add (fun i ↦ ‖d.c i‖ ^ 2) h m
  rw [hn, ← partialMass, ← partialMass] at hsum
  simp only [Nat.add_comm h] at hsum
  linarith

private theorem partialMass_le_of_nonneg (hT : ∀ j, 0 ≤ d.milinSum j) (j : ℕ) :
    d.partialMass j ≤ j := by
  by_cases hj : j = 0
  · simp [hj, partialMass]
  · exact d.partialMass_le_index (Nat.pos_of_ne_zero hj) (hT j)

private theorem exists_phase_real_part (a : ℂ) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ (conj ω * a).re = ‖a‖ := by
  by_cases ha : a = 0
  · exact ⟨1, by simp, by simp [ha]⟩
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

/-- Shifted blocks of a nearly saturated coefficient sequence are close up to a unit phase. -/
theorem exists_index_for_shift_stability :
    ∃ N : ℕ, 6 ≤ N ∧ ∀ (d : MilinCoefficients) (n h : ℕ), N ≤ n → 1 ≤ h → h ≤ n / 2 →
      (∀ j, 0 ≤ d.milinSum j) → (n : ℝ) - ‖d.squareCoeff n‖ ≤ 3 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ∑ j ∈ range (n - h), ‖d.c (j + h) - ω * d.c j‖ ^ 2 ≤
          (1152 * 8 * 6920 : ℝ) * ((n : ℝ) - ‖d.squareCoeff n‖) := by
  obtain ⟨N, hN, hToeplitz⟩ := exists_index_for_toeplitzError
  refine ⟨max N (46080 ^ 2), hN.trans (le_max_left _ _), ?_⟩
  intro d n h hn _ hh hT hD
  have hnN := (le_max_left N (46080 ^ 2)).trans hn
  have hn₆ := hN.trans hnN
  have hnLarge := (le_max_right N (46080 ^ 2)).trans hn
  have hn₁₂ : 12 ≤ n := (by decide : 12 ≤ 46080 ^ 2).trans hnLarge
  have hnR : 0 < (n : ℝ) := by positivity
  have hn₁₂R : 12 ≤ (n : ℝ) := by exact_mod_cast hn₁₂
  let m : ℕ := n - h
  have hm : h + m = n := Nat.add_sub_of_le (by omega)
  have hm₀ : 0 < m := by omega
  have hnm : n ≤ 2 * m := by omega
  have hnmR : (n : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hnm
  let x := d.c
  let y := fun i : ℕ ↦ d.c (i + h)
  obtain ⟨ω, hω, hphase⟩ := exists_phase_real_part (∑ i ∈ range m, y i * conj (x i))
  let E : ℝ := ∑ j ∈ range m, ‖y j - ω * x j‖ ^ 2
  have hE₀ : 0 ≤ E := sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hx : (n : ℝ) / 576 ≤ ∑ i ∈ range m, ‖x i‖ ^ 2 := by
    change (n : ℝ) / 576 ≤ d.partialMass m
    have h := d.index_le_mul_partialMass hT hn₆ hm₀ (by omega) hD
    linarith
  have hy : (n : ℝ) / 576 ≤ ∑ i ∈ range m, ‖y i‖ ^ 2 := by
    change (n : ℝ) / 576 ≤ ∑ i ∈ range m, ‖d.c (i + h)‖ ^ 2
    rw [d.shift_mass_eq_sub hm]
    have hA := d.norm_squareCoeff_le_partialMass n
    have hhA := d.partialMass_le_of_nonneg hT h
    have hmR : (h : ℝ) + m = n := by exact_mod_cast hm
    linarith
  let F : ℕ → ℕ → ℝ := fun i j ↦ ‖x i * conj (x j) - y i * conj (y j)‖ ^ 2
  have hGramLo : (n : ℝ) / 576 * E ≤ ∑ i ∈ range m, ∑ j ∈ range m, F i j :=
    (mul_le_mul_of_nonneg_right (le_min hx hy) hE₀).trans
      (min_mass_mul_phaseError_le_gramDifference x y m hω hphase)
  have hDiag : ∑ i ∈ range m, F i i ≤ 40 * Real.sqrt n * E := calc
    _ ≤ ∑ i ∈ range m, (4 * (10 * Real.sqrt n)) * ‖y i - ω * x i‖ ^ 2 := by
      refine sum_le_sum fun i hi ↦ ?_
      have hi' := mem_range.mp hi
      exact gram_diagonal_le (x i) (y i) ω hω
        (d.norm_sq_le_sqrt_index hT hn₆ (by omega : i < n) hD)
        (d.norm_sq_le_sqrt_index hT hn₆ (by omega : i + h < n) hD)
    _ = _ := by rw [← mul_sum]; ring
  have hGramHi : ∑ i ∈ range m, ∑ j ∈ range m, F i j ≤
      8 * d.toeplitzError n + 40 * Real.sqrt n * E := by
    rw [sum_symmetric_square F (gram_hermitian_norm x y) m]
    have hoff := d.sum_off_diagonal_le hm
    change (∑ i ∈ range m, ∑ j ∈ range i, F i j) ≤ _ at hoff
    linarith
  have hroot : (46080 : ℝ) ≤ Real.sqrt n := by
    have h : (46080 : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hnLarge
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 46080)] using
      Real.sqrt_le_sqrt h
  have hAbs : 40 * Real.sqrt n ≤ (n : ℝ) / 1152 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hroot) (Real.sqrt_nonneg n),
      Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
  have hErr : (n : ℝ) / 1152 * E ≤ 8 * d.toeplitzError n := by
    linarith only [hGramLo.trans hGramHi, mul_le_mul_of_nonneg_right hAbs hE₀]
  refine ⟨ω, hω, ?_⟩
  change E ≤ _
  apply (mul_le_mul_iff_of_pos_left hnR).mp
  have hTarget := hToeplitz d n hnN hT hD
  linarith only [hErr, hTarget]

end MilinCoefficients

end Zalcman
