/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Milin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reflection estimates for Taylor coefficient blocks

Reflection in the endpoint of a coefficient convolution extends an initial square-summable
estimate to intervals near twice its length. The logarithmic mass deficit and this extended
estimate then bound the real-part deficit at the target index.
-/

public section

open Finset
open scoped ComplexConjugate

namespace Zalcman.MilinCoefficients

variable (d : MilinCoefficients)

/-- The real-part deficit relative to the phase of the normalized square. -/
@[expose] def phaseDeficit (α : ℂ) (j : ℕ) : ℝ :=
  j - (conj (α ^ 2) * d.squareCoeff j).re

/-- Multiplication of the square-root coefficients by the conjugate of their reference phase. -/
def phasedCoeff (α : ℂ) (i : ℕ) : ℂ := conj α * d.c i

/-- The squared distance of an initial coefficient block from the reference constant. -/
noncomputable def blockError (α : ℂ) (j : ℕ) : ℝ :=
  ∑ i ∈ range j, ‖d.phasedCoeff α i - 1‖ ^ 2

theorem blockError_nonneg (α : ℂ) (j : ℕ) : 0 ≤ d.blockError α j := by
  exact sum_nonneg (fun _ _ => sq_nonneg _)

/-- Increasing a block cannot decrease its squared error. -/
theorem blockError_mono (α : ℂ) : Monotone (d.blockError α) := by
  intro i j hij
  unfold blockError
  exact sum_le_sum_of_subset_of_nonneg (range_mono hij) (fun _ _ _ => sq_nonneg _)

/-- The block error is the squared distance to the unscaled unit constant. -/
theorem blockError_eq_sum_norm_sub {α : ℂ} (hα : ‖α‖ = 1) (j : ℕ) :
    d.blockError α j = ∑ i ∈ range j, ‖d.c i - α‖ ^ 2 := by
  have hunit : conj α * α = 1 := by rw [Complex.conj_mul', hα]; norm_num
  unfold blockError
  apply sum_congr rfl
  intro i _
  rw [phasedCoeff, ← hunit, ← mul_sub, norm_mul, Complex.norm_conj, hα, one_mul]

private theorem norm_sub_conj_sq_le (u v : ℂ) :
    ‖u - conj v‖ ^ 2 ≤ 2 * ‖u - 1‖ ^ 2 + 2 * ‖v - 1‖ ^ 2 := by
  have heq : u - conj v = (u - 1) - conj (v - 1) := by simp
  have hnorm : ‖u - conj v‖ ≤ ‖u - 1‖ + ‖v - 1‖ := by
    rw [heq]
    simpa only [Complex.norm_conj] using norm_sub_le (u - 1) (conj (v - 1))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith only [hsq, sq_nonneg (‖u - 1‖ - ‖v - 1‖)]

private theorem norm_sub_one_sq_le (u v : ℂ) :
    ‖u - 1‖ ^ 2 ≤ 2 * ‖u - conj v‖ ^ 2 + 2 * ‖v - 1‖ ^ 2 := by
  have hnorm : ‖u - 1‖ ≤ ‖u - conj v‖ + ‖v - 1‖ := by
    calc
      ‖u - 1‖ = ‖(u - conj v) + conj (v - 1)‖ := by
        simp only [map_sub, map_one]
        congr 1
        ring
      _ ≤ ‖u - conj v‖ + ‖v - 1‖ := by
        simpa only [Complex.norm_conj] using norm_add_le (u - conj v) (conj (v - 1))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith only [hsq, sq_nonneg (‖u - conj v‖ - ‖v - 1‖)]

/-- Reflection expresses the phase deficit as a mass deficit plus a nonnegative error. -/
theorem phaseDeficit_eq_reflection {α : ℂ} (hα : ‖α‖ = 1) (j : ℕ) :
    d.phaseDeficit α j = j - d.partialMass j +
      (∑ i ∈ range j, ‖d.phasedCoeff α i - conj (d.phasedCoeff α (j - 1 - i))‖ ^ 2) / 2 := by
  have hunit : conj α * α = 1 := by rw [Complex.conj_mul', hα]; norm_num
  have hphase : conj α * α ^ 2 = α := calc
    _ = (conj α * α) * α := by ring
    _ = _ := by simp [hunit]
  have hterm (i : ℕ) :
      d.phasedCoeff α i - conj (d.phasedCoeff α (j - 1 - i)) =
        conj α * (d.c i - α ^ 2 * conj (d.c (j - 1 - i))) := by
    simp only [phasedCoeff, map_mul, Complex.conj_conj, mul_sub, ← mul_assoc, hphase]
  have h := d.reflection_norm_sq j (ω := α ^ 2) (by simp [norm_pow, hα])
  simp only [phaseDeficit, hterm, norm_mul, Complex.norm_conj, hα, one_mul, h]
  ring

/-- Reflection bounds the real-part deficit using the distance from a constant sequence. -/
theorem phaseDeficit_le_massDeficit_add_blockError {α : ℂ} (hα : ‖α‖ = 1) (j : ℕ) :
    d.phaseDeficit α j ≤ j - d.partialMass j + 2 * d.blockError α j := by
  have h := sum_le_sum (s := range j) (fun i _ =>
    norm_sub_conj_sq_le (d.phasedCoeff α i) (d.phasedCoeff α (j - 1 - i)))
  rw [sum_add_distrib, ← mul_sum, ← mul_sum,
    sum_range_reflect (fun i => ‖d.phasedCoeff α i - 1‖ ^ 2) j, ← blockError] at h
  rw [d.phaseDeficit_eq_reflection hα]
  linarith

/-- An endpoint with small phase deficit gives a reflected interval with small error. -/
theorem reflectedBlock_le {α : ℂ} (hα : ‖α‖ = 1) {n j : ℕ} (hnj : n ≤ j)
    (hMass : d.partialMass j ≤ j) :
    (∑ i ∈ Ico (j - n) j, ‖d.phasedCoeff α i - 1‖ ^ 2) ≤
      4 * d.phaseDeficit α j + 2 * d.blockError α n := by
  have hpair := sum_le_sum (s := Ico (j - n) j) (fun i _ =>
    norm_sub_one_sq_le (d.phasedCoeff α i) (d.phasedCoeff α (j - 1 - i)))
  have hrefl (g : ℕ → ℝ) : (∑ i ∈ Ico (j - n) j, g (j - 1 - i)) = ∑ i ∈ range n, g i := by
    have hj : j = 0 ∨ 0 < j := Nat.eq_zero_or_pos j
    rcases hj with rfl | hj
    · have : n = 0 := by omega
      simp [this]
    rw [sum_Ico_reflect g (j - n) (m := j) (n := j - 1) (by omega)]
    have hstart : j - 1 + 1 - j = 0 := by omega
    have hend : j - 1 + 1 - (j - n) = n := by omega
    rw [hstart, hend, Nat.Ico_zero_eq_range]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum,
    hrefl (fun i => ‖d.phasedCoeff α i - 1‖ ^ 2), ← blockError] at hpair
  have hle := sum_le_sum_of_subset_of_nonneg
    (s := Ico (j - n) j) (t := range j)
    (f := fun i => ‖d.phasedCoeff α i - conj (d.phasedCoeff α (j - 1 - i))‖ ^ 2)
    (by intro i hi; exact mem_range.mpr (mem_Ico.mp hi).2)
    (by intros; positivity)
  have hdef := d.phaseDeficit_eq_reflection hα j
  linarith only [hpair, hle, hdef, hMass]

private theorem sum_union_le_add_sum (s t : Finset ℕ) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) :
    (∑ i ∈ s ∪ t, w i) ≤ (∑ i ∈ s, w i) + ∑ i ∈ t, w i := by
  have h := sum_union_inter (s₁ := s) (s₂ := t) (f := w)
  have hnonneg : 0 ≤ ∑ i ∈ s ∩ t, w i := sum_nonneg (fun i _ => hw i)
  linarith

/-- Two reflected intervals extend the initial block to any endpoint that they cover. -/
theorem blockError_le_of_cover {α : ℂ} (hα : ‖α‖ = 1) {n j₁ j₂ m : ℕ}
    (hn₁ : n ≤ j₁) (hn₂ : n ≤ j₂) (h₁ : j₁ - n ≤ n) (h₂ : j₂ - n ≤ j₁)
    (hm : m ≤ j₂) (hMass₁ : d.partialMass j₁ ≤ j₁) (hMass₂ : d.partialMass j₂ ≤ j₂) :
    d.blockError α m ≤ 5 * d.blockError α n +
      4 * (d.phaseDeficit α j₁ + d.phaseDeficit α j₂) := by
  let s := range n
  let t := Ico (j₁ - n) j₁
  let u := Ico (j₂ - n) j₂
  let w (i : ℕ) := ‖d.phasedCoeff α i - 1‖ ^ 2
  have hw (i : ℕ) : 0 ≤ w i := by dsimp [w]; positivity
  have hs : range m ⊆ (s ∪ t) ∪ u := by
    intro i hi
    have hi' := mem_range.mp hi
    by_cases hin : i < n
    · exact mem_union_left _ (mem_union_left _ (mem_range.mpr hin))
    by_cases hi₁ : i < j₁
    · exact mem_union_left _ (mem_union_right _ (mem_Ico.mpr ⟨by omega, hi₁⟩))
    exact mem_union_right _ (mem_Ico.mpr ⟨by omega, by omega⟩)
  have hsub := sum_le_sum_of_subset_of_nonneg (f := w) hs (fun i _ _ => hw i)
  have hsum₁ := sum_union_le_add_sum s t hw
  have hsum₂ := sum_union_le_add_sum (s ∪ t) u hw
  have hbound₁ := d.reflectedBlock_le hα hn₁ hMass₁
  have hbound₂ := d.reflectedBlock_le hα hn₂ hMass₂
  dsimp only [s, t, u, w] at hsub hsum₁ hsum₂
  change d.blockError α m ≤ _ at hsub
  change (∑ i ∈ range n ∪ Ico (j₁ - n) j₁, _) ≤ d.blockError α n + _ at hsum₁
  linarith only [hsub, hsum₁, hsum₂, hbound₁, hbound₂]

/-- The logarithmic mass deficit bounds the linear mass deficit. -/
theorem massDeficit_le_milinSum_add_logRemainder {j : ℕ} (hj : 0 < j) :
    (j : ℝ) - d.partialMass j ≤ d.milinSum j + j * d.logRemainder j := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hA := d.partialMass_pos hj
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hj' hA)
  rw [inv_div] at hlog
  have hh := mul_le_mul_of_nonneg_left hlog hj'.le
  have heq : (j : ℝ) * (1 - d.partialMass j / j) = j - d.partialMass j := by
    field_simp
  rw [heq] at hh
  calc
    _ ≤ (j : ℝ) * Real.log (j / d.partialMass j) := hh
    _ = _ := by rw [logRemainder]; field_simp; ring

/-- At the target index the phase deficit is controlled by the two Milin terms and block error. -/
theorem phaseDeficit_le_milinSum_add_logRemainder_add_blockError {α : ℂ} (hα : ‖α‖ = 1)
    {j : ℕ} (hj : 0 < j) :
    d.phaseDeficit α j ≤ d.milinSum j + j * d.logRemainder j + 2 * d.blockError α j :=
  (d.phaseDeficit_le_massDeficit_add_blockError hα j).trans
    (add_le_add_left (d.massDeficit_le_milinSum_add_logRemainder hj) _)

end Zalcman.MilinCoefficients
