/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite interval controls

A time partition gives a measurable piecewise constant control. The integral
of any function of its values is the sum of the values weighted by the
lengths of the pieces.
-/

@[expose] public section

namespace Zalcman

open MeasureTheory Set
open scoped BigOperators

private theorem disjoint_control_intervals {a : ℕ → ℝ} (ha : Monotone a) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (Ioc (a i) (a (i + 1))) (Ioc (a j) (a (j + 1))) := by
  rw [disjoint_left]
  intro x hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge (hi.2.trans (ha (Nat.succ_le_of_lt h)))) hj.1
  · exact (not_lt_of_ge (hj.2.trans (ha (Nat.succ_le_of_lt h)))) hi.1

private theorem exists_piece_of_mem_interval {a : ℕ → ℝ} {x : ℝ} {n : ℕ}
    (hx : x ∈ Ioc (a 0) (a n)) : ∃ i ∈ Finset.range n, x ∈ Ioc (a i) (a (i + 1)) := by
  induction n with
  | zero => exact (not_lt_of_ge hx.2 hx.1).elim
  | succ n ih =>
    by_cases h : x ≤ a n
    · obtain ⟨i, hi, hix⟩ := ih ⟨hx.1, h⟩
      exact ⟨i, Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans (Nat.lt_succ_self n)), hix⟩
    · exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), ⟨lt_of_not_ge h, hx.2⟩⟩

/-- Glue one control to each interval of a finite time partition. The control
has value one outside the partition. -/
noncomputable def glueIntervalControls (n : ℕ) (a : ℕ → ℝ) (q : ℕ → ℝ → ℂ) (t : ℝ) : ℂ :=
  1 + ∑ i ∈ Finset.range n, (Ioc (a i) (a (i + 1))).indicator (fun x ↦ q i x - 1) t

theorem glueIntervalControls_eq_on_piece {n i : ℕ} {a : ℕ → ℝ} {q : ℕ → ℝ → ℂ}
    (ha : Monotone a) (hi : i ∈ Finset.range n) {t : ℝ}
    (ht : t ∈ Ioc (a i) (a (i + 1))) : glueIntervalControls n a q t = q i t := by
  unfold glueIntervalControls
  rw [Finset.sum_eq_single i]
  · rw [indicator_of_mem ht]
    abel
  · intro j _ hji
    exact indicator_of_notMem ((disjoint_left.mp (disjoint_control_intervals ha hji.symm)) ht) _
  · intro h
    exact (h hi).elim

theorem measurable_glueIntervalControls {n : ℕ} (a : ℕ → ℝ) {q : ℕ → ℝ → ℂ}
    (hq : ∀ i ∈ Finset.range n, Measurable (q i)) : Measurable (glueIntervalControls n a q) := by
  exact measurable_const.add (Finset.measurable_sum _ fun i hi ↦
    ((hq i hi).sub measurable_const).indicator measurableSet_Ioc)

theorem norm_glueIntervalControls_eq_one {n : ℕ} {a : ℕ → ℝ} {q : ℕ → ℝ → ℂ}
    (ha : Monotone a) (hq : ∀ i ∈ Finset.range n, ∀ t, ‖q i t‖ = 1) (t : ℝ) :
    ‖glueIntervalControls n a q t‖ = 1 := by
  by_cases h : ∃ i ∈ Finset.range n, t ∈ Ioc (a i) (a (i + 1))
  · obtain ⟨i, hi, ht⟩ := h
    rw [glueIntervalControls_eq_on_piece ha hi ht, hq i hi t]
  · unfold glueIntervalControls
    rw [Finset.sum_eq_zero fun i hi ↦ indicator_of_notMem (fun ht ↦ h ⟨i, hi, ht⟩) _, add_zero, norm_one]

/-- The constant `ζ i` on the `i`th piece of a finite time partition. -/
noncomputable def intervalControl (n : ℕ) (a : ℕ → ℝ) (ζ : ℕ → ℂ) : ℝ → ℂ :=
  glueIntervalControls n a (fun i _ ↦ ζ i)

theorem intervalControl_eq_on_piece {n i : ℕ} {a : ℕ → ℝ} {ζ : ℕ → ℂ}
    (ha : Monotone a) (hi : i ∈ Finset.range n) {t : ℝ}
    (ht : t ∈ Ioc (a i) (a (i + 1))) : intervalControl n a ζ t = ζ i :=
  glueIntervalControls_eq_on_piece ha hi ht

theorem measurable_intervalControl (n : ℕ) (a : ℕ → ℝ) (ζ : ℕ → ℂ) :
    Measurable (intervalControl n a ζ) :=
  measurable_glueIntervalControls a fun _ _ ↦ measurable_const

theorem norm_intervalControl_eq_one {n : ℕ} {a : ℕ → ℝ} {ζ : ℕ → ℂ}
    (ha : Monotone a) (hζ : ∀ i ∈ Finset.range n, ‖ζ i‖ = 1) (t : ℝ) :
    ‖intervalControl n a ζ t‖ = 1 :=
  norm_glueIntervalControls_eq_one ha (fun i hi _ ↦ hζ i hi) t

/-- Integrating a function of the control multiplies each value by the
length of its piece. -/
theorem intervalIntegral_intervalControl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {n : ℕ} {a : ℕ → ℝ} {ζ : ℕ → ℂ} (ha : Monotone a) (G : ℂ → E) :
    (∫ t in a 0..a n, G (intervalControl n a ζ t)) =
      ∑ i ∈ Finset.range n, (a (i + 1) - a i) • G (ζ i) := by
  let I := Ioc (a 0) (a n)
  let P := fun i : ℕ ↦ (Ioc (a i) (a (i + 1))).indicator (fun _ ↦ G (ζ i))
  have heq : EqOn (fun t ↦ G (intervalControl n a ζ t)) (fun t ↦ ∑ i ∈ Finset.range n, P i t) I := by
    intro t ht
    obtain ⟨i, hi, hti⟩ := exists_piece_of_mem_interval ht
    change G (intervalControl n a ζ t) = ∑ i ∈ Finset.range n, P i t
    rw [intervalControl_eq_on_piece ha hi hti, Finset.sum_eq_single i]
    · exact (indicator_of_mem hti (fun _ : ℝ ↦ G (ζ i))).symm
    · intro j _ hji
      exact indicator_of_notMem ((disjoint_left.mp (disjoint_control_intervals ha hji.symm)) hti)
        (fun _ : ℝ ↦ G (ζ j))
    · intro h
      exact (h hi).elim
  have hPInt (i : ℕ) : Integrable (P i) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
  rw [intervalIntegral.integral_of_le (ha (Nat.zero_le n)), setIntegral_congr_fun measurableSet_Ioc heq,
    integral_finsetSum _ (fun i _ ↦ (hPInt i).mono_measure Measure.restrict_le_self)]
  apply Finset.sum_congr rfl
  intro i hi
  have hsub : Ioc (a i) (a (i + 1)) ⊆ I := by
    intro t ht
    exact ⟨(ha (Nat.zero_le i)).trans_lt ht.1, ht.2.trans (ha (Finset.mem_range.mp hi))⟩
  rw [show P i = (Ioc (a i) (a (i + 1))).indicator (fun _ ↦ G (ζ i)) from rfl,
    integral_indicator_const _ measurableSet_Ioc, measureReal_def,
    Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr hsub, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (ha (Nat.le_succ i)))]

/-- Unit control values can be assigned piece lengths proportional to prescribed
nonnegative weights that sum to one. -/
theorem exists_intervalControl_of_weights {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {a b : ℝ} (hab : a ≤ b) {n : ℕ} {w : ℕ → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i ∈ Finset.range n, w i = 1) (ζ : ℕ → ℂ) :
    ∃ A : ℕ → ℝ, Monotone A ∧ A 0 = a ∧ A n = b ∧ ∀ G : ℂ → E,
      (∫ t in a..b, G (intervalControl n A ζ t)) =
        (b - a) • (∑ i ∈ Finset.range n, w i • G (ζ i)) := by
  let A := fun j ↦ a + (b - a) * ∑ i ∈ Finset.range j, w i
  have hA₀ : A 0 = a := by simp [A]
  have hAend : A n = b := by
    dsimp only [A]
    rw [hwsum, mul_one]
    ring
  have hAdiff (i : ℕ) : A (i + 1) - A i = (b - a) * w i := by
    dsimp only [A]
    rw [Finset.sum_range_succ]
    ring
  have hA : Monotone A := monotone_nat_of_le_succ fun i ↦ sub_nonneg.mp (by
    rw [hAdiff]
    exact mul_nonneg (sub_nonneg.mpr hab) (hw i))
  refine ⟨A, hA, hA₀, hAend, fun G ↦ ?_⟩
  simpa only [hA₀, hAend, hAdiff, mul_smul, Finset.smul_sum] using
    intervalIntegral_intervalControl (n := n) (ζ := ζ) hA G

/-- Bounds for complete partition intervals give a uniform bound for all
primitive integrals. The last partial interval costs at most its mesh size
times the pointwise bound. -/
theorem norm_primitive_le_of_interval_partition {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {a : ℕ → ℝ} {n : ℕ}
    (ha : Monotone a) {M η mesh : ℝ} (hM : 0 ≤ M) (hη : 0 ≤ η) (hmesh : 0 ≤ mesh)
    (hInt : IntervalIntegrable f volume (a 0) (a n))
    (hBound : ∀ᵐ t ∂volume.restrict (Ioc (a 0) (a n)), ‖f t‖ ≤ M)
    (hLength : ∀ j < n, a (j + 1) - a j ≤ mesh)
    (hFull : ∀ j < n, ‖∫ t in a j..a (j + 1), f t‖ ≤ η * (a (j + 1) - a j))
    {t : ℝ} (ht : t ∈ Icc (a 0) (a n)) :
    ‖∫ s in a 0..t, f s‖ ≤ η * (a n - a 0) + M * mesh := by
  have hsub {x y : ℝ} (hx : a 0 ≤ x) (hy : y ≤ a n) : Ioc x y ⊆ Ioc (a 0) (a n) :=
    fun _ h ↦ ⟨hx.trans_lt h.1, h.2.trans hy⟩
  have hi {x y : ℝ} (hx : a 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ a n) :
      IntervalIntegrable f volume x y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).mpr (hInt.1.mono_set (hsub hx hy))
  have hprefix (j : ℕ) (hj : j ≤ n) : ‖∫ s in a 0..a j, f s‖ ≤ η * (a j - a 0) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hjlt : j < n := hj
      have hleft := hi le_rfl (ha (Nat.zero_le j)) (ha hjlt.le)
      have hright := hi (ha (Nat.zero_le j)) (ha (Nat.le_succ j)) (ha hj)
      rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
      calc
        _ ≤ ‖∫ s in a 0..a j, f s‖ + ‖∫ s in a j..a (j + 1), f s‖ := norm_add_le _ _
        _ ≤ η * (a j - a 0) + η * (a (j + 1) - a j) := add_le_add (ih hjlt.le) (hFull j hjlt)
        _ = _ := by ring
  by_cases ht₀ : t = a 0
  · rw [ht₀, intervalIntegral.integral_same, norm_zero]
    exact add_nonneg (mul_nonneg hη (sub_nonneg.mpr (ha (Nat.zero_le n)))) (mul_nonneg hM hmesh)
  have htc : t ∈ Ioc (a 0) (a n) := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht₀), ht.2⟩
  obtain ⟨j, hj, hjt⟩ := exists_piece_of_mem_interval htc
  have hjlt : j < n := Finset.mem_range.mp hj
  have hleft := hi le_rfl (ha (Nat.zero_le j)) (ha hjlt.le)
  have hright := hi (ha (Nat.zero_le j)) hjt.1.le ht.2
  have htailAE : ∀ᵐ s ∂volume, s ∈ Ioc (a j) t → ‖f s‖ ≤ M :=
    (ae_restrict_iff' measurableSet_Ioc).mp <|
      ae_mono (Measure.restrict_mono_set volume (hsub (ha (Nat.zero_le j)) ht.2)) hBound
  have htail : ‖∫ s in a j..t, f s‖ ≤ M * (t - a j) := by
    simpa only [abs_of_nonneg (sub_nonneg.mpr hjt.1.le)] using
      (intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := a j) (b := t) (C := M) (f := f)
        (by simpa only [uIoc_of_le hjt.1.le] using htailAE))
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  calc
    _ ≤ ‖∫ s in a 0..a j, f s‖ + ‖∫ s in a j..t, f s‖ := norm_add_le _ _
    _ ≤ η * (a j - a 0) + M * (t - a j) := add_le_add (hprefix j hjlt.le) htail
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (sub_le_sub_right (ha hjlt.le) _) hη)
      (mul_le_mul_of_nonneg_left ((sub_le_sub_right hjt.2 _).trans (hLength j hjlt)) hM)

end Zalcman
