/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.TriangularStability
public import Zalcman.PrimitiveWeight
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite coefficient stability under changes of a driving moment

For a backward triangular system, the difference of two coefficient paths
splits between a term controlled by lower coefficient errors and forcing
integrals controlled separately by the primitive of the moment difference.
-/
public section

namespace Zalcman

open Finset Filter MeasureTheory Set
open scoped NNReal

/-- The backward stability estimate restricted to a finite prefix. -/
theorem triangular_error_le_of_integral_inequality_prefix {M : ℕ} {d : ℕ → ℝ → ℝ}
    {T C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hd : ∀ j t, 0 ≤ d j t)
    (hInt : ∀ j ≤ M, ∀ t, 0 ≤ t → t ≤ T → IntervalIntegrable (d j) volume t T)
    (h : ∀ n ≤ M, ∀ t, 0 ≤ t → t ≤ T →
      d n t ≤ ε + C * ∑ j ∈ range n, ∫ u in t..T, d j u)
    {n : ℕ} (hn : n ≤ M) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    d n t ≤ ε * (1 + C * T) ^ n := by
  let D (j : ℕ) (u : ℝ) : ℝ := if j ≤ M then d j u else 0
  have hDInt (j : ℕ) (u : ℝ) (hu : 0 ≤ u) (huT : u ≤ T) :
      IntervalIntegrable (D j) volume u T := by
    by_cases hj : j ≤ M
    · simpa only [D, ite_eq_left hj] using hInt j hj u hu huT
    · simpa only [D, ite_eq_right hj] using (intervalIntegrable_const (c := (0 : ℝ)))
  have hD (k : ℕ) (u : ℝ) (hu : 0 ≤ u) (huT : u ≤ T) :
      D k u ≤ ε + C * ∑ j ∈ range k, ∫ v in u..T, D j v := by
    by_cases hk : k ≤ M
    · have hsum : (∑ j ∈ range k, ∫ v in u..T, D j v) =
          ∑ j ∈ range k, ∫ v in u..T, d j v := by
        apply sum_congr rfl
        intro j hj
        have hle := (Nat.le_of_lt (mem_range.mp hj)).trans hk
        simp only [D, ite_eq_left hle]
      rw [hsum]
      simpa only [D, ite_eq_left hk] using h k hk u hu huT
    · simp only [D, ite_eq_right hk]
      apply add_nonneg hε (mul_nonneg hC (sum_nonneg fun j _ ↦ ?_))
      exact intervalIntegral.integral_nonneg_of_forall huT fun v ↦ by
        by_cases hj : j ≤ M
        · simpa only [D, ite_eq_left hj] using hd j v
        · simp only [ite_eq_right hj, le_refl]
  simpa only [D, ite_eq_left hn] using triangular_error_le_of_integral_inequality hC hε hDInt hD n t ht htT

/-- Separate a triangular system's integrated moment forcing from its lower-degree
coefficient errors, then propagate both through a finite prefix. -/
theorem norm_coefficient_error_le_of_integrated_moment_forcing {M : ℕ}
    {A B p q : ℕ → ℝ → ℂ} {W : ℕ → ℕ → ℝ → ℝ → ℂ} {E : ℕ → ℝ → ℂ}
    {T C δ η : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hE : ∀ n ≤ M, ∀ t ∈ Set.Icc (0 : ℝ) T, ‖E n t‖ ≤ δ)
    (hW : ∀ n ≤ M, ∀ j < n, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ u ∈ Set.Icc t T, ‖W n j t u‖ ≤ C)
    (hq : ∀ i, ∀ᵐ u ∂volume, u ∈ Set.Ioc (0 : ℝ) T → ‖q i u‖ ≤ 1)
    (hDiff : ∀ j ≤ M, ∀ t ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable (fun u ↦ ‖A j u - B j u‖) volume t T)
    (hTrans : ∀ n ≤ M, ∀ j < n, ∀ t ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable (fun u ↦ W n j t u * ((A j u - B j u) * q (n - 1 - j) u)) volume t T)
    (hForceI : ∀ n ≤ M, ∀ j < n, ∀ t ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable (fun u ↦ W n j t u * (A j u * (p (n - 1 - j) u - q (n - 1 - j) u)))
        volume t T)
    (hForce : ∀ n ≤ M, ∀ j < n, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖∫ u in t..T, W n j t u * (A j u * (p (n - 1 - j) u - q (n - 1 - j) u))‖ ≤ η)
    (hRec : ∀ n ≤ M, ∀ t ∈ Set.Icc (0 : ℝ) T, A n t - B n t = E n t +
      ∑ j ∈ range n, ∫ u in t..T, W n j t u * (A j u * p (n - 1 - j) u - B j u * q (n - 1 - j) u))
    {n : ℕ} (hn : n ≤ M) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖A n t - B n t‖ ≤ (δ + (M : ℝ) * η) * (1 + C * T) ^ n := by
  have hδε : 0 ≤ δ + (M : ℝ) * η := by positivity
  apply triangular_error_le_of_integral_inequality_prefix hC hδε
    (d := fun j u ↦ ‖A j u - B j u‖) (fun _ _ ↦ norm_nonneg _) (fun j hj u hu huT ↦ hDiff j hj u ⟨hu, huT⟩)
    ?_ hn ht.1 ht.2
  intro k hk u hu huT
  have hut : u ∈ Set.Icc (0 : ℝ) T := ⟨hu, huT⟩
  let I (j : ℕ) (v : ℝ) : ℂ := W k j u v * (A j v * p (k - 1 - j) v - B j v * q (k - 1 - j) v)
  have hSingle (j : ℕ) (hj : j ∈ range k) :
      ‖∫ v in u..T, I j v‖ ≤ C * (∫ v in u..T, ‖A j v - B j v‖) + η := by
    have hjk := mem_range.mp hj
    let V (v : ℝ) : ℂ := W k j u v * ((A j v - B j v) * q (k - 1 - j) v)
    let G (v : ℝ) : ℂ := W k j u v * (A j v * (p (k - 1 - j) v - q (k - 1 - j) v))
    have heq : I j = fun v ↦ V v + G v := by
      funext v
      dsimp only [I, V, G]
      ring
    have hV : ‖∫ v in u..T, V v‖ ≤ C * (∫ v in u..T, ‖A j v - B j v‖) := by
      have hI := (hDiff j ((Nat.le_of_lt hjk).trans hk) u hut).const_mul C
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.norm_integral_le_of_norm_le huT ?_ hI
      filter_upwards [hq (k - 1 - j)] with v hvq hv
      have hvW := hW k hk j hjk u hut v ⟨hv.1.le, hv.2⟩
      have hvq' := hvq ⟨hu.trans_lt hv.1, hv.2⟩
      calc
        ‖V v‖ = ‖W k j u v‖ * (‖A j v - B j v‖ * ‖q (k - 1 - j) v‖) := by simp only [V, norm_mul]
        _ ≤ C * (‖A j v - B j v‖ * 1) :=
          mul_le_mul hvW (mul_le_mul_of_nonneg_left hvq' (norm_nonneg _)) (by positivity) hC
        _ = C * ‖A j v - B j v‖ := by rw [mul_one]
    rw [heq, intervalIntegral.integral_add (hTrans k hk j hjk u hut) (hForceI k hk j hjk u hut)]
    exact (norm_add_le _ _).trans (add_le_add hV (hForce k hk j hjk u hut))
  change ‖A k u - B k u‖ ≤ _
  rw [hRec k hk u hut]
  calc
    _ ≤ δ + ∑ j ∈ range k, (C * (∫ v in u..T, ‖A j v - B j v‖) + η) :=
      (norm_add_le _ _).trans (add_le_add (hE k hk u hut) <|
        (norm_sum_le _ _).trans (sum_le_sum fun j hj ↦ hSingle j hj))
    _ = δ + (C * ∑ j ∈ range k, ∫ v in u..T, ‖A j v - B j v‖) + (k : ℝ) * η := by
      rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul, add_assoc]
    _ ≤ _ := by
      rw [add_right_comm]
      exact add_le_add (add_le_add (le_refl δ) (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hη)) (le_refl _)

private noncomputable def momentCorrection (A p : ℕ → ℝ → ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  2 * ∑ j ∈ range n, ((j : ℂ) + 1) * A j u * p (n - 1 - j) u

private noncomputable def momentKernel (n j : ℕ) (t u : ℝ) : ℂ :=
  (-(2 * ((j : ℂ) + 1))) * backwardExpWeight n t u

private theorem continuous_momentKernel (n j : ℕ) (t : ℝ) : Continuous (momentKernel n j t) :=
  continuous_const.mul (contDiff_backwardExpWeight n t).continuous

private theorem intervalIntegrable_moment_of_norm_le_one {T : ℝ} (hT : 0 ≤ T) {p : ℝ → ℂ}
    (hp : Measurable p) (hBound : ∀ᵐ u ∂volume.restrict (Set.Ioc 0 T), ‖p u‖ ≤ 1) :
    IntervalIntegrable p volume 0 T := by
  have hμ : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc 0 T)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  letI := hμ
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
    (Integrable.of_bound hp.aestronglyMeasurable 1 hBound)

private theorem intervalIntegrable_momentCorrection {A p : ℕ → ℝ → ℂ} {t T : ℝ}
    (hAC : ∀ n, AbsolutelyContinuousOnInterval (A n) t T)
    (hI : ∀ n, IntervalIntegrable (p n) volume t T) (n : ℕ) :
    IntervalIntegrable (momentCorrection A p n) volume t T := by
  have hSum := IntervalIntegrable.sum (range n)
    (f := fun j u ↦ ((j : ℂ) + 1) * A j u * p (n - 1 - j) u) (fun j _ ↦
      (hI (n - 1 - j)).continuousOn_mul (continuousOn_const.mul (hAC j).continuousOn))
  change IntervalIntegrable (fun u ↦ (2 : ℂ) * ∑ j ∈ range n,
    ((j : ℂ) + 1) * A j u * p (n - 1 - j) u) volume t T
  simpa only [Finset.sum_apply] using hSum.const_mul (2 : ℂ)

private theorem eq_terminal_add_moment_integrals {A p : ℕ → ℝ → ℂ} {t T : ℝ}
    (hA : ∀ n, AbsolutelyContinuousOnInterval (A n) t T)
    (hI : ∀ n, IntervalIntegrable (p n) volume t T)
    (hD : ∀ᵐ u ∂volume, u ∈ uIoc t T → ∀ n,
      HasDerivAt (A n) ((n : ℂ) * A n u + momentCorrection A p n u) u) (n : ℕ) :
    A n t = backwardExpWeight n t T * A n T +
      ∑ j ∈ range n, ∫ u in t..T, momentKernel n j t u * (A j u * p (n - 1 - j) u) := by
  have hV := eq_terminal_mul_sub_integral_of_hasDerivAt (q := (n : ℝ)) (hA n)
    (intervalIntegrable_momentCorrection hA hI n) (hD.mono fun _ h hu ↦ by
      simpa only [Complex.ofReal_natCast] using h hu n)
  have hIterm (j : ℕ) : IntervalIntegrable
      (fun u ↦ momentKernel n j t u * (A j u * p (n - 1 - j) u)) volume t T :=
    ((hI (n - 1 - j)).continuousOn_mul (hA j).continuousOn).continuousOn_mul
      (continuous_momentKernel n j t).continuousOn
  have hEq : (fun u ↦ backwardExpWeight n t u * momentCorrection A p n u) =
      fun u ↦ -(∑ j ∈ range n, momentKernel n j t u * (A j u * p (n - 1 - j) u)) := by
    funext u
    rw [momentCorrection, ← mul_assoc, mul_sum, ← sum_neg_distrib]
    exact sum_congr rfl (fun j _ ↦ by unfold momentKernel; ring)
  rw [hEq, intervalIntegral.integral_neg,
    intervalIntegral.integral_finsetSum (fun j _ ↦ hIterm j), sub_neg_eq_add] at hV
  exact hV

set_option maxHeartbeats 1000000 in
/-- Stability of the normalized triangular coefficient system under a change of
measurable moments, with the same terminal coefficients. The constant depends
on the reference coefficient paths and the fixed time and degree bounds. -/
theorem exists_coefficient_stability_constant (M : ℕ) {T : ℝ} (hT : 0 ≤ T)
    {A p : ℕ → ℝ → ℂ} (hA : ∀ n, AbsolutelyContinuousOnInterval (A n) 0 T)
    (hPm : ∀ n, Measurable (p n))
    (hP : ∀ n, ∀ᵐ u ∂volume.restrict (Set.Ioc 0 T), ‖p n u‖ ≤ 1)
    (hAD : ∀ᵐ u : ℝ ∂volume, u ∈ Set.Ioo 0 T → ∀ n,
      HasDerivAt (A n) ((n : ℂ) * A n u + 2 * ∑ j ∈ range n,
        ((j : ℂ) + 1) * A j u * p (n - 1 - j) u) u) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {B q : ℕ → ℝ → ℂ} {ε : ℝ}, 0 ≤ ε →
      (∀ n, AbsolutelyContinuousOnInterval (B n) 0 T) →
      (∀ n, Measurable (q n)) →
      (∀ n, ∀ᵐ u ∂volume.restrict (Set.Ioc 0 T), ‖q n u‖ ≤ 1) →
      (∀ᵐ u : ℝ ∂volume, u ∈ Set.Ioo 0 T → ∀ n,
        HasDerivAt (B n) ((n : ℂ) * B n u + 2 * ∑ j ∈ range n,
          ((j : ℂ) + 1) * B j u * q (n - 1 - j) u) u) →
      (∀ n ≤ M, A n T = B n T) →
      (∀ k < M, ∀ u ∈ Set.Icc (0 : ℝ) T, ‖∫ s in 0..u, p k s - q k s‖ ≤ ε) →
      ∀ n ≤ M, ‖A n 0 - B n 0‖ ≤ C * ε := by
  classical
  have hpI (n : ℕ) := intervalIntegrable_moment_of_norm_le_one hT (hPm n) (hP n)
  have hAD' : ∀ᵐ u ∂volume.restrict (Set.Ioc 0 T), ∀ n,
      HasDerivAt (A n) ((n : ℂ) * A n u + momentCorrection A p n u) u := by
    rw [← restrict_Ioo_eq_restrict_Ioc, ae_restrict_iff' measurableSet_Ioo]
    exact hAD
  have hAIder (n : ℕ) : IntervalIntegrable (deriv (A n)) volume 0 T := by
    have hI := ((hA n).continuousOn.intervalIntegrable.const_mul (n : ℂ)).add
      (intervalIntegrable_momentCorrection hA hpI n)
    apply hI.congr_ae
    rw [uIoc_of_le hT]
    exact hAD'.mono fun _ hu ↦ (hu n).deriv.symm
  choose r hr using fun n ↦ (hA n).exists_bound
  have hr₀ (n : ℕ) : 0 ≤ r n := (norm_nonneg _).trans (hr n 0 left_mem_uIcc)
  let R := 1 + ∑ n ∈ range (M + 1), r n
  let D := ∑ n ∈ range (M + 1), ∫ u in 0..T, ‖deriv (A n) u‖
  let K := 2 * ((M : ℝ) + 1)
  let S := R + D + (M : ℝ) * R * T
  have hR : 0 < R := by dsimp only [R]; exact add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg fun n _ ↦ hr₀ n)
  have hD₀ (n : ℕ) : 0 ≤ ∫ u in 0..T, ‖deriv (A n) u‖ :=
    intervalIntegral.integral_nonneg_of_forall hT fun _ ↦ norm_nonneg _
  have hD : 0 ≤ D := sum_nonneg fun n _ ↦ hD₀ n
  have hK : 0 < K := by dsimp only [K]; positivity
  have hS : 0 < S := by dsimp only [S]; positivity
  have hRb (n : ℕ) (hn : n ≤ M) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) T) : ‖A n u‖ ≤ R := by
    have hn' : n ∈ range (M + 1) := mem_range.mpr (Nat.lt_succ_of_le hn)
    have hc : r n ≤ ∑ i ∈ range (M + 1), r i := single_le_sum (fun i _ ↦ hr₀ i) hn'
    have hu' : u ∈ uIcc 0 T := by simpa only [uIcc_of_le hT] using hu
    have hb := hr n u hu'
    dsimp only [R]
    linarith
  have hDle (n : ℕ) (hn : n ≤ M) : (∫ u in 0..T, ‖deriv (A n) u‖) ≤ D :=
    single_le_sum (fun i _ ↦ hD₀ i) (mem_range.mpr (Nat.lt_succ_of_le hn))
  let C := ((M : ℝ) + 1) * (2 * K * S) * (1 + K * T) ^ M
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro B q ε hε hB hQm hQ hBD hTerminal hPrim n hn
  have hqI (i : ℕ) := intervalIntegrable_moment_of_norm_le_one hT (hQm i) (hQ i)
  have hBD' : ∀ᵐ u ∂volume.restrict (Set.Ioc 0 T), ∀ k,
      HasDerivAt (B k) ((k : ℂ) * B k u + momentCorrection B q k u) u := by
    rw [← restrict_Ioo_eq_restrict_Ioc, ae_restrict_iff' measurableSet_Ioo]
    exact hBD
  have hsub (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) : uIcc t T ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht.2, uIcc_of_le hT]
    exact Icc_subset_Icc_left ht.1
  have hSmallInterval (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) : uIoc t T ⊆ Set.Ioc 0 T := by
    rw [uIoc_of_le ht.2]
    exact Ioc_subset_Ioc_left ht.1
  have hAvar (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :=
    eq_terminal_add_moment_integrals (fun j ↦ (hA j).mono (hsub t ht))
      (fun j ↦ (hpI j).mono_set (hsub t ht))
      ((ae_restrict_iff' measurableSet_uIoc).mp (ae_mono
        (Measure.restrict_mono_set _ (hSmallInterval t ht)) hAD')) k
  have hBvar (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :=
    eq_terminal_add_moment_integrals (fun j ↦ (hB j).mono (hsub t ht))
      (fun j ↦ (hqI j).mono_set (hsub t ht))
      ((ae_restrict_iff' measurableSet_uIoc).mp (ae_mono
        (Measure.restrict_mono_set _ (hSmallInterval t ht)) hBD')) k
  have hScale (j : ℕ) (hj : j ≤ M) : ‖-(2 * ((j : ℂ) + 1))‖ ≤ K := by
    rw [norm_neg, norm_mul, Complex.norm_two]
    change (2 : ℝ) * ‖(j : ℂ) + 1‖ ≤ 2 * ((M : ℝ) + 1)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc
      _ ≤ ‖(j : ℂ)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = (j : ℝ) + 1 := by rw [Complex.norm_natCast, norm_one]
      _ ≤ _ := add_le_add (Nat.cast_le.mpr hj) (le_refl (1 : ℝ))
  have hW (k j : ℕ) (hj : j ≤ M) (t u : ℝ) (htu : t ≤ u) : ‖momentKernel k j t u‖ ≤ K := by
    rw [momentKernel, norm_mul]
    exact (mul_le_mul_of_nonneg_left (norm_backwardExpWeight_le_one (Nat.cast_nonneg k) htu)
      (norm_nonneg _)).trans (by simpa only [mul_one] using hScale j hj)
  have hDiff (j : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      IntervalIntegrable (fun u ↦ ‖A j u - B j u‖) volume t T :=
    (((hA j).continuousOn.sub (hB j).continuousOn).mono (hsub t ht)).norm.intervalIntegrable
  have hTrans (k j : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      IntervalIntegrable (fun u ↦ momentKernel k j t u * ((A j u - B j u) * q (k - 1 - j) u))
        volume t T :=
    (((hqI (k - 1 - j)).mono_set (hsub t ht)).continuousOn_mul
      (((hA j).continuousOn.sub (hB j).continuousOn).mono (hsub t ht))).continuousOn_mul
      (continuous_momentKernel k j t).continuousOn
  have hForceI (k j : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      IntervalIntegrable (fun u ↦ momentKernel k j t u * (A j u * (p (k - 1 - j) u - q (k - 1 - j) u)))
        volume t T :=
    ((((hpI (k - 1 - j)).sub (hqI (k - 1 - j))).mono_set (hsub t ht)).continuousOn_mul
      ((hA j).continuousOn.mono (hsub t ht))).continuousOn_mul (continuous_momentKernel k j t).continuousOn
  let η := (2 * ε) * (K * S)
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hForce (k : ℕ) (hk : k ≤ M) (j : ℕ) (hj : j < k) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      ‖∫ u in t..T, momentKernel k j t u * (A j u * (p (k - 1 - j) u - q (k - 1 - j) u))‖ ≤ η := by
    let i := k - 1 - j
    let g (u : ℝ) := p i u - q i u
    have hi : i < M := by dsimp only [i]; omega
    have hjM := (Nat.le_of_lt hj).trans hk
    have hgB : ∀ᵐ u ∂volume.restrict (Set.Ioc 0 T), ‖g u‖ ≤ ((2 : ℝ≥0) : ℝ) := by
      filter_upwards [hP i, hQ i] with u hpu hqu
      exact (norm_sub_le _ _).trans (by norm_num; linarith)
    have hADer : ∀ᵐ u ∂volume, u ∈ uIoc 0 T → HasDerivAt (A j) (deriv (A j) u) u := by
      apply (ae_restrict_iff' measurableSet_uIoc).mp
      rw [uIoc_of_le hT]
      exact hAD'.mono fun _ hu ↦ (hu j).differentiableAt.hasDerivAt
    have hF := norm_exponential_weighted_forcing_le ht.1 ht.2 (Nat.cast_nonneg k) hε
      ((hpI i).sub (hqI i)) hgB (hPrim i hi) (hA j) (hAIder j) hADer (hRb j hjM)
    have hSle : R + (∫ u in 0..T, ‖deriv (A j) u‖) + (k : ℝ) * R * T ≤ S := by
      dsimp only [S]
      have hk' : (k : ℝ) ≤ M := Nat.cast_le.mpr hk
      exact add_le_add (add_le_add (le_refl R) (hDle j hjM)) <|
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk' hR.le) hT
    have hIntegral := hF.trans (mul_le_mul_of_nonneg_left hSle (by positivity : 0 ≤ 2 * ε))
    have hPull : (∫ u in t..T, momentKernel k j t u * (A j u * g u)) =
        (-(2 * ((j : ℂ) + 1))) * (∫ u in t..T, backwardExpWeight k t u * A j u * g u) := by
      simp_rw [momentKernel, mul_assoc]
      rw [intervalIntegral.integral_const_mul]
    change ‖∫ u in t..T, momentKernel k j t u * (A j u * g u)‖ ≤ η
    rw [hPull, norm_mul]
    calc
      _ ≤ K * ((2 * ε) * S) := mul_le_mul (hScale j hjM) hIntegral (norm_nonneg _) hK.le
      _ = η := by dsimp only [η]; ring
  have hRec (k : ℕ) (hk : k ≤ M) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) : A k t - B k t = (0 : ℂ) +
      ∑ j ∈ range k, ∫ u in t..T, momentKernel k j t u * (A j u * p (k - 1 - j) u - B j u * q (k - 1 - j) u) := by
    have hterm (j : ℕ) (d : ℕ → ℝ → ℂ) {f : ℕ → ℝ → ℂ}
        (hd : ∀ i, IntervalIntegrable (d i) volume 0 T)
        (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) 0 T) :
        IntervalIntegrable (fun u ↦ momentKernel k j t u * (f j u * d (k - 1 - j) u)) volume t T :=
      (((hd (k - 1 - j)).mono_set (hsub t ht)).continuousOn_mul
        ((hf j).continuousOn.mono (hsub t ht))).continuousOn_mul (continuous_momentKernel k j t).continuousOn
    rw [hAvar k t ht, hBvar k t ht, hTerminal k hk, zero_add]
    rw [add_sub_add_left_eq_sub, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    rw [← intervalIntegral.integral_sub (hterm j p hpI hA) (hterm j q hqI hB)]
    simp only [mul_sub]
  have hQB (j : ℕ) : ∀ᵐ u ∂volume, u ∈ Set.Ioc (0 : ℝ) T → ‖q j u‖ ≤ 1 :=
    (ae_restrict_iff' measurableSet_Ioc).mp (hQ j)
  have hStab := norm_coefficient_error_le_of_integrated_moment_forcing (W := momentKernel)
    (E := fun _ _ ↦ 0) hK.le (le_refl (0 : ℝ)) hη (fun _ _ _ _ ↦ by simp)
    (fun k hk j hj t _ u hu ↦ hW k j ((Nat.le_of_lt hj).trans hk) t u hu.1)
    hQB (fun j _ t ht ↦ hDiff j t ht) (fun k _ j _ t ht ↦ hTrans k j t ht)
    (fun k _ j _ t ht ↦ hForceI k j t ht) hForce hRec hn (show (0 : ℝ) ∈ Set.Icc 0 T from ⟨le_rfl, hT⟩)
  have hPow : (1 + K * T) ^ n ≤ (1 + K * T) ^ M :=
    pow_le_pow_right₀ (by linarith only [mul_nonneg hK.le hT]) hn
  calc
    _ ≤ (0 + (M : ℝ) * η) * (1 + K * T) ^ n := hStab
    _ ≤ ((M : ℝ) + 1) * η * (1 + K * T) ^ M := by
      rw [zero_add]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hη) hPow (by positivity) (by positivity)
    _ = C * ε := by dsimp only [C, η]; ring

end Zalcman
