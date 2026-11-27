/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.UnitMomentHull
public import Zalcman.PiecewiseUnitControl
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Approximation of moments by finite unit controls

On a short time interval the average moment vector can be approximated by a
finite mixture of unit-point vectors. Giving each point its proportion of
the interval controls the integral error. A uniform mesh controls the error
at each intermediate time.
-/

public section

namespace Zalcman

open Filter MeasureTheory Set
open scoped BigOperators

theorem intervalIntegrable_of_measurable_bounded_moments {M : ℕ}
    {a b : ℝ} (hab : a ≤ b) {m : ℝ → Fin M → ℂ} (hm : Measurable m)
    (hBound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖m t‖ ≤ 1) : IntervalIntegrable m volume a b := by
  have hμ : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc a b)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  letI := hμ
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    (Integrable.of_bound hm.aestronglyMeasurable 1 hBound)

theorem intervalIntegrable_unitMoments {M : ℕ} {a b : ℝ} (hab : a ≤ b)
    {q : ℝ → ℂ} (hq : Measurable q) (hUnit : ∀ t, ‖q t‖ = 1) :
    IntervalIntegrable (fun t ↦ unitMomentCurve M (q t)) volume a b :=
  intervalIntegrable_of_measurable_bounded_moments hab ((continuous_unitMomentCurve M).measurable.comp hq)
    (.of_forall fun t ↦ norm_le_one_of_mem_closedUnitMomentHull (unitMomentCurve_mem_closedUnitMomentHull M (hUnit t)))

private theorem exists_cell_unit_control {M : ℕ} {a b η : ℝ} (hab : a < b) (hη : 0 < η)
    {m : ℝ → Fin M → ℂ} (hmI : IntervalIntegrable m volume a b)
    (hm : ∀ᵐ t ∂volume.restrict (Ioc a b), m t ∈ closedUnitMomentHull M) :
    ∃ (p : ℕ) (A : ℕ → ℝ) (ζ : ℕ → ℂ), Monotone A ∧ A 0 = a ∧ A p = b ∧
      (∀ j ∈ Finset.range p, ‖ζ j‖ = 1) ∧
      ‖∫ t in a..b, (unitMomentCurve M (intervalControl p A ζ t) - m t)‖ ≤ η * (b - a) := by
  let avg := (b - a)⁻¹ • (∫ t in a..b, m t)
  have havg : avg ∈ closedUnitMomentHull M := intervalAverage_mem_closedUnitMomentHull hab hmI hm
  obtain ⟨p, w, ζ, hw, hsum, hζ, hclose⟩ := exists_range_unit_moment_mixture_close havg hη
  obtain ⟨A, hA, hA₀, hAp, hInt⟩ := exists_intervalControl_of_weights (E := Fin M → ℂ) hab.le hw hsum ζ
  have hU := intervalIntegrable_unitMoments (M := M) hab.le (measurable_intervalControl p A ζ)
    (norm_intervalControl_eq_one hA hζ)
  have hmScale : (∫ t in a..b, m t) = (b - a) • avg := by
    dsimp only [avg]
    rw [smul_smul, mul_inv_cancel₀ (sub_pos.mpr hab).ne', one_smul]
  have hnorm : ‖(∑ j ∈ Finset.range p, w j • unitMomentCurve M (ζ j)) - avg‖ ≤ η := by
    simpa only [dist_eq_norm, norm_sub_rev] using hclose.le
  refine ⟨p, A, ζ, hA, hA₀, hAp, hζ, ?_⟩
  rw [intervalIntegral.integral_sub hU hmI, hInt (unitMomentCurve M), hmScale, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab.le)]
  exact (mul_le_mul_of_nonneg_left hnorm (sub_nonneg.mpr hab.le)).trans_eq (mul_comm _ _)

/-- A measurable moment vector in the closed unit-moment hull is approximated
uniformly at the level of its primitive by a finite piecewise constant unit
control. The data include the outer mesh and the constant pieces of each cell. -/
theorem exists_piecewise_unit_primitive_approximation {M : ℕ} {a b ε : ℝ}
    (hab : a < b) (hε : 0 < ε) {m : ℝ → Fin M → ℂ} (hmeas : Measurable m)
    (hHull : ∀ᵐ t ∂volume.restrict (Ioc a b), m t ∈ closedUnitMomentHull M) :
    ∃ (N : ℕ) (A : ℕ → ℝ) (q : ℕ → ℝ → ℂ), Monotone A ∧ A 0 = a ∧ A N = b ∧
      (∀ i < N, ∃ (p : ℕ) (S : ℕ → ℝ) (ζ : ℕ → ℂ), Monotone S ∧ S 0 = A i ∧
        S p = A (i + 1) ∧ (∀ j ∈ Finset.range p, ‖ζ j‖ = 1) ∧ q i = intervalControl p S ζ) ∧
      Measurable (glueIntervalControls N A q) ∧ (∀ t, ‖glueIntervalControls N A q t‖ = 1) ∧
      ∀ u ∈ Icc a b, ‖∫ t in a..u, (unitMomentCurve M (glueIntervalControls N A q t) - m t)‖ < ε := by
  let mesh := ε / 8
  let η := ε / (2 * (b - a))
  have hLen : 0 < b - a := sub_pos.mpr hab
  have hmesh : 0 < mesh := div_pos hε (by norm_num)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / mesh)
  have hN₀ : 0 < (N : ℝ) := (div_pos hLen hmesh).trans hN
  have hNmesh : (b - a) / (N : ℝ) ≤ mesh := by
    apply (div_le_iff₀ hN₀).mpr
    simpa only [mul_comm] using ((div_lt_iff₀ hmesh).mp hN).le
  let A := fun i : ℕ ↦ a + (b - a) * ((i : ℝ) / (N : ℝ))
  have hA : Monotone A := by
    intro i j hij
    have hquot := div_le_div_of_nonneg_right (Nat.cast_le.mpr hij : (i : ℝ) ≤ (j : ℝ)) hN₀.le
    exact add_le_add_right (mul_le_mul_of_nonneg_left hquot hLen.le) a
  have hA₀ : A 0 = a := by simp [A]
  have hAN : A N = b := by
    dsimp only [A]
    rw [div_self hN₀.ne', mul_one]
    ring
  have hAdiff (i : ℕ) : A (i + 1) - A i = (b - a) / (N : ℝ) := by
    simp only [A, Nat.cast_add, Nat.cast_one]
    ring
  have hAstep (i : ℕ) : A i < A (i + 1) := sub_pos.mp (by rw [hAdiff]; exact div_pos hLen hN₀)
  have hmB : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖m t‖ ≤ 1 :=
    hHull.mono fun _ ↦ norm_le_one_of_mem_closedUnitMomentHull
  have hmI := intervalIntegrable_of_measurable_bounded_moments hab.le hmeas hmB
  have hPieceSub {i : ℕ} (hi : i < N) : Ioc (A i) (A (i + 1)) ⊆ Ioc a b := by
    have h0i : a ≤ A i := hA₀ ▸ hA (Nat.zero_le i)
    have hiN : A (i + 1) ≤ b := hAN ▸ hA (Nat.succ_le_of_lt hi)
    exact fun _ ht ↦ ⟨h0i.trans_lt ht.1, ht.2.trans hiN⟩
  have hex (i : Fin N) := exists_cell_unit_control (hAstep i.val) hη
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (hAstep i.val).le).mpr
      (hmI.1.mono_set (hPieceSub i.isLt)))
    (ae_mono (Measure.restrict_mono_set volume (hPieceSub i.isLt)) hHull)
  choose p S ζ hS hS₀ hSp hζ hApprox using hex
  let q (i : ℕ) : ℝ → ℂ := if hi : i < N then intervalControl (p ⟨i, hi⟩) (S ⟨i, hi⟩) (ζ ⟨i, hi⟩) else 1
  have hq (i : ℕ) (hi : i < N) : q i = intervalControl (p ⟨i, hi⟩) (S ⟨i, hi⟩) (ζ ⟨i, hi⟩) := by
    simp only [q, dite_eq_left hi]
  have hMeas : Measurable (glueIntervalControls N A q) := measurable_glueIntervalControls A fun i hi ↦ by
    rw [hq i (Finset.mem_range.mp hi)]
    exact measurable_intervalControl _ _ _
  have hUnit : ∀ t, ‖glueIntervalControls N A q t‖ = 1 :=
    norm_glueIntervalControls_eq_one hA fun i hi t ↦ by
      rw [hq i (Finset.mem_range.mp hi)]
      exact norm_intervalControl_eq_one (hS _) (hζ _) t
  refine ⟨N, A, q, hA, hA₀, hAN, ?_, hMeas, hUnit, ?_⟩
  · intro i hi
    refine ⟨p ⟨i, hi⟩, S ⟨i, hi⟩, ζ ⟨i, hi⟩, hS _, hS₀ _, hSp _, hζ _, hq i hi⟩
  · intro u hu
    let e := fun t ↦ unitMomentCurve M (glueIntervalControls N A q t) - m t
    have hInt : IntervalIntegrable e volume a b :=
      (intervalIntegrable_unitMoments hab.le hMeas hUnit).sub hmI
    have hBound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖e t‖ ≤ 2 := hmB.mono fun t ht ↦ by
      refine (norm_sub_le _ _).trans ?_
      have hQ := norm_le_one_of_mem_closedUnitMomentHull (unitMomentCurve_mem_closedUnitMomentHull M (hUnit t))
      linarith only [hQ, ht]
    have hFull (i : ℕ) (hi : i < N) : ‖∫ t in A i..A (i + 1), e t‖ ≤ η * (A (i + 1) - A i) := by
      have hEqual : EqOn e (fun t ↦ unitMomentCurve M (q i t) - m t) (Ioc (A i) (A (i + 1))) := by
        intro t ht
        change unitMomentCurve M (glueIntervalControls N A q t) - m t = unitMomentCurve M (q i t) - m t
        rw [glueIntervalControls_eq_on_piece hA (Finset.mem_range.mpr hi) ht]
      rw [intervalIntegral.integral_of_le (hAstep i).le, setIntegral_congr_fun measurableSet_Ioc hEqual,
        ← intervalIntegral.integral_of_le (hAstep i).le, hq i hi]
      exact hApprox ⟨i, hi⟩
    have hPrim := norm_primitive_le_of_interval_partition (n := N) (f := e) (t := u)
      hA (by norm_num : 0 ≤ (2 : ℝ)) hη.le hmesh.le
      (by simpa only [hA₀, hAN] using hInt) (by simpa only [hA₀, hAN] using hBound)
      (fun i _ ↦ by rw [hAdiff]; exact hNmesh) hFull (by simpa only [hA₀, hAN] using hu)
    have hηLen : η * (b - a) = ε / 2 := by
      dsimp only [η]
      field_simp [hLen.ne']
    have hSmall : η * (b - a) + 2 * mesh < ε := by
      rw [hηLen]
      dsimp only [mesh]
      linarith
    exact (by simpa only [hA₀, hAN] using hPrim : ‖∫ t in a..u, e t‖ ≤ η * (b - a) + 2 * mesh).trans_lt hSmall

/-- Componentwise primitive bounds follow from the uniform vector bound. -/
theorem norm_moment_coordinate_intervalIntegral_le {M : ℕ} {a b : ℝ} {m : ℝ → Fin M → ℂ}
    (hm : IntervalIntegrable m volume a b) (k : Fin M) :
    ‖∫ t in a..b, m t k‖ ≤ ‖∫ t in a..b, m t‖ := by
  let L : (Fin M → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj k
  change ‖∫ t in a..b, L (m t)‖ ≤ _
  rw [L.intervalIntegral_comp_comm hm]
  simpa only [L, ContinuousLinearMap.proj_apply] using
    norm_le_pi_norm ((∫ t in a..b, m t) : Fin M → ℂ) k

end Zalcman
