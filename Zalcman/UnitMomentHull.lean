/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex

/-!
# The closed convex hull of unit-circle moments

The norm bound and finite mixtures in this hull control the time averages
used for piecewise constant approximations.
-/

@[expose] public section

namespace Zalcman

open Complex Filter MeasureTheory Real Set
open scoped ENNReal Real Topology

/-- The first `M` powers of a point on the unit circle, starting with power one. -/
noncomputable def unitMomentCurve (M : ℕ) (z : ℂ) (k : Fin M) : ℂ := z ^ (k.val + 1)

/-- The closed convex hull of the finite unit-circle moment vectors. -/
noncomputable def closedUnitMomentHull (M : ℕ) : Set (Fin M → ℂ) :=
  closure (convexHull ℝ (unitMomentCurve M '' Metric.sphere 0 1))

theorem continuous_unitMomentCurve (M : ℕ) : Continuous (unitMomentCurve M) :=
  continuous_pi fun _ ↦ continuous_id.pow _

theorem unitMomentCurve_mem_closedUnitMomentHull (M : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    unitMomentCurve M z ∈ closedUnitMomentHull M := by
  apply subset_closure (subset_convexHull ℝ _ ?_)
  exact ⟨z, by simpa only [Metric.mem_sphere, dist_zero_right] using hz, rfl⟩

/-- The moment norm stays at most one under mixing and passage to limits. -/
theorem norm_le_one_of_mem_closedUnitMomentHull {M : ℕ} {m : Fin M → ℂ}
    (hm : m ∈ closedUnitMomentHull M) : ‖m‖ ≤ 1 := by
  have hset : unitMomentCurve M '' Metric.sphere 0 1 ⊆ Metric.closedBall (0 : Fin M → ℂ) 1 := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    have hz' : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    intro k
    simp only [unitMomentCurve, norm_pow, hz', one_pow, le_refl]
  have hclosure := closure_minimal (convexHull_min hset (convex_closedBall (0 : Fin M → ℂ) 1))
    Metric.isClosed_closedBall
  simpa only [Metric.mem_closedBall, dist_zero_right] using hclosure hm

/-- A closed-hull moment vector can be approximated by a finite unit-point mixture. -/
theorem exists_unit_moment_mixture_close {M : ℕ} {m : Fin M → ℂ}
    (hm : m ∈ closedUnitMomentHull M) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (ζ : ι → ℂ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, ‖ζ i‖ = 1) ∧
        dist m (∑ i, w i • unitMomentCurve M (ζ i)) < ε := by
  obtain ⟨v, hv, hvε⟩ := Metric.mem_closure_iff.mp hm ε hε
  obtain ⟨ι, _, w, z, hw, hsum, hz, hvz⟩ := mem_convexHull_iff_exists_fintype.mp hv
  choose ζ hζ heq using hz
  refine ⟨ι, inferInstance, w, ζ, hw, hsum, fun i ↦ ?_, ?_⟩
  · simpa only [Metric.mem_sphere, dist_zero_right] using hζ i
  · simpa only [heq, hvz] using hvε

/-- The finite mixture can be indexed by consecutive natural numbers. -/
theorem exists_range_unit_moment_mixture_close {M : ℕ} {m : Fin M → ℂ}
    (hm : m ∈ closedUnitMomentHull M) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (w : ℕ → ℝ) (ζ : ℕ → ℂ),
      (∀ i, 0 ≤ w i) ∧ (∑ i ∈ Finset.range n, w i) = 1 ∧
      (∀ i ∈ Finset.range n, ‖ζ i‖ = 1) ∧
        dist m (∑ i ∈ Finset.range n, w i • unitMomentCurve M (ζ i)) < ε := by
  obtain ⟨ι, _, w, ζ, hw, hsum, hζ, hdist⟩ := exists_unit_moment_mixture_close hm hε
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let W (k : ℕ) := if hk : k < n then w (e.symm ⟨k, hk⟩) else 0
  let Z (k : ℕ) := if hk : k < n then ζ (e.symm ⟨k, hk⟩) else 1
  have hW (k : Fin n) : W k = w (e.symm k) := by simp only [W, dite_eq_left k.isLt]
  have hZ (k : Fin n) : Z k = ζ (e.symm k) := by simp only [Z, dite_eq_left k.isLt]
  refine ⟨n, W, Z, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k < n
    · simpa only [W, dite_eq_left hk] using hw (e.symm ⟨k, hk⟩)
    · simp [W, hk]
  · rw [← Fin.sum_univ_eq_sum_range]
    simp only [hW]
    exact (Equiv.sum_comp e.symm w).trans hsum
  · intro k hk
    simpa only [Z, dite_eq_left (Finset.mem_range.mp hk)] using hζ (e.symm ⟨k, Finset.mem_range.mp hk⟩)
  · rw [← Fin.sum_univ_eq_sum_range]
    simp only [hW, hZ]
    have heSum : (∑ k : Fin n, w (e.symm k) • unitMomentCurve M (ζ (e.symm k))) =
        ∑ i : ι, w i • unitMomentCurve M (ζ i) :=
      Equiv.sum_comp e.symm (fun i ↦ w i • unitMomentCurve M (ζ i))
    rwa [heSum]

/-- Time averages stay in the closed moment hull. -/
theorem intervalAverage_mem_closedUnitMomentHull {M : ℕ} {a b : ℝ} (hab : a < b)
    {m : ℝ → Fin M → ℂ} (hi : IntervalIntegrable m volume a b)
    (hm : ∀ᵐ t ∂volume.restrict (Ioc a b), m t ∈ closedUnitMomentHull M) :
    (b - a)⁻¹ • (∫ t in a..b, m t) ∈ closedUnitMomentHull M := by
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hvol₀ : (volume : Measure ℝ) (Ioc a b) ≠ 0 := by
    rw [Real.volume_Ioc]
    exact (ENNReal.ofReal_pos.mpr hlen).ne'
  have hvol_top : (volume : Measure ℝ) (Ioc a b) ≠ ∞ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hconv : Convex ℝ (closedUnitMomentHull M) := (convex_convexHull ℝ _).closure
  have hv := hconv.set_average_mem isClosed_closure hvol₀ hvol_top hm hi.1
  rw [setAverage_eq, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal hlen.le] at hv
  simpa only [intervalIntegral.integral_of_le hab.le] using hv

end Zalcman
