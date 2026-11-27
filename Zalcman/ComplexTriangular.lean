/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.Ring

/-!
# Limits and measurability for triangular systems

A lower triangular transformation with a nonzero diagonal has a unique inverse.
The inverse is continuous coefficient by coefficient and preserves measurability.
-/

public section

namespace Zalcman

open Filter
open scoped BigOperators Topology

section Field

variable {𝕜 : Type*} [Field 𝕜]

/-- Solve the triangular system with matrix `B` and right-hand side `T`. -/
noncomputable def complexTriangularSolution (B : ℕ → ℕ → 𝕜) (T : ℕ → 𝕜) (m : ℕ) : 𝕜 :=
  (T m - ∑ k : Fin m, B m k * complexTriangularSolution B T k) / B m m
termination_by m
decreasing_by exact k.isLt

lemma sum_complexTriangularSolution {B : ℕ → ℕ → 𝕜} (T : ℕ → 𝕜)
    (hd : ∀ m, B m m ≠ 0) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), B m k * complexTriangularSolution B T k) = T m := by
  rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range,
    complexTriangularSolution.eq_def (B := B) (T := T) (m := m)]
  rw [mul_comm (B m m), div_mul_cancel₀ _ (hd m)]
  ring

lemma complexTriangularSolution_eq_of_sum {B : ℕ → ℕ → 𝕜} {T r : ℕ → 𝕜}
    (hd : ∀ m, B m m ≠ 0)
    (hr : ∀ m, (∑ k ∈ Finset.range (m + 1), B m k * r k) = T m) (m : ℕ) :
    complexTriangularSolution B T m = r m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have h := hr m
    rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range] at h
    have hsum : (∑ k : Fin m, B m k * complexTriangularSolution B T k) =
        ∑ k : Fin m, B m k * r k := by
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [ih k k.isLt]
    rw [complexTriangularSolution.eq_def]
    apply (div_eq_iff (hd m)).mpr
    rw [← h, hsum]
    ring

lemma tendsto_complexTriangularSolution {ι : Type*} {l : Filter ι}
    [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
    {B : ℕ → ℕ → 𝕜} {T : ℕ → 𝕜} {T' : ι → ℕ → 𝕜}
    (hT : ∀ m, Tendsto (fun i ↦ T' i m) l (𝓝 (T m))) (m : ℕ) :
    Tendsto (fun i ↦ complexTriangularSolution B (T' i) m) l (𝓝 (complexTriangularSolution B T m)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    simp only [complexTriangularSolution.eq_def (m := m)]
    exact ((hT m).sub (tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun k _ ↦
      tendsto_const_nhds.mul (ih k.val k.isLt))).div_const _

/-- If a fixed triangular combination converges in every degree, so do its inputs. -/
theorem tendsto_of_complex_triangular_sums {ι : Type*} {l : Filter ι}
    [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] {B : ℕ → ℕ → 𝕜}
    {T : ℕ → 𝕜} {x : ι → ℕ → 𝕜} (hd : ∀ m, B m m ≠ 0)
    (h : ∀ m, Tendsto (fun i ↦ ∑ k ∈ Finset.range (m + 1), B m k * x i k) l (𝓝 (T m)))
    (m : ℕ) : Tendsto (fun i ↦ x i m) l (𝓝 (complexTriangularSolution B T m)) := by
  refine (tendsto_complexTriangularSolution h m).congr ?_
  intro i
  exact complexTriangularSolution_eq_of_sum (r := x i) hd (fun _ ↦ rfl) m

end Field

/-- Triangular inversion preserves measurability of coefficients of complex systems. -/
theorem measurable_complexTriangularSolution {α : Type*} [MeasurableSpace α]
    {B : α → ℕ → ℕ → ℂ} {T : α → ℕ → ℂ}
    (hB : ∀ m k, Measurable (fun a ↦ B a m k)) (hT : ∀ m, Measurable (fun a ↦ T a m))
    (m : ℕ) : Measurable (fun a ↦ complexTriangularSolution (B a) (T a) m) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    simp only [complexTriangularSolution.eq_def (m := m)]
    exact ((hT m).sub (Finset.measurable_sum (Finset.univ : Finset (Fin m)) fun k _ ↦
      (hB m k).mul (ih k.val k.isLt))).div (hB m m)

end Zalcman
