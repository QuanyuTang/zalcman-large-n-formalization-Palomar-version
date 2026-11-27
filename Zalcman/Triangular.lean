/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.Ring

/-!
# Limits of positive triangular representations

A lower triangular transformation with a nonzero diagonal has a unique inverse.
The inverse is continuous coefficient by coefficient, so the representation by
nonnegative coefficients passes to pointwise limits.
-/

public section

namespace Zalcman

open Filter
open scoped BigOperators Topology

/-- Solve the triangular system with matrix `B` and right-hand side `T`. -/
noncomputable def triangularSolution (B : ℕ → ℕ → ℝ) (T : ℕ → ℝ) (m : ℕ) : ℝ :=
  (T m - ∑ k : Fin m, B m k * triangularSolution B T k) / B m m
termination_by m
decreasing_by exact k.isLt

lemma sum_triangularSolution {B : ℕ → ℕ → ℝ} (T : ℕ → ℝ)
    (hd : ∀ m, B m m ≠ 0) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), B m k * triangularSolution B T k) = T m := by
  rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range,
    triangularSolution.eq_def (B := B) (T := T) (m := m)]
  rw [mul_comm (B m m), div_mul_cancel₀ _ (hd m)]
  ring

lemma triangularSolution_eq_of_sum {B : ℕ → ℕ → ℝ} {T r : ℕ → ℝ}
    (hd : ∀ m, B m m ≠ 0)
    (hr : ∀ m, (∑ k ∈ Finset.range (m + 1), B m k * r k) = T m) (m : ℕ) :
    triangularSolution B T m = r m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have h := hr m
    rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range] at h
    have hsum : (∑ k : Fin m, B m k * triangularSolution B T k) =
        ∑ k : Fin m, B m k * r k := by
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [ih k k.isLt]
    rw [triangularSolution.eq_def]
    apply (div_eq_iff (hd m)).mpr
    rw [← h, hsum]
    ring

lemma tendsto_triangularSolution {ι : Type*} {l : Filter ι}
    {B : ℕ → ℕ → ℝ} {T : ℕ → ℝ} {T' : ι → ℕ → ℝ}
    (hT : ∀ m, Tendsto (fun i ↦ T' i m) l (𝓝 (T m))) (m : ℕ) :
    Tendsto (fun i ↦ triangularSolution B (T' i) m) l (𝓝 (triangularSolution B T m)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    simp only [triangularSolution.eq_def (m := m)]
    exact ((hT m).sub (tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun k _ ↦
      tendsto_const_nhds.mul (ih k.val k.isLt))).div_const _

/-- Nonnegative representations with the same triangular matrix persist at the limit. -/
theorem exists_nonnegative_triangular_representation_of_pointwise_limit
    {ι : Type*} {l : Filter ι} [NeBot l] {B : ℕ → ℕ → ℝ} {T : ℕ → ℝ} {T' : ι → ℕ → ℝ}
    (hd : ∀ m, B m m ≠ 0) (hT : ∀ m, Tendsto (fun i ↦ T' i m) l (𝓝 (T m)))
    (h : ∀ i, ∃ r : ℕ → ℝ, (∀ k, 0 ≤ r k) ∧
      ∀ m, (∑ k ∈ Finset.range (m + 1), B m k * r k) = T' i m) :
    ∃ r : ℕ → ℝ, (∀ k, 0 ≤ r k) ∧
      ∀ m, (∑ k ∈ Finset.range (m + 1), B m k * r k) = T m := by
  refine ⟨triangularSolution B T, fun m ↦ ?_, sum_triangularSolution T hd⟩
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds (tendsto_triangularSolution hT m)
  intro i
  obtain ⟨r, hr, heq⟩ := h i
  exact (triangularSolution_eq_of_sum hd heq m).symm ▸ hr m

end Zalcman
