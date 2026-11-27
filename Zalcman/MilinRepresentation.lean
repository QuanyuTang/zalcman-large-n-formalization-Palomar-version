/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CoefficientContinuity
public import Zalcman.Triangular
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Passing a positive Milin representation to a locally uniform limit

The shifted row index M corresponds to the Milin sum with index M+1.
The same triangular matrix is used for each approximant and for the limit.
-/

public section

namespace Zalcman

open Filter
open scoped BigOperators

/-- A common positive triangular representation persists under locally uniform convergence. -/
theorem exists_nonnegative_milin_representation_of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (h : TendstoLocallyUniformlyOn F f l unitDisk)
    (hF : ∀ i, NormalizedUnivalent (F i)) (hf : NormalizedUnivalent f)
    {B : ℕ → ℕ → ℝ} (hd : ∀ M, B M M ≠ 0)
    (hrep : ∀ i, ∃ rho : ℕ → ℝ, (∀ j, 0 ≤ rho j) ∧ ∀ M,
      (∑ j ∈ Finset.range (M + 1), B M j * rho j) = (milinCoefficients (hF i)).milinSum (M + 1)) :
    ∃ rho : ℕ → ℝ, rho 0 = 0 ∧ (∀ j, 0 ≤ rho j) ∧ ∀ M,
      (∑ j ∈ Finset.range (M + 1), B M j * rho j) = (milinCoefficients hf).milinSum (M + 1) := by
  obtain ⟨rho, hpos, hr⟩ := exists_nonnegative_triangular_representation_of_pointwise_limit hd
    (fun M ↦ tendsto_milinSum h hF hf (M + 1)) hrep
  refine ⟨rho, ?_, hpos, hr⟩
  have hzero : B 0 0 * rho 0 = 0 := by simpa using hr 0
  exact (mul_eq_zero.mp hzero).resolve_left (hd 0)

/-- Nonnegative summands give nonnegative Milin sums at all represented indices. -/
theorem milinSum_nonneg_of_representation {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {B : ℕ → ℕ → ℝ} {rho : ℕ → ℝ}
    (hB : ∀ M j, j ≤ M → 0 ≤ B M j) (hpos : ∀ j, 0 ≤ rho j)
    (hrep : ∀ M,
      (∑ j ∈ Finset.range (M + 1), B M j * rho j) = (milinCoefficients hf).milinSum (M + 1))
    (M : ℕ) : 0 ≤ (milinCoefficients hf).milinSum (M + 1) := by
  rw [← hrep]
  exact Finset.sum_nonneg fun j hj ↦
    mul_nonneg (hB M j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) (hpos j)

end Zalcman
