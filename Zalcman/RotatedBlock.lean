/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.PrefixRotation
public import Zalcman.ConstantPrefix
public import Zalcman.CoefficientBlocks
import Mathlib.Tactic.Ring

public section

namespace Zalcman

open Finset
open scoped ComplexConjugate

/-- Normalized rotation makes any geometric approximation a constant approximation. -/
theorem sum_rootCoeff_rotated_const_error {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {lam β : ℂ} (hUnit : ‖lam‖ = 1) (n : ℕ) :
    let h := rotate_normalizedUnivalent hf (by simpa only [Complex.norm_conj] using hUnit : ‖conj lam‖ = 1)
    (∑ i ∈ range n, ‖rootCoeff h i - β‖ ^ 2) =
      ∑ i ∈ range n, ‖rootCoeff hf i - β * lam ^ i‖ ^ 2 := by
  have hConjUnit : ‖conj lam‖ = 1 := by simpa only [Complex.norm_conj] using hUnit
  let hg := rotate_normalizedUnivalent hf hConjUnit
  change (∑ i ∈ range n, ‖rootCoeff hg i - β‖ ^ 2) = _
  have hunit : conj lam * lam = 1 := by rw [Complex.conj_mul', hUnit]; norm_num
  apply sum_congr rfl
  intro i _
  have hPower : conj lam ^ i * lam ^ i = 1 := by rw [← mul_pow, hunit, one_pow]
  have h : rootCoeff hg i - β = conj lam ^ i * (rootCoeff hf i - β * lam ^ i) := calc
    _ = conj lam ^ i * rootCoeff hf i - β := by rw [rootCoeff_rotate hf hConjUnit i]
    _ = conj lam ^ i * rootCoeff hf i - β * (conj lam ^ i * lam ^ i) := by rw [hPower, mul_one]
    _ = _ := by ring
  rw [h, norm_mul, norm_pow, hConjUnit, one_pow, one_mul]

/-- A controlled geometric approximation gives a unit phase after rotating the map. -/
theorem exists_reference_phase_of_geometric_approx {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {lam β : ℂ} (hUnit : ‖lam‖ = 1) {n : ℕ} (hn : 0 < n) {E : ℝ}
    (hGeom : (∑ j ∈ range n, ‖rootCoeff hf j - β * lam ^ j‖ ^ 2) ≤ E)
    (hNear : (n : ℝ) - ‖coeff f n‖ + E < n) (hDhalf : (n : ℝ) - ‖coeff f n‖ ≤ (n : ℝ) / 2)
    (hT : ∀ {g : ℂ → ℂ} (hg : NormalizedUnivalent g), 0 ≤ (milinCoefficients hg).milinSum n) :
    let g := rotate (conj lam) f
    let hg := rotate_normalizedUnivalent hf (by simpa only [Complex.norm_conj] using hUnit : ‖conj lam‖ = 1)
    let D := (n : ℝ) - ‖coeff f n‖
    ∃ α : ℂ, ‖α‖ = 1 ∧ (milinCoefficients hg).blockError α n ≤ D + 2 * E ∧
      ‖coeff g n / (‖coeff g n‖ : ℂ) - α ^ 2‖ ≤ 4 * (D + E) / (n : ℝ) := by
  have hConjUnit : ‖conj lam‖ = 1 := by simpa only [Complex.norm_conj] using hUnit
  let g := rotate (conj lam) f
  let hg := rotate_normalizedUnivalent hf hConjUnit
  let dg := milinCoefficients hg
  have hnorm : ‖coeff g n‖ = ‖coeff f n‖ := by
    dsimp only [g]
    rw [coeff_rotate f hConjUnit (by omega), norm_mul, norm_pow, hConjUnit, one_pow, one_mul]
  have hE : (∑ j ∈ range n, ‖dg.c j - β‖ ^ 2) ≤ E :=
    (sum_rootCoeff_rotated_const_error hf (β := β) hUnit n).trans_le hGeom
  have hMass := dg.partialMass_le_index hn (hT hg)
  obtain ⟨α, hα, hblock, hphase⟩ := MilinCoefficients.exists_unit_const_of_near_const dg hn hMass hE
    (by rw [milinCoefficients_squareCoeff hg, hnorm]; exact hNear)
    (by rw [milinCoefficients_squareCoeff hg, hnorm]; exact hDhalf)
  rw [← dg.blockError_eq_sum_norm_sub hα n, milinCoefficients_squareCoeff hg, hnorm] at hblock
  rw [milinCoefficients_squareCoeff hg] at hphase
  conv at hphase => rhs; rw [hnorm]
  exact ⟨α, hα, hblock, hphase⟩

end Zalcman
