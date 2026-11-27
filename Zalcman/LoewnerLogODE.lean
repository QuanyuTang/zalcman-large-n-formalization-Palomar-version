/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CoefficientVelocity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The coefficient equation for a radial Löwner velocity

With the radial velocity of the normalized logarithm as input, taking Taylor coefficients
gives the finite logarithmic coefficient system used in the energy calculation.
-/

public section

namespace Zalcman

open Finset Filter
open scoped Topology

/-- The radial Löwner factor for a point on the unit circle. -/
@[expose] noncomputable def radialDriver (κ z : ℂ) : ℂ := (1 + κ * z) / (1 - κ * z)

private theorem driver_denominator_ne_zero {κ z : ℂ} (hκ : ‖κ‖ ≤ 1) (hz : z ∈ unitDisk) :
    1 - κ * z ≠ 0 := by
  have hs : ‖κ * z‖ < 1 := calc
    _ = ‖κ‖ * ‖z‖ := norm_mul _ _
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hκ (norm_nonneg _)
    _ < _ := by simpa using mem_unitDisk.mp hz
  intro h
  rw [← eq_of_sub_eq_zero h, norm_one] at hs
  exact (lt_irrefl _ hs)

private theorem coeff_const_succ (c : ℂ) (n : ℕ) : coeff (fun _ : ℂ => c) (n + 1) = 0 := by
  simp [coeff, iteratedDeriv_const]

private theorem mul_z_coeff_succ {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisk) (n : ℕ) :
    coeff (fun z => z * f z) (n + 1) = coeff f n := by
  have hid (j : ℕ) : coeff (fun z : ℂ => z) j = if j = 1 then 1 else 0 := by
    by_cases hj : j = 1
    · simp [hj]
    · simp [coeff, iteratedDeriv_fun_id_zero, hj]
  have hid' : DifferentiableOn ℂ (fun z : ℂ => z) unitDisk := differentiableOn_id
  rw [coeff_mul hid' hf]
  simp_rw [hid, ite_mul, one_mul, zero_mul]
  rw [sum_eq_single 1]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h
    exact (h (mem_range.mpr (by omega))).elim

private theorem geometric_coeff {κ : ℂ} (hκ : ‖κ‖ ≤ 1) (n : ℕ) :
    coeff (fun z : ℂ => (1 - κ * z)⁻¹) n = κ ^ n := by
  let g (z : ℂ) := (1 - κ * z)⁻¹
  have hg : DifferentiableOn ℂ g unitDisk := by
    exact ((differentiableOn_const (1 : ℂ)).sub
      ((differentiableOn_const κ).mul differentiableOn_id)).inv
      (fun _ => driver_denominator_ne_zero hκ)
  have hzg : DifferentiableOn ℂ (fun z => κ * (z * g z)) unitDisk :=
    (differentiableOn_const κ).mul (differentiableOn_id.mul hg)
  have hz (j : ℕ) : coeff (fun z => g z - κ * (z * g z)) (j + 1) = 0 := by
    have heq : Set.EqOn (fun z => g z - κ * (z * g z)) (fun _ => 1) unitDisk := by
      intro z hz
      change (1 - κ * z)⁻¹ - κ * (z * (1 - κ * z)⁻¹) = 1
      rw [show (1 - κ * z)⁻¹ - κ * (z * (1 - κ * z)⁻¹) =
        (1 - κ * z) * (1 - κ * z)⁻¹ by ring, mul_inv_cancel₀ (driver_denominator_ne_zero hκ hz)]
    rw [coeff_congr_on_unitDisk heq]
    exact coeff_const_succ 1 j
  induction n with
  | zero => simp
  | succ j ih =>
    change coeff g (j + 1) = κ ^ (j + 1)
    have he := hz j
    rw [coeff_sub hg hzg, coeff_const_mul, mul_z_coeff_succ hg] at he
    change coeff g j = κ ^ j at ih
    rw [sub_eq_zero.mp he, ih, pow_succ, mul_comm]

/-- The coefficients of the radial driver are twice the positive powers of its phase. -/
theorem coeff_radialDriver {κ : ℂ} (hκ : ‖κ‖ ≤ 1) (n : ℕ) :
    coeff (radialDriver κ) (n + 1) = 2 * κ ^ (n + 1) := by
  let g (z : ℂ) := (1 - κ * z)⁻¹
  have hg : DifferentiableOn ℂ g unitDisk := by
    exact ((differentiableOn_const (1 : ℂ)).sub
      ((differentiableOn_const κ).mul differentiableOn_id)).inv
      (fun _ => driver_denominator_ne_zero hκ)
  have he : Set.EqOn (radialDriver κ) (fun z => 2 * g z - 1) unitDisk := by
    intro z hz
    change (1 + κ * z) / (1 - κ * z) = 2 * (1 - κ * z)⁻¹ - 1
    field_simp [driver_denominator_ne_zero hκ hz]
    ring
  have h2g : DifferentiableOn ℂ (fun z => (2 : ℂ) * g z) unitDisk :=
    (differentiableOn_const (2 : ℂ)).fun_mul hg
  rw [coeff_congr_on_unitDisk he, coeff_sub h2g
    (differentiableOn_const 1), coeff_const_mul]
  rw [show coeff g (n + 1) = κ ^ (n + 1) from geometric_coeff hκ _]
  rw [coeff_const_succ, sub_zero]

theorem radialDriver_holomorphic {κ : ℂ} (hκ : ‖κ‖ ≤ 1) :
    DifferentiableOn ℂ (radialDriver κ) unitDisk := by
  unfold radialDriver
  apply DifferentiableOn.div
  · exact (differentiableOn_const (1 : ℂ)).add ((differentiableOn_const κ).mul differentiableOn_id)
  · exact (differentiableOn_const (1 : ℂ)).sub ((differentiableOn_const κ).mul differentiableOn_id)
  · exact fun _ => driver_denominator_ne_zero hκ

private theorem coeff_one_add_z_deriv_succ {L : ℂ → ℂ}
    (hL : DifferentiableOn ℂ L unitDisk) (k : ℕ) :
    coeff (fun z => 1 + z * deriv L z) (k + 1) = (k + 1 : ℂ) * coeff L (k + 1) := by
  have hsub : (fun z => 1 + z * deriv L z) = fun z => z * deriv L z - (-1 : ℂ) := by
    funext z
    ring
  have hg : DifferentiableOn ℂ (fun z => z * deriv L z) unitDisk :=
    differentiableOn_id.fun_mul (hL.deriv unitDisk_isOpen)
  rw [hsub, coeff_sub hg
    (differentiableOn_const _), mul_z_coeff_succ (hL.deriv unitDisk_isOpen), coeff_deriv]
  rw [coeff_const_succ, sub_zero]

/-- The half-logarithm coefficients satisfy the radial logarithmic system when the
logarithm has the corresponding locally uniform time derivative. -/
theorem hasDerivAt_radialLogCoeff {L : ℝ → ℂ → ℂ} {u : ℝ} {κ : ℂ}
    (hκ : ‖κ‖ ≤ 1) (hL : ∀ t, DifferentiableOn ℂ (L t) unitDisk)
    (h : TendstoLocallyUniformlyOn (fun t z => slope (fun s => L s z) u t)
      (fun z => (1 + z * deriv (L u) z) * radialDriver κ z - 1) (𝓝[≠] u) unitDisk)
    (k : ℕ) :
    HasDerivAt (fun t => coeff (L t) (k + 1) / 2)
      (κ ^ (k + 1) + ((k : ℂ) + 1) * (coeff (L u) (k + 1) / 2) +
        2 * ∑ j ∈ range k, ((j : ℂ) + 1) * (coeff (L u) (j + 1) / 2) * κ ^ (k - j)) u := by
  have h₁ : DifferentiableOn ℂ (fun z => 1 + z * deriv (L u) z) unitDisk :=
    (differentiableOn_const (1 : ℂ)).add (differentiableOn_id.mul ((hL u).deriv unitDisk_isOpen))
  have h₂ := radialDriver_holomorphic hκ
  have hv := (hasDerivAt_coeff_of_locallyUniform_slope hL h (k + 1)).div_const (2 : ℂ)
  rw [coeff_sub (h₁.fun_mul h₂) (differentiableOn_const 1), coeff_mul h₁ h₂] at hv
  rw [sum_range_succ', sum_range_succ] at hv
  have hzero : coeff (fun z => 1 + z * deriv (L u) z) 0 = 1 := by simp
  have hdriverZero : coeff (radialDriver κ) 0 = 1 := by simp [radialDriver]
  have hidx (j : ℕ) (hj : j < k) : k + 1 - (j + 1) = (k - (j + 1)) + 1 := by omega
  have hsum : (∑ j ∈ range k,
      coeff (fun z => 1 + z * deriv (L u) z) (j + 1) * coeff (radialDriver κ) (k + 1 - (j + 1))) =
      ∑ j ∈ range k, ((j : ℂ) + 1) * coeff (L u) (j + 1) * (2 * κ ^ (k - j)) := by
    apply sum_congr rfl
    intro j hj
    rw [coeff_one_add_z_deriv_succ (hL u), hidx j (mem_range.mp hj), coeff_radialDriver hκ,
      show k - (j + 1) + 1 = k - j by have := mem_range.mp hj; omega]
  rw [hsum] at hv
  simp only [Nat.sub_self, Nat.sub_zero, coeff_one_add_z_deriv_succ (hL u), hzero, hdriverZero,
    coeff_radialDriver hκ, one_mul, mul_one] at hv
  rw [coeff_const_succ, sub_zero] at hv
  have hsum' : 2 * (∑ j ∈ range k, ((j : ℂ) + 1) * (coeff (L u) (j + 1) / 2) * κ ^ (k - j)) =
      ∑ j ∈ range k, ((j : ℂ) + 1) * coeff (L u) (j + 1) * κ ^ (k - j) := by
    rw [mul_sum]
    exact sum_congr rfl (fun _ _ => by ring)
  have hsum'' : (∑ j ∈ range k, ((j : ℂ) + 1) * coeff (L u) (j + 1) * (2 * κ ^ (k - j))) =
      2 * ∑ j ∈ range k, ((j : ℂ) + 1) * coeff (L u) (j + 1) * κ ^ (k - j) := by
    rw [mul_sum]
    exact sum_congr rfl (fun _ _ => by ring)
  rw [hsum']
  rw [hsum''] at hv
  convert hv using 1
  ring

/-- The ordinary normalized Taylor coefficients obey the triangular radial system. -/
theorem hasDerivAt_radialTaylorCoeff {F : ℝ → ℂ → ℂ} {u : ℝ} {κ : ℂ}
    (hκ : ‖κ‖ ≤ 1) (hF : ∀ t, DifferentiableOn ℂ (F t) unitDisk)
    (h : TendstoLocallyUniformlyOn (fun t z => slope (fun s => F s z) u t)
      (fun z => z * deriv (F u) z * radialDriver κ z - F u z) (𝓝[≠] u) unitDisk)
    (k : ℕ) :
    HasDerivAt (fun t => coeff (F t) (k + 1))
      ((k : ℂ) * coeff (F u) (k + 1) + 2 *
        ∑ j ∈ range k, ((j : ℂ) + 1) * coeff (F u) (j + 1) * κ ^ (k - j)) u := by
  have hid : DifferentiableOn ℂ (fun z : ℂ => z) unitDisk := differentiableOn_id
  have hDer := (hF u).deriv unitDisk_isOpen
  have h₁ := hid.fun_mul hDer
  have h₂ := radialDriver_holomorphic hκ
  have hv := hasDerivAt_coeff_of_locallyUniform_slope hF h (k + 1)
  rw [coeff_sub (h₁.fun_mul h₂) (hF u), coeff_mul h₁ h₂, sum_range_succ', sum_range_succ] at hv
  have hzero : coeff (fun z => z * deriv (F u) z) 0 = 0 := by simp
  have hdriverZero : coeff (radialDriver κ) 0 = 1 := by simp [radialDriver]
  have hsum : (∑ j ∈ range k,
      coeff (fun z => z * deriv (F u) z) (j + 1) * coeff (radialDriver κ) (k + 1 - (j + 1))) =
      2 * ∑ j ∈ range k, ((j : ℂ) + 1) * coeff (F u) (j + 1) * κ ^ (k - j) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [mul_z_coeff_succ hDer, coeff_deriv,
      show k + 1 - (j + 1) = (k - (j + 1)) + 1 by omega,
      coeff_radialDriver hκ, show k - (j + 1) + 1 = k - j by omega]
    ring
  rw [hsum] at hv
  simp only [Nat.sub_self, hzero, hdriverZero, zero_mul, add_zero, mul_one,
    mul_z_coeff_succ hDer, coeff_deriv] at hv
  convert hv using 1
  ring

end Zalcman
