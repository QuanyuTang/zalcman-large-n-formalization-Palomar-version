/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CoefficientVelocity
public import Zalcman.DiskTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic.Ring

/-!
# Positive-real functions from radial transitions

Dividing the deficit of the normalized transition slope by its derivative
deficit gives a holomorphic function with nonnegative real part and value one
at the origin. Its Taylor coefficients are the scaled higher transition
coefficients.
-/

@[expose] public section

namespace Zalcman

/-- The normalized deficit of a disk transition fixing zero. -/
noncomputable def transitionDriver (phi : ℂ → ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  (1 - dslope phi 0 z) / (1 - (a : ℂ))

/-- Schwarz bounds the normalized deficit in the right half-plane. -/
theorem transitionDriver_spec {phi : ℂ → ℂ} {a : ℝ}
    (hd : DifferentiableOn ℂ phi unitDisk) (hm : Set.MapsTo phi unitDisk unitDisk)
    (h₀ : phi 0 = 0) (hder : deriv phi 0 = (a : ℂ)) (ha : a < 1) :
    DifferentiableOn ℂ (transitionDriver phi a) unitDisk ∧ transitionDriver phi a 0 = 1 ∧
      ∀ z ∈ unitDisk, 0 ≤ (transitionDriver phi a z).re := by
  have hds : DifferentiableOn ℂ (dslope phi 0) unitDisk :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds zero_mem_unitDisk)).mpr hd
  have hcast : 1 - (a : ℂ) = ((1 - a : ℝ) : ℂ) := by simp
  have hden : 1 - (a : ℂ) ≠ 0 := hcast.symm ▸ Complex.ofReal_ne_zero.mpr (sub_pos.mpr ha).ne'
  have hclose : Set.MapsTo phi unitDisk (Metric.closedBall (phi 0) 1) := by
    rw [h₀]
    exact fun z hz ↦ Metric.ball_subset_closedBall (hm hz)
  refine ⟨((differentiableOn_const (1 : ℂ)).fun_sub hds).div_const _, ?_, ?_⟩
  · rw [transitionDriver, dslope_same, hder, div_self hden]
  · intro z hz
    have hnorm : ‖dslope phi 0 z‖ ≤ 1 := by
      simpa only [div_one] using Complex.norm_dslope_le_div_of_mapsTo_ball hd hclose hz
    rw [transitionDriver, hcast, Complex.div_ofReal_re, Complex.sub_re, Complex.one_re]
    exact div_nonneg (sub_nonneg.mpr ((Complex.re_le_norm _).trans hnorm)) (sub_nonneg.mpr ha.le)

/-- The positive-degree coefficients of the driver are the negatives of the next
transition coefficients divided by the derivative deficit. -/
theorem coeff_transitionDriver_succ {phi : ℂ → ℂ}
    (hd : DifferentiableOn ℂ phi unitDisk) (a : ℝ) (n : ℕ) :
    coeff (transitionDriver phi a) (n + 1) = -coeff phi (n + 2) / (1 - (a : ℂ)) := by
  let F := dslope phi 0
  have hsub : coeff (fun z ↦ 1 - F z) (n + 1) = -coeff F (n + 1) := by
    unfold coeff
    rw [iteratedDeriv_const_sub (Nat.succ_pos n), iteratedDeriv_neg, mul_neg]
  have heq : transitionDriver phi a = fun z ↦ (1 - (a : ℂ))⁻¹ * (1 - F z) := by
    funext z
    simp [transitionDriver, F, div_eq_mul_inv, mul_comm]
  rw [heq, coeff_const_mul, hsub, ← coeff_dslope hd (n + 1)]
  ring

/-- The normalized drivers are bounded on each compact subdisk uniformly in the
nonnegative transition derivative. -/
theorem norm_transitionDriver_le {phi : ℂ → ℂ} {a : ℝ}
    (hd : DifferentiableOn ℂ phi unitDisk) (hm : Set.MapsTo phi unitDisk unitDisk)
    (h₀ : phi 0 = 0) (hder : deriv phi 0 = (a : ℂ))
    (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : z ∈ unitDisk) :
    ‖transitionDriver phi a z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) := by
  by_cases hz₀ : z = 0
  · rw [hz₀, (transitionDriver_spec hd hm h₀ hder ha₁).2.1]
    simp
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz₀
  have hfactor := sub_smul_dslope phi (0 : ℂ) z
  rw [sub_zero, smul_eq_mul, h₀, sub_zero] at hfactor
  have hAbs : ‖1 - dslope phi 0 z‖ * ‖z‖ = ‖phi z - z‖ := by
    calc
      _ = ‖z * (1 - dslope phi 0 z)‖ := by rw [norm_mul, mul_comm]
      _ = ‖z - phi z‖ := by rw [mul_sub, mul_one, hfactor]
      _ = _ := norm_sub_rev _ _
  have hclose := norm_sub_id_of_disk_transition hd hm h₀ ha₀ ha₁ hder hz
  rw [transitionDriver, norm_div, show 1 - (a : ℂ) = ((1 - a : ℝ) : ℂ) by simp,
    Complex.norm_of_nonneg (sub_nonneg.mpr ha₁.le), div_le_iff₀ (sub_pos.mpr ha₁)]
  apply (mul_le_mul_iff_of_pos_right hzpos).mp
  rw [hAbs]
  calc
    _ ≤ _ := hclose
    _ = _ := by ring

end Zalcman
