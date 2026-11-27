/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A quantitative Schwarz estimate for radial transition maps

A disk self-map fixing the origin with derivative a in [0,1) differs from
the identity by O(1 - a) on every compact subdisk.
-/

public section

namespace Zalcman

private lemma norm_one_sub_real_mul {a : ℝ} (ha : 0 ≤ a) (w : ℂ) :
    1 - a * ‖w‖ ≤ ‖1 - (a : ℂ) * w‖ := by
  simpa only [norm_one, norm_mul, Complex.norm_of_nonneg ha] using
    (norm_sub_norm_le (1 : ℂ) ((a : ℂ) * w))

private lemma norm_disk_transform {a : ℝ} {w : ℂ} (ha : 0 ≤ a) (ha₁ : a ≤ 1)
    (hw : ‖w‖ ≤ 1) : ‖w - (a : ℂ)‖ ≤ ‖1 - (a : ℂ) * w‖ := by
  have hid : ‖1 - (a : ℂ) * w‖ ^ 2 - ‖w - (a : ℂ)‖ ^ 2 =
      (1 - a ^ 2) * (1 - ‖w‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have ha' : 0 ≤ 1 - a ^ 2 := by
    have hh := pow_le_pow_left₀ ha ha₁ 2
    linarith
  have hw' : 0 ≤ 1 - ‖w‖ ^ 2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hw 2
    linarith
  have hsq := mul_nonneg ha' hw'
  rw [← hid, sub_nonneg] at hsq
  exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (norm_nonneg _) hsq

/-- The derivative deficit controls the deviation of a disk transition from the identity. -/
theorem norm_sub_id_of_disk_transition {phi : ℂ → ℂ} (hphi : DifferentiableOn ℂ phi unitDisk)
    (hmap : Set.MapsTo phi unitDisk unitDisk) (hzero : phi 0 = 0) {a : ℝ}
    (ha : 0 ≤ a) (ha₁ : a < 1) (hderiv : deriv phi 0 = (a : ℂ))
    {z : ℂ} (hz : z ∈ unitDisk) :
    ‖phi z - z‖ ≤ (1 - a) * (‖z‖ * (1 + ‖z‖) / (1 - ‖z‖)) := by
  let w := dslope phi 0
  have hopen : IsOpen unitDisk := Metric.isOpen_ball
  have hclose : Set.MapsTo phi (Metric.ball (0 : ℂ) 1) (Metric.closedBall (phi 0) 1) := by
    rw [hzero]
    exact fun v hv ↦ Metric.ball_subset_closedBall (hmap hv)
  have hw (v : ℂ) (hv : v ∈ unitDisk) : ‖w v‖ ≤ 1 := by
    simpa only [div_one] using Complex.norm_dslope_le_div_of_mapsTo_ball hphi hclose hv
  have hw0 : w 0 = (a : ℂ) := (dslope_same phi 0).trans hderiv
  have hwd : DifferentiableOn ℂ w unitDisk :=
    (Complex.differentiableOn_dslope (hopen.mem_nhds zero_mem_unitDisk)).mpr hphi
  have hden (v : ℂ) (hv : v ∈ unitDisk) : 1 - (a : ℂ) * w v ≠ 0 := by
    apply norm_pos_iff.mp
    have hl := norm_one_sub_real_mul ha (w v)
    have hm := mul_le_mul_of_nonneg_left (hw v hv) ha
    linarith
  let g := fun v ↦ (w v - (a : ℂ)) / (1 - (a : ℂ) * w v)
  have hgd : DifferentiableOn ℂ g unitDisk := by
    have hnum : DifferentiableOn ℂ (fun v ↦ w v - (a : ℂ)) unitDisk := hwd.sub_const _
    have hdiv : DifferentiableOn ℂ (fun v ↦ 1 - (a : ℂ) * w v) unitDisk :=
      (differentiableOn_const 1).fun_sub (hwd.const_mul (a : ℂ))
    exact hnum.div hdiv hden
  have hgmap : Set.MapsTo g unitDisk (Metric.closedBall (0 : ℂ) 1) := by
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖(w v - (a : ℂ)) / (1 - (a : ℂ) * w v)‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.mpr (hden v hv))]
    exact norm_disk_transform ha ha₁.le (hw v hv)
  have hg0 : g 0 = 0 := by simp [g, hw0]
  have hg := Complex.norm_le_norm_of_mapsTo_ball hgd hgmap hg0 (mem_unitDisk.mp hz)
  have hfloor : 1 - ‖z‖ ≤ ‖1 + (a : ℂ) * g z‖ := by
    have hnorm := norm_one_sub_real_mul ha (-g z)
    have hmul := mul_le_mul_of_nonneg_right ha₁.le (norm_nonneg (g z))
    rw [norm_neg, mul_neg, sub_neg_eq_add] at hnorm
    linarith
  have hz₁ : 0 < 1 - ‖z‖ := sub_pos.mpr (mem_unitDisk.mp hz)
  have hd' : 0 < ‖1 + (a : ℂ) * g z‖ := hz₁.trans_le hfloor
  have hrew : (w z - 1) * (1 + (a : ℂ) * g z) = ((a : ℂ) - 1) * (1 - g z) := by
    have hrel : g z * (1 - (a : ℂ) * w z) = w z - (a : ℂ) :=
      div_mul_cancel₀ _ (hden z hz)
    linear_combination -hrel
  have hnorm : ‖w z - 1‖ = (1 - a) * ‖1 - g z‖ / ‖1 + (a : ℂ) * g z‖ := by
    apply (eq_div_iff hd'.ne').mpr
    rw [← norm_mul, hrew, norm_mul,
      show (a : ℂ) - 1 = ((a - 1 : ℝ) : ℂ) by simp,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : a - 1 ≤ 0)]
    ring
  have hbound : ‖w z - 1‖ ≤ (1 - a) * (1 + ‖z‖) / (1 - ‖z‖) := by
    have hup : ‖1 - g z‖ ≤ 1 + ‖z‖ := by
      exact (norm_sub_le 1 _).trans (by rw [norm_one]; linarith only [hg])
    rw [hnorm]
    exact (div_le_div_of_nonneg_left (mul_nonneg (sub_nonneg.mpr ha₁.le) (norm_nonneg _))
      hz₁ hfloor).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hup (sub_nonneg.mpr ha₁.le)) hz₁.le)
  have hfactor : z * w z = phi z := by
    simpa only [sub_zero, smul_eq_mul, hzero] using sub_smul_dslope phi (0 : ℂ) z
  calc
    _ = ‖z * (w z - 1)‖ := by rw [mul_sub, hfactor, mul_one]
    _ = ‖z‖ * ‖w z - 1‖ := norm_mul _ _
    _ ≤ ‖z‖ * ((1 - a) * (1 + ‖z‖) / (1 - ‖z‖)) :=
      mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = _ := by ring

end Zalcman
