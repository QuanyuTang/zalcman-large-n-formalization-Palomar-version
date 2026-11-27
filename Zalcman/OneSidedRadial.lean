/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.RadialComparison
public import Zalcman.RadialKinematics
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The one-sided radial differential estimate

Over a previous unit interval, exponential comparison bounds the current
second-coefficient deficit by the loss of velocity amplitude. This controls
the real deficit of the velocity and hence the unnormalized radial deficit.
-/

public section

namespace Zalcman

open Set

private theorem le_decay_loss {E U : ℝ → ℝ} (hU0 : U 0 = 1)
    (hE : ∀ x ≥ 0, 0 ≤ E x ∧ E x ≤ 4)
    (hEd : ∀ x ≥ 0, HasDerivAt E (deriv E x) x)
    (hEderiv : ∀ x ≥ 0, deriv E x ≤ 8 * E x)
    (hU : ∀ x ≥ 0, 0 ≤ U x)
    (hUd : ∀ x ≥ 0, HasDerivAt U (-2 * E x * U x) x)
    {x : ℝ} (hx : 1 ≤ x) :
    E x ≤ (4 + (2 * Real.exp (-8))⁻¹) * (1 - U x) := by
  let a := 2 * Real.exp (-8)
  have ha : 0 < a := by dsimp [a]; positivity
  have hex : 0 ≤ x := by linarith
  have hprevious : 0 ≤ x - 1 := by linarith
  have hEx := hE x hex
  have hUp : U (x - 1) ≤ 1 := by
    have h := le_exp_mul_of_hasDerivAt_le (x := 0) (y := x - 1) (C := 0) hprevious
      (fun t ht => hUd t ht.1) (fun t ht => by
        simp only [zero_mul]
        nlinarith only [mul_nonneg (hE t ht.1).1 (hU t ht.1)])
    simpa only [zero_mul, Real.exp_zero, one_mul, hU0] using h
  have hElower (t : ℝ) (ht : t ∈ Icc (x - 1) x) : Real.exp (-8) * E x ≤ E t := by
    have ht₀ : 0 ≤ t := hprevious.trans ht.1
    have h := le_exp_mul_of_hasDerivAt_le (C := 8) ht.2
      (fun v hv => hEd v (ht₀.trans hv.1)) (fun v hv => hEderiv v (ht₀.trans hv.1))
    have hExp : Real.exp (8 * (x - t)) ≤ Real.exp 8 := by
      apply Real.exp_le_exp.mpr
      linarith only [ht.1]
    have hmul := h.trans (mul_le_mul_of_nonneg_right hExp (hE t ht₀).1)
    have hfinal := mul_le_mul_of_nonneg_left hmul (Real.exp_pos (-8)).le
    rwa [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at hfinal
  have hUdec : U x ≤ Real.exp (-(a * E x)) := by
    have h := le_exp_mul_of_hasDerivAt_le (x := x - 1) (y := x) (C := -(a * E x))
      (by linarith) (fun t ht => hUd t (hprevious.trans ht.1)) (fun t ht => by
        have hcalc := mul_le_mul_of_nonneg_right (hElower t ht) (hU t (hprevious.trans ht.1))
        dsimp only [a]
        nlinarith only [hcalc])
    rw [show x - (x - 1) = 1 by ring, mul_one] at h
    exact h.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hUp (Real.exp_pos _).le)
  have hprod : 0 ≤ a * E x := mul_nonneg ha.le hEx.1
  have hp : 0 < 1 + a * E x := by linarith
  have hexp : Real.exp (-(a * E x)) ≤ 1 / (1 + a * E x) := by
    rw [Real.exp_neg, one_div]
    apply inv_anti₀ hp
    simpa only [add_comm] using Real.add_one_le_exp (a * E x)
  have hdiv : a * E x / (1 + a * E x) ≤ 1 - U x := by
    have hcalc : a * E x / (1 + a * E x) = 1 - 1 / (1 + a * E x) := by
      field_simp
      ring
    rw [hcalc]
    exact sub_le_sub_left (hUdec.trans hexp) 1
  have hn : 0 ≤ 1 - U x := (div_nonneg hprod hp.le).trans hdiv
  have hnum := (div_le_iff₀ hp).mp hdiv
  have hden : 1 + a * E x ≤ 1 + 4 * a := by
    nlinarith only [mul_le_mul_of_nonneg_left hEx.2 ha.le]
  have hmul : a * E x ≤ (1 + 4 * a) * (1 - U x) :=
    hnum.trans (by simpa only [mul_comm (1 - U x)] using mul_le_mul_of_nonneg_right hden hn)
  apply (mul_le_mul_iff_of_pos_left ha).mp
  convert hmul using 1
  rw [show a * ((4 + a⁻¹) * (1 - U x)) = (4 * a + a * a⁻¹) * (1 - U x) by ring,
    mul_inv_cancel₀ ha.ne']
  ring

/-- The real-part velocity deficit has a uniform upper differential bound. -/
theorem radial_velocity_deficit_deriv_le {P Q : ℝ → ℂ}
    (hP : ∀ x ≥ 0, HasDerivAt P (2 * (Q x - 2) * P x) x)
    (hne : ∀ x ≥ 0, P x ≠ 0) (hP0 : ‖P 0‖ = 1)
    (hQ : ∀ x ≥ 0, ‖Q x‖ ≤ 2)
    (hE : ∀ x ≥ 0, HasDerivAt (fun t => 2 - (Q t).re)
      (deriv (fun t => 2 - (Q t).re) x) x)
    (hEd : ∀ x ≥ 0, deriv (fun t => 2 - (Q t).re) x ≤ 8 * (2 - (Q x).re)) :
    ∀ x ≥ 1, deriv (fun t => 1 - (P t).re) x ≤
      (6 * (4 + (2 * Real.exp (-8))⁻¹) + 2) * (1 - (P x).re) := by
  let E (t : ℝ) := 2 - (Q t).re
  let U (t : ℝ) := ‖P t‖
  have hEpos (t : ℝ) (ht : 0 ≤ t) : 0 ≤ E t ∧ E t ≤ 4 := by
    have ha := abs_le.mp ((Complex.abs_re_le_norm (Q t)).trans (hQ t ht))
    dsimp [E]
    constructor <;> linarith
  have hUd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt U (-2 * E t * U t) t := by
    have h := hasDerivAt_velocity_norm (hP t ht) (hne t ht)
    convert h using 1
    simp only [E, U, Complex.sub_re, Complex.re_ofNat]
    ring
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  have hup : U x ≤ 1 := by
    have h := le_exp_mul_of_hasDerivAt_le (x := 0) (y := x) (C := 0) hx0
      (fun t ht => hUd t ht.1) (fun t ht => by
        simp only [zero_mul]
        nlinarith only [mul_nonneg (hEpos t ht.1).1 (norm_nonneg (P t))])
    simpa only [zero_mul, Real.exp_zero, one_mul, U, hP0] using h
  have htemp := le_decay_loss hP0 hEpos hE hEd (fun _ _ => norm_nonneg _) hUd hx
  let V := 1 - (P x).re
  have hV : 0 ≤ V := sub_nonneg.mpr ((Complex.re_le_norm _).trans hup)
  have hEV : E x ≤ (4 + (2 * Real.exp (-8))⁻¹) * V :=
    htemp.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left (Complex.re_le_norm _) 1) (by positivity))
  have hQim : (Q x).im ^ 2 ≤ 4 * E x := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (hQ x hx0) 2
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    dsimp [E]
    nlinarith only [h, sq_nonneg ((Q x).re - 2)]
  have hPim : (P x).im ^ 2 ≤ 2 * V := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hup 2
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    dsimp [V]
    nlinarith only [h, sq_nonneg ((P x).re - 1)]
  have hder := (hasDerivAt_const x (1 : ℝ)).fun_sub
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hP x hx0))
  change HasDerivAt (fun t ↦ 1 - (P t).re) (0 - (Complex.reCLM (2 * (Q x - 2) * P x))) x
    at hder
  rw [hder.deriv]
  have hreal : 0 - (Complex.reCLM (2 * (Q x - 2) * P x)) =
      2 * E x * (P x).re + 2 * (Q x).im * (P x).im := by
    simp only [E, Complex.reCLM_apply, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    ring
  rw [hreal]
  have hre : (P x).re ≤ 1 := (Complex.re_le_norm _).trans hup
  nlinarith only [hEV, hQim, hPim, sq_nonneg ((Q x).im - (P x).im),
    mul_nonneg (hEpos x hx0).1 (sub_nonneg.mpr hre)]

/-- The unnormalized radial deficit inherits a uniform differential bound. -/
theorem oneSided_radial_deficit_deriv_le {H V : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hH0 : H 0 = 0)
    (hV₀ : ∀ t ≥ 0, 0 ≤ V t) (hH : ∀ t ≥ 0, HasDerivAt H (Real.exp (4 * t) * V t) t)
    (hV : ∀ t ≥ 1, HasDerivAt V (deriv V t) t)
    (hVd : ∀ t ≥ 1, deriv V t ≤ C * V t) {x : ℝ} (hx : 2 ≤ x) :
    deriv H x ≤ Real.exp (C + 4) * H x := by
  have hx₀ : 0 ≤ x := by linarith
  have hxm : 0 ≤ x - 1 := by linarith
  have hHpos : 0 ≤ H (x - 1) := by
    have hmono : MonotoneOn H (Icc 0 (x - 1)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact fun t ht => (hH t ht.1).continuousAt.continuousWithinAt
      · exact fun t ht => (hH t (interior_subset ht).1).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht₀ := (interior_subset ht).1
        rw [(hH t ht₀).deriv]
        exact mul_nonneg (Real.exp_pos _).le (hV₀ t ht₀)
    simpa only [hH0] using hmono (left_mem_Icc.mpr hxm) (right_mem_Icc.mpr hxm) hxm
  let b := Real.exp (4 * (x - 1)) * (Real.exp (-C) * V x)
  have hRate (t : ℝ) (ht : t ∈ Icc (x - 1) x) : b ≤ Real.exp (4 * t) * V t := by
    have ht1 : 1 ≤ t := by linarith only [ht.1, hx]
    have h := le_exp_mul_of_hasDerivAt_le (C := C) ht.2
      (fun v hv => hV v (ht1.trans hv.1)) (fun v hv => hVd v (ht1.trans hv.1))
    have hCompare : Real.exp (C * (x - t)) ≤ Real.exp C := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hC (show 0 ≤ 1 - (x - t) by linarith only [ht.1])]
    have h₁ := h.trans (mul_le_mul_of_nonneg_right hCompare (hV₀ t (by linarith)))
    have h₂ := mul_le_mul_of_nonneg_left h₁ (Real.exp_pos (-C)).le
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at h₂
    have h₃ : Real.exp (4 * (x - 1)) ≤ Real.exp (4 * t) :=
      Real.exp_le_exp.mpr (by linarith only [ht.1])
    exact mul_le_mul h₃ h₂ (mul_nonneg (Real.exp_pos _).le (hV₀ x hx₀)) (Real.exp_pos _).le
  let G (t : ℝ) := H t - b * t
  have hG (t : ℝ) (ht : t ∈ Icc (x - 1) x) :
      HasDerivAt G (Real.exp (4 * t) * V t - b) t := by
    simpa only [G, id, mul_one] using (hH t (hxm.trans ht.1)).fun_sub
      ((hasDerivAt_id t).const_mul b)
  have hMono : MonotoneOn G (Icc (x - 1) x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t ht => (hG t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hG t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hG t (interior_subset ht)).deriv]
      exact sub_nonneg.mpr (hRate t (interior_subset ht))
  have hxle : x - 1 ≤ x := by linarith
  have hb : b ≤ H x := by
    have hh := hMono (left_mem_Icc.mpr hxle) (right_mem_Icc.mpr hxle) hxle
    dsimp only [G] at hh
    linarith only [hh, hHpos]
  rw [(hH x hx₀).deriv]
  calc
    _ = Real.exp (C + 4) * b := by
      dsimp [b]
      rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 2 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le

end Zalcman
