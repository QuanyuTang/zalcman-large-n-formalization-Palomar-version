/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Slit-plane image of the Koebe function

The Cayley map sends the unit disk onto a right half-plane. Squaring then
gives the slit-plane image used for the terminal Koebe continuation.
-/

public section

namespace Zalcman

private lemma unitDisk_sub_one_ne_zero {z : ℂ} (hz : z ∈ unitDisk) : 1 - z ≠ 0 := by
  intro he
  have h := mem_unitDisk.mp hz
  rw [← eq_of_sub_eq_zero he] at h
  simp at h

private lemma koebe_cayley_sq {z : ℂ} (hz : z ∈ unitDisk) :
    1 + 4 * koebe z = ((1 + z) / (1 - z)) ^ 2 := by
  have h0 := unitDisk_sub_one_ne_zero hz
  unfold koebe
  field_simp [h0] <;> ring

private lemma re_cayley_pos {z : ℂ} (hz : z ∈ unitDisk) : 0 < ((1 + z) / (1 - z)).re := by
  have hn : ‖z‖ ^ 2 < 1 ^ 2 :=
    pow_lt_pow_left₀ (mem_unitDisk.mp hz) (norm_nonneg _) (by decide : (2 : ℕ) ≠ 0)
  rw [Complex.div_re, ← add_div]
  have h := Complex.normSq_pos.mpr (unitDisk_sub_one_ne_zero hz)
  apply div_pos _ h
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  nlinarith only [hn]

private lemma sq_mem_slitPlane_of_re_pos {w : ℂ} (hw : 0 < w.re) : w ^ 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hi : (w ^ 2).im = 0
  · left
    rw [pow_two, Complex.mul_im] at hi
    have hz : (2 * w.re) * w.im = 0 := by linear_combination hi
    have him : w.im = 0 := (mul_eq_zero.mp hz).resolve_left (by positivity)
    simpa only [pow_two, Complex.mul_re, him, zero_mul, sub_zero] using mul_pos hw hw
  · exact Or.inr hi

private lemma exists_right_half_plane_sqrt {u : ℂ} (hu : u ∈ Complex.slitPlane) :
    ∃ w : ℂ, 0 < w.re ∧ w ^ 2 = u := by
  have harg := Complex.mem_slitPlane_iff_arg.mp hu
  refine ⟨Complex.exp (Complex.log u / 2), ?_, ?_⟩
  · rw [Complex.exp_re]
    apply mul_pos (Real.exp_pos _)
    apply Real.cos_pos_of_mem_Ioo
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_im, Complex.log_im]
    exact ⟨by linarith [Complex.neg_pi_lt_arg u],
      by linarith [lt_of_le_of_ne (Complex.arg_le_pi u) harg.1]⟩
  · rw [← Complex.exp_nat_mul]
    have h : ((2 : ℕ) : ℂ) * (Complex.log u / 2) = Complex.log u := by
      push_cast
      ring
    rw [h, Complex.exp_log harg.2]

private lemma inv_cayley_mem_disk {v : ℂ} (hv : 0 < v.re) :
    (v - 1) / (v + 1) ∈ unitDisk := by
  have hdiff : ‖v + 1‖ ^ 2 - ‖v - 1‖ ^ 2 = 4 * v.re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.sub_re,
      Complex.add_im, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have hn : ‖v - 1‖ < ‖v + 1‖ := by
    by_contra! hc
    have hb := pow_le_pow_left₀ (norm_nonneg (v + 1)) hc 2
    linarith
  rw [mem_unitDisk, norm_div, div_lt_one ((norm_nonneg _).trans_lt hn)]
  exact hn

/-- The image of the Koebe function is the plane with the ray ending at −1/4 removed. -/
theorem koebe_image_unitDisk :
    koebe '' unitDisk = {w : ℂ | (1 : ℂ) + 4 * w ∈ Complex.slitPlane} := by
  ext u
  constructor
  · rintro ⟨z, hz, rfl⟩
    change 1 + 4 * koebe z ∈ Complex.slitPlane
    rw [koebe_cayley_sq hz]
    exact sq_mem_slitPlane_of_re_pos (re_cayley_pos hz)
  · intro hu
    change (1 : ℂ) + 4 * u ∈ Complex.slitPlane at hu
    obtain ⟨v, hv, hs⟩ := exists_right_half_plane_sqrt hu
    let z := (v - 1) / (v + 1)
    have hz : z ∈ unitDisk := inv_cayley_mem_disk hv
    have hv0 : v + 1 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
      linarith
    have hf : (1 + z) / (1 - z) = v := by
      apply (div_eq_iff (unitDisk_sub_one_ne_zero hz)).mpr
      dsimp only [z]
      field_simp [hv0] <;> ring
    have hk := koebe_cayley_sq hz
    rw [hf, hs] at hk
    refine ⟨z, hz, ?_⟩
    linear_combination hk / 4

/-- Positive dilates of the Koebe image increase with the dilation parameter. -/
theorem koebe_scaled_image_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (fun z ↦ (a : ℂ) * koebe z) '' unitDisk ⊆
      (fun z ↦ (b : ℂ) * koebe z) '' unitDisk := by
  rintro _ ⟨z, hz, rfl⟩
  have hb : 0 < b := ha.trans_le hab
  let c := a / b
  have hc₀ : 0 < c := div_pos ha hb
  have hc₁ : c ≤ 1 := (div_le_one hb).mpr hab
  have hmem : (1 : ℂ) + 4 * koebe z ∈ Complex.slitPlane := by
    have h : koebe z ∈ koebe '' unitDisk := ⟨z, hz, rfl⟩
    rw [koebe_image_unitDisk] at h
    exact h
  have hmem' : (1 : ℂ) + 4 * ((c : ℂ) * koebe z) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff] at hmem ⊢
    have hre : (1 + 4 * ((c : ℂ) * koebe z)).re =
        (1 - c) + c * (1 + 4 * koebe z).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.one_re,
        Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have him : (1 + 4 * ((c : ℂ) * koebe z)).im = c * (1 + 4 * koebe z).im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.one_im,
        Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rcases hmem with h | h
    · left
      rw [hre]
      exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hc₁) (mul_pos hc₀ h)
    · right
      rw [him]
      exact mul_ne_zero hc₀.ne' h
  have hnew : (c : ℂ) * koebe z ∈ koebe '' unitDisk := by
    rwa [koebe_image_unitDisk]
  obtain ⟨w, hw, hkw⟩ := hnew
  refine ⟨w, hw, ?_⟩
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  change (b : ℂ) * koebe w = (a : ℂ) * koebe z
  rw [hkw, ← mul_assoc, show (b : ℂ) * (c : ℂ) = a by
    rw [show (c : ℂ) = (a : ℂ) / (b : ℂ) by simp [c], mul_comm (b : ℂ), div_mul_cancel₀ _ hbC]]

end Zalcman
