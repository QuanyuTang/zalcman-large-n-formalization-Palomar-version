/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pointwise real algebra of the fourth-order driving integrands
-/

@[expose] public section

namespace Zalcman

def fourthDrivingA (η : ℂ) : ℂ := 2 * (η - 1)

def fourthDrivingB (t : ℝ) (η : ℂ) : ℂ := -2 * (t : ℂ) * (η ^ 2 - 1)

def fourthDrivingC (t : ℝ) (η : ℂ) : ℂ := 2 * (t : ℂ) ^ 2 * ((η ^ 2 - 1) * (η + 2))

theorem fourthDrivingA_re_im {η : ℂ} {y v : ℝ}
    (hy : η.re = 1 - 2 * y) (hv : η.im = v) :
    (fourthDrivingA η).re = -4 * y ∧ (fourthDrivingA η).im = 2 * v := by
  constructor <;> simp [fourthDrivingA, Complex.mul_re, Complex.mul_im, hy, hv] <;> ring

private lemma driving_sq_re_im {η : ℂ} {y v : ℝ} (hη : ‖η‖ = 1)
    (hy : η.re = 1 - 2 * y) (hv : η.im = v) :
    (η ^ 2 - 1).re = -2 * v ^ 2 ∧ (η ^ 2 - 1).im = 2 * (1 - 2 * y) * v ∧
      v ^ 2 = 4 * y * (1 - y) := by
  have hunit := Complex.sq_norm η
  rw [hη, one_pow, Complex.normSq_apply, hy, hv] at hunit
  refine ⟨?_, ?_, ?_⟩
  · simp [pow_two, Complex.mul_re, hy, hv]
    nlinarith only [hunit]
  · simp [pow_two, Complex.mul_im, hy, hv]
    ring
  · nlinarith only [hunit]

theorem fourthDrivingB_re_im {η : ℂ} {y v : ℝ} (hη : ‖η‖ = 1)
    (hy : η.re = 1 - 2 * y) (hv : η.im = v) (t : ℝ) :
    (fourthDrivingB t η).re = 16 * t * y * (1 - y) ∧
      (fourthDrivingB t η).im = -4 * t * v + 8 * t * y * v := by
  obtain ⟨hre, him, hsq⟩ := driving_sq_re_im hη hy hv
  constructor
  · simp only [fourthDrivingB, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, zero_add, add_zero, sub_zero, hre, him, hsq]
    ring
  · simp only [fourthDrivingB, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, zero_add, add_zero, sub_zero, hre, him]
    ring

theorem fourthDrivingC_re {η : ℂ} {y v : ℝ} (hη : ‖η‖ = 1)
    (hy : η.re = 1 - 2 * y) (hv : η.im = v) (t : ℝ) :
    (fourthDrivingC t η).re = -64 * t ^ 2 * y * (1 - y) ^ 2 := by
  obtain ⟨hre, him, hsq⟩ := driving_sq_re_im hη hy hv
  simp only [fourthDrivingC, ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, zero_add, add_zero, sub_zero, hy, hv, hre, him, hsq]
  linear_combination (-4 * t ^ 2 * (1 - 2 * y)) * hsq

/-- The linear integral has a factor vanishing at the Koebe-driving endpoint. -/
theorem fourthDriving_linear_integrand_re {η : ℂ} {y v : ℝ} (hη : ‖η‖ = 1)
    (hy : η.re = 1 - 2 * y) (hv : η.im = v) (t : ℝ) :
    (8 * fourthDrivingA η + 6 * fourthDrivingB t η + fourthDrivingC t η).re =
      -32 * y * (1 - t * (1 - y)) * (1 - 2 * t * (1 - y)) := by
  obtain ⟨hA, _⟩ := fourthDrivingA_re_im hy hv
  obtain ⟨hB, _⟩ := fourthDrivingB_re_im hη hy hv t
  have hC := fourthDrivingC_re hη hy hv t
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero, hA, hB, hC]
  ring

/-- Pointwise estimate of the linear term by the quadratic driving energy. -/
theorem abs_fourthDriving_linear_integrand_re_le {η : ℂ} {y v t : ℝ}
    (hη : ‖η‖ = 1) (hy : η.re = 1 - 2 * y) (hv : η.im = v)
    (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    |(8 * fourthDrivingA η + 6 * fourthDrivingB t η + fourthDrivingC t η).re| ≤
      32 * ((1 - t) * y + t * y ^ 2) := by
  rw [fourthDriving_linear_integrand_re hη hy hv]
  have h₀ : 0 ≤ t * (1 - y) := mul_nonneg ht₀ (sub_nonneg.mpr hy₁)
  have h₁ : t * (1 - y) ≤ 1 := by
    calc
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left (by linarith only [hy₀]) ht₀
      _ = t := mul_one _
      _ ≤ _ := ht₁
  have hlast : |1 - 2 * t * (1 - y)| ≤ 1 := (abs_le.mpr ⟨by nlinarith only [h₁],
    by nlinarith only [h₀]⟩)
  have hNeg : |(-32 : ℝ) * y| = 32 * y := by
    rw [abs_mul, abs_of_nonneg hy₀]
    norm_num
  rw [abs_mul, abs_mul, hNeg, abs_of_nonneg (sub_nonneg.mpr h₁)]
  calc
    _ ≤ 32 * y * (1 - t * (1 - y)) * 1 :=
      mul_le_mul_of_nonneg_left hlast
        (mul_nonneg (mul_nonneg (by norm_num) hy₀) (sub_nonneg.mpr h₁))
    _ = _ := by ring

/-- Exact splitting of the triangular integrand into its signed kernel
and the mixed remainder controlled by the quadratic driving energy. -/
theorem fourthDriving_triangle_integrand_re {ηs ηt : ℂ} {ys yt vs vt : ℝ}
    (hηs : ‖ηs‖ = 1) (hηt : ‖ηt‖ = 1)
    (hys : ηs.re = 1 - 2 * ys) (hyt : ηt.re = 1 - 2 * yt)
    (hvs : ηs.im = vs) (hvt : ηt.im = vt) (s t : ℝ) :
    (12 * fourthDrivingA ηt * fourthDrivingA ηs +
       3 * fourthDrivingA ηt * fourthDrivingB s ηs +
       2 * fourthDrivingB t ηt * fourthDrivingA ηs).re =
      -(48 - 24 * s - 16 * t) * vs * vt +
        (192 * ys * yt - 192 * s * yt * ys * (1 - ys) - 128 * t * yt * ys * (1 - yt)
          - 48 * s * ys * vs * vt - 32 * t * yt * vs * vt) := by
  obtain ⟨hAs, hAsi⟩ := fourthDrivingA_re_im hys hvs
  obtain ⟨hAt, hAti⟩ := fourthDrivingA_re_im hyt hvt
  obtain ⟨hBs, hBsi⟩ := fourthDrivingB_re_im hηs hys hvs s
  obtain ⟨hBt, hBti⟩ := fourthDrivingB_re_im hηt hyt hvt t
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, mul_zero, sub_zero, add_zero, zero_add, hAs, hAsi, hAt, hAti, hBs, hBsi, hBt, hBti]
  ring

/-- The mixed fourth-order remainder is pointwise dominated by separable
products of the real and imaginary driving functions. -/
theorem abs_fourthDriving_triangle_remainder_le {s t ys yt vs vt : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hys : 0 ≤ ys) (hys1 : ys ≤ 1) (hyt : 0 ≤ yt) (hyt1 : yt ≤ 1) :
    |192 * ys * yt - 192 * s * yt * ys * (1 - ys) - 128 * t * yt * ys * (1 - yt) -
      48 * s * ys * vs * vt - 32 * t * yt * vs * vt| ≤
      512 * ys * yt + 48 * ys * |vs| * |vt| + 32 * yt * |vs| * |vt| := by
  let a := 192 * ys * yt
  let b := 192 * s * yt * ys * (1 - ys)
  let c := 128 * t * yt * ys * (1 - yt)
  let d := 48 * s * ys * vs * vt
  let e := 32 * t * yt * vs * vt
  have ha₀ : 0 ≤ a := by
    change 0 ≤ 192 * ys * yt
    positivity
  have ha : |a| = 192 * ys * yt := abs_of_nonneg ha₀
  have hys' : 0 ≤ 1 - ys := sub_nonneg.mpr hys1
  have hyt' : 0 ≤ 1 - yt := sub_nonneg.mpr hyt1
  have hb : |b| ≤ 192 * ys * yt := by
    dsimp only [b]
    rw [abs_of_nonneg (by positivity)]
    have hscale : s * (1 - ys) ≤ 1 := by
      simpa only [mul_one] using
        mul_le_mul hs1 (show 1 - ys ≤ 1 by linarith only [hys]) hys' zero_le_one
    calc
      _ = (s * (1 - ys)) * (192 * ys * yt) := by ring
      _ ≤ 1 * (192 * ys * yt) := mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = _ := one_mul _
  have hc : |c| ≤ 128 * ys * yt := by
    dsimp only [c]
    rw [abs_of_nonneg (by positivity)]
    have hscale : t * (1 - yt) ≤ 1 := by
      simpa only [mul_one] using
        mul_le_mul ht1 (show 1 - yt ≤ 1 by linarith only [hyt]) hyt' zero_le_one
    calc
      _ = (t * (1 - yt)) * (128 * ys * yt) := by ring
      _ ≤ 1 * (128 * ys * yt) := mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = _ := one_mul _
  have hd : |d| ≤ 48 * ys * |vs| * |vt| := by
    dsimp only [d]
    simp only [abs_mul, abs_of_nonneg hs, abs_of_nonneg hys,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 48)]
    calc
      _ = s * (48 * ys * |vs| * |vt|) := by ring
      _ ≤ 1 * (48 * ys * |vs| * |vt|) := mul_le_mul_of_nonneg_right hs1 (by positivity)
      _ = _ := one_mul _
  have he : |e| ≤ 32 * yt * |vs| * |vt| := by
    dsimp only [e]
    simp only [abs_mul, abs_of_nonneg ht, abs_of_nonneg hyt,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 32)]
    calc
      _ = t * (32 * yt * |vs| * |vt|) := by ring
      _ ≤ 1 * (32 * yt * |vs| * |vt|) := mul_le_mul_of_nonneg_right ht1 (by positivity)
      _ = _ := one_mul _
  have hab := norm_sub_le a b
  have habc := norm_sub_le (a - b) c
  have habcd := norm_sub_le (a - b - c) d
  have habcde := norm_sub_le (a - b - c - d) e
  simp only [Real.norm_eq_abs] at hab habc habcd habcde
  change |a - b - c - d - e| ≤ _
  nlinarith only [hab, habc, habcd, habcde, ha, hb, hc, hd, he]

/-- The cubic term is controlled by the first and second moments of the driver. -/
theorem abs_fourthDriving_cube_re_le {z : ℂ} {Y ν E d : ℝ}
    (hre : z.re = -4 * Y) (him : z.im = 2 * ν)
    (hY₀ : 0 ≤ Y) (hY₁ : Y ≤ 1) (hY₂ : Y ^ 2 ≤ E) (hν : ν ^ 2 ≤ d / 4) :
    |(z ^ 3).re| ≤ 64 * E + 12 * d := by
  have hcube : (z ^ 3).re = -64 * Y ^ 3 + 48 * Y * ν ^ 2 := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, pow_two]
    simp only [Complex.mul_re, Complex.mul_im, hre, him]
    ring
  have hY₃ : Y ^ 3 ≤ E := by
    calc
      _ = Y * Y ^ 2 := by ring
      _ ≤ 1 * Y ^ 2 := mul_le_mul_of_nonneg_right hY₁ (sq_nonneg _)
      _ = Y ^ 2 := one_mul _
      _ ≤ _ := hY₂
  have hYν : Y * ν ^ 2 ≤ d / 4 := by
    calc
      _ ≤ 1 * ν ^ 2 := mul_le_mul_of_nonneg_right hY₁ (sq_nonneg _)
      _ = ν ^ 2 := one_mul _
      _ ≤ _ := hν
  rw [hcube]
  calc
    _ ≤ |-64 * Y ^ 3| + |48 * Y * ν ^ 2| := abs_add_le _ _
    _ = 64 * Y ^ 3 + 48 * Y * ν ^ 2 := by
      rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hY₀ _)),
        abs_of_nonneg (by positivity)]
      ring
    _ ≤ _ := by nlinarith only [hY₃, hYν]

end Zalcman
