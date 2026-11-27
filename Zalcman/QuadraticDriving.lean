/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quadratic estimates for the real driving data

For a unit-valued radial Löwner driving function, the real and imaginary parts give
the data `y` and `v`. The estimates here use their pointwise quadratic relation and
the sign of the real part of the second coefficient after a half-turn rotation.
-/

public section

open MeasureTheory Set Filter

namespace Zalcman

local notation "μ₁" => volume.restrict (Ioc (0 : ℝ) 1)

private lemma driving_restrict_univ : μ₁ univ = 1 := by
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc]
  norm_num

private instance driving_finiteMeasure : IsFiniteMeasure μ₁ :=
  ⟨by rw [driving_restrict_univ]; exact ENNReal.one_lt_top⟩

private lemma ae_mem_driving_interval : ∀ᵐ t ∂μ₁, t ∈ Ioc (0 : ℝ) 1 :=
  ae_restrict_mem (μ := volume) measurableSet_Ioc

private lemma driving_integral_const (c : ℝ) : (∫ _ : ℝ, c ∂μ₁) = c := by
  simp [MeasureTheory.integral_const, measureReal_def, smul_eq_mul]

private lemma integrable_driving_of_bound {f : ℝ → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ t ∈ Ioc (0 : ℝ) 1, |f t| ≤ C) : Integrable f μ₁ :=
  Integrable.of_bound hf.aestronglyMeasurable C <|
    ae_mem_driving_interval.mono fun t ht ↦ by simpa only [Real.norm_eq_abs] using hC t ht

private lemma driving_integral_id : (∫ t : ℝ, t ∂μ₁) = 1 / 2 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_id]
  norm_num

private lemma integrable_driving_id : Integrable (fun t : ℝ ↦ t) μ₁ :=
  integrable_driving_of_bound measurable_id 1 fun t ht ↦ by simpa [abs_of_pos ht.1] using ht.2

private lemma driving_integral_weight : (∫ t, (1 - t) ∂μ₁) = 1 / 2 := by
  rw [integral_sub (f := fun _ : ℝ ↦ (1 : ℝ)) (g := fun t ↦ t)
    (integrable_const _) integrable_driving_id, driving_integral_const, driving_integral_id]
  norm_num

/-- The real quadratic driving estimates on the unit interval.

The variables `Y`, `ν`, and `E` are the real driving mean, the imaginary driving
mean, and the quadratic energy. The quantity `d` equals `3 - Re a₃` when the
second and third coefficients satisfy the reverse Löwner coefficient formulas. -/
theorem quadratic_driving_estimates {y v : ℝ → ℝ}
    (hy_meas : Measurable y) (hv_meas : Measurable v)
    (hy : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ y t ∧ y t ≤ 1)
    (hv : ∀ t ∈ Ioc (0 : ℝ) 1, v t ^ 2 = 4 * y t * (1 - y t))
    (hY : (∫ t in (0 : ℝ)..1, y t) ≤ 1 / 2) :
    let Y := ∫ t in (0 : ℝ)..1, y t
    let ν := ∫ t in (0 : ℝ)..1, v t
    let E := ∫ t in (0 : ℝ)..1, (1 - t) * y t + t * y t ^ 2
    let d := 16 * (E - Y ^ 2) + 4 * ν ^ 2
    IntervalIntegrable v volume 0 1 ∧ 0 ≤ Y ∧
      E - Y ^ 2 = (∫ t in (0 : ℝ)..1, (y t - Y) ^ 2) +
        (∫ t in (0 : ℝ)..1, (1 - t) * y t * (1 - y t)) ∧
      E ≤ 65 * d / 16 ∧ Y ^ 2 ≤ E ∧
      (∫ t in (0 : ℝ)..1, y t ^ 2) ≤ E ∧
      (∫ t in (0 : ℝ)..1, v t ^ 2) ≤ 4 * Y ∧
      (∫ t in (0 : ℝ)..1, (1 - t) * v t ^ 2) ≤ d / 4 ∧
      (2 * ν) ^ 2 ≤ d := by
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hY ⊢
  let Y := ∫ t, y t ∂μ₁
  let ν := ∫ t, v t ∂μ₁
  let E := ∫ t, ((1 - t) * y t + t * y t ^ 2) ∂μ₁
  let d := 16 * (E - Y ^ 2) + 4 * ν ^ 2
  let σ₂ := ∫ t, (y t - Y) ^ 2 ∂μ₁
  let Q := ∫ t, ((1 - t) * y t * (1 - y t)) ∂μ₁
  change IntervalIntegrable v volume 0 1 ∧ 0 ≤ Y ∧ E - Y ^ 2 = σ₂ + Q ∧ E ≤ 65 * d / 16 ∧
    Y ^ 2 ≤ E ∧ (∫ t, y t ^ 2 ∂μ₁) ≤ E ∧ (∫ t, v t ^ 2 ∂μ₁) ≤ 4 * Y ∧
    (∫ t, (1 - t) * v t ^ 2 ∂μ₁) ≤ d / 4 ∧ (2 * ν) ^ 2 ≤ d
  change Y ≤ 1 / 2 at hY
  have hY0 : 0 ≤ Y := integral_nonneg_of_ae <|
    ae_mem_driving_interval.mono fun t ht ↦ (hy t ht).1
  have hyInt : Integrable y μ₁ := integrable_driving_of_bound hy_meas 1 fun t ht ↦ by
    rw [abs_of_nonneg (hy t ht).1]
    exact (hy t ht).2
  have hySqInt : Integrable (fun t ↦ y t ^ 2) μ₁ :=
    integrable_driving_of_bound (by fun_prop) 1 fun t ht ↦ by
      rw [abs_of_nonneg (sq_nonneg _)]
      simpa using pow_le_pow_left₀ (hy t ht).1 (hy t ht).2 2
  have hqInt : Integrable (fun t ↦ (1 - t) * y t * (1 - y t)) μ₁ :=
    integrable_driving_of_bound (by fun_prop) 1 fun t ht ↦ by
      have hyt := hy t ht
      have hw0 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
      have hw1 : 1 - t ≤ 1 := by linarith only [ht.1]
      have hcy0 : 0 ≤ 1 - y t := sub_nonneg.mpr hyt.2
      have hcy1 : 1 - y t ≤ 1 := by linarith only [hyt.1]
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg hw0 hyt.1) hcy0)]
      calc
        _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul hw1 hyt.2 hyt.1 zero_le_one) hcy1 hcy0 (by norm_num)
        _ = _ := by norm_num
  have hWeightInt : Integrable (fun t : ℝ ↦ 1 - t) μ₁ :=
    integrable_driving_of_bound (by fun_prop) 1 fun t ht ↦ by
      rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]
      linarith [ht.1]
  have hEInt : Integrable (fun t ↦ (1 - t) * y t + t * y t ^ 2) μ₁ := by
    have he : (fun t ↦ (1 - t) * y t + t * y t ^ 2) =
        (fun t ↦ y t ^ 2 + (1 - t) * y t * (1 - y t)) := by ext t; ring
    rw [he]
    exact hySqInt.add hqInt
  have hσInt : Integrable (fun t ↦ (y t - Y) ^ 2) μ₁ := by
    have hfun : (fun t ↦ (y t - Y) ^ 2) = (fun t ↦ y t ^ 2 - (2 * Y) * y t + Y ^ 2) := by
      ext t
      ring
    rw [hfun]
    exact (hySqInt.sub (hyInt.const_mul (2 * Y))).add (integrable_const _)
  have hσ₂ : σ₂ = (∫ t, y t ^ 2 ∂μ₁) - Y ^ 2 := by
    dsimp only [σ₂]
    calc
      _ = ∫ t, (y t ^ 2 - (2 * Y) * y t + Y ^ 2) ∂μ₁ := by
        congr 1
        ext t
        ring
      _ = _ := by
        rw [integral_add (f := fun t ↦ y t ^ 2 - (2 * Y) * y t) (g := fun _ ↦ Y ^ 2)
          (hySqInt.sub (hyInt.const_mul _)) (integrable_const _),
          integral_sub (f := fun t ↦ y t ^ 2) (g := fun t ↦ (2 * Y) * y t)
            hySqInt (hyInt.const_mul _), integral_const_mul, driving_integral_const]
        change _ - _ * Y + _ = _
        ring
  have hE : E = (∫ t, y t ^ 2 ∂μ₁) + Q := by
    dsimp only [E, Q]
    calc
      _ = ∫ t, (y t ^ 2 + (1 - t) * y t * (1 - y t)) ∂μ₁ := by
        congr 1
        ext t
        ring
      _ = _ := integral_add hySqInt hqInt
  have hIdentity : E - Y ^ 2 = σ₂ + Q := by linarith only [hE, hσ₂]
  have hσ0 : 0 ≤ σ₂ := integral_nonneg fun t ↦ sq_nonneg _
  have hQ0 : 0 ≤ Q := integral_nonneg_of_ae <| ae_mem_driving_interval.mono fun t ht ↦
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hy t ht).1) (sub_nonneg.mpr (hy t ht).2)
  have hE_le_Y : E ≤ Y := integral_mono_ae hEInt hyInt <| ae_mem_driving_interval.mono fun t ht ↦ by
    have hyt := hy t ht
    nlinarith only [mul_nonneg (mul_nonneg ht.1.le hyt.1) (sub_nonneg.mpr hyt.2)]
  have hd_lower : 16 * (σ₂ + Q) ≤ d := by
    dsimp only [d]
    rw [hIdentity]
    nlinarith only [sq_nonneg ν]
  have henergy : E ≤ 65 * d / 16 := by
    by_cases hlarge : Y ^ 2 / 64 ≤ σ₂
    · linarith only [hIdentity, hlarge, hd_lower, hQ0]
    · have hsmall : σ₂ < Y ^ 2 / 64 := lt_of_not_ge hlarge
      have hYpos : 0 < Y := by
        by_contra! hbad
        have : Y = 0 := le_antisymm hbad hY0
        rw [this] at hsmall
        norm_num at hsmall
        exact hsmall.not_ge hσ0
      have hpoint (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
          (Y / 4) * ((Y * (1 - Y)) * (1 - t) - (1 - t) * y t * (1 - y t)) ≤
            (y t - Y) ^ 2 + Y ^ 2 / 64 := by
        have hyt := hy t ht
        have hlip : |Y * (1 - Y) - y t * (1 - y t)| ≤ |y t - Y| := by
          rw [show Y * (1 - Y) - y t * (1 - y t) = (Y - y t) * (1 - Y - y t) by ring,
            abs_mul, abs_sub_comm Y (y t)]
          refine mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨?_, ?_⟩)
          · linarith only [hY, hyt.2]
          · linarith only [hY0, hyt.1]
        have hweighted :
            Y * (1 - Y) * (1 - t) - (1 - t) * y t * (1 - y t) ≤ |y t - Y| := calc
          _ = (1 - t) * (Y * (1 - Y) - y t * (1 - y t)) := by ring
          _ ≤ (1 - t) * |Y * (1 - Y) - y t * (1 - y t)| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (sub_nonneg.mpr ht.2)
          _ ≤ |Y * (1 - Y) - y t * (1 - y t)| :=
            mul_le_of_le_one_left (abs_nonneg _) (by linarith [ht.1])
          _ ≤ _ := hlip
        calc
          _ ≤ (Y / 4) * |y t - Y| := mul_le_mul_of_nonneg_left hweighted (by positivity)
          _ ≤ _ := by
            have hsq := sq_nonneg (|y t - Y| - Y / 8)
            nlinarith only [hsq, sq_abs (y t - Y)]
      have hdiffInt := (hWeightInt.const_mul (Y * (1 - Y))).sub hqInt
      have hInt := integral_mono_ae (hdiffInt.const_mul (Y / 4))
        (hσInt.add (integrable_const (Y ^ 2 / 64))) <| ae_mem_driving_interval.mono fun t ht ↦ hpoint t ht
      change (∫ t, (Y / 4) * (Y * (1 - Y) * (1 - t) - (1 - t) * y t * (1 - y t)) ∂μ₁) ≤
        (∫ t, (y t - Y) ^ 2 + Y ^ 2 / 64 ∂μ₁) at hInt
      rw [integral_const_mul,
        integral_sub (f := fun t ↦ Y * (1 - Y) * (1 - t))
          (g := fun t ↦ (1 - t) * y t * (1 - y t)) (hWeightInt.const_mul _) hqInt,
        integral_const_mul, driving_integral_weight,
        integral_add (f := fun t ↦ (y t - Y) ^ 2) (g := fun _ ↦ Y ^ 2 / 64)
          hσInt (integrable_const _), driving_integral_const] at hInt
      change (Y / 4) * (Y * (1 - Y) * (1 / 2) - Q) ≤ σ₂ + Y ^ 2 / 64 at hInt
      have hQabs : Y * (1 - Y) * (1 / 2) - Q ≤ Y / 8 := by
        apply (mul_le_mul_iff_right₀ (show 0 < Y / 4 by positivity)).mp
        nlinarith only [hsmall, hInt]
      have hQ : Y / 8 ≤ Q := by
        nlinarith only [hQabs, mul_nonneg hY0 (sub_nonneg.mpr hY)]
      linarith only [hE_le_Y, hY0, hd_lower, hσ0, hQ]
  have hvSq : (∫ t, v t ^ 2 ∂μ₁) = 4 * (Y - ∫ t, y t ^ 2 ∂μ₁) := calc
    _ = ∫ t, (4 * (y t - y t ^ 2)) ∂μ₁ := integral_congr_ae <|
      ae_mem_driving_interval.mono fun t ht ↦ by rw [hv t ht]; ring
    _ = _ := by rw [integral_const_mul, integral_sub hyInt hySqInt]
  have hvWeighted : (∫ t, (1 - t) * v t ^ 2 ∂μ₁) = 4 * Q := calc
    _ = ∫ t, (4 * ((1 - t) * y t * (1 - y t))) ∂μ₁ := integral_congr_ae <|
      ae_mem_driving_interval.mono fun t ht ↦ by rw [hv t ht]; ring
    _ = _ := integral_const_mul _ _
  have hvInt : Integrable v μ₁ := integrable_driving_of_bound hv_meas 2 fun t ht ↦ by
    have hv_bound : v t ^ 2 ≤ 4 := by
      rw [hv t ht]
      have hyt := hy t ht
      nlinarith only [hyt.2, mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg (y t))]
    by_contra! hbad
    have h := pow_lt_pow_left₀ hbad (by norm_num : (0 : ℝ) ≤ 2) (by decide : (2 : ℕ) ≠ 0)
    rw [sq_abs] at h
    nlinarith only [hv_bound, h]
  have hYSq0 : 0 ≤ ∫ t, y t ^ 2 ∂μ₁ := integral_nonneg fun _ ↦ sq_nonneg _
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).2 hvInt,
    hY0, hIdentity, henergy, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hIdentity, hσ0, hQ0]
  · linarith only [hE, hQ0]
  · linarith only [hvSq, hYSq0]
  · linarith only [hvWeighted, hd_lower, hσ0]
  · dsimp only [d]
    nlinarith only [hIdentity, hσ0, hQ0]

/-- The reverse-time coefficient formulas bound the quadratic driving moments. -/
theorem quadratic_moments_of_unit_driving {η : ℝ → ℂ} {a₂ a₃ : ℂ}
    (hη : Measurable η) (hunit : ∀ t ∈ Ioc (0 : ℝ) 1, ‖η t‖ = 1)
    (ha₂ : a₂ = 2 * ∫ t in (0 : ℝ)..1, η t)
    (ha₃ : a₃ = a₂ ^ 2 - 2 * ∫ t in (0 : ℝ)..1, (t : ℂ) * η t ^ 2)
    (ha₂sign : 0 ≤ a₂.re) :
    let y (t : ℝ) := (1 - (η t).re) / 2
    let v (t : ℝ) := (η t).im
    let Y := ∫ t in (0 : ℝ)..1, y t
    let ν := ∫ t in (0 : ℝ)..1, v t
    let E := ∫ t in (0 : ℝ)..1, (1 - t) * y t + t * y t ^ 2
    let d := 3 - a₃.re
    0 ≤ Y ∧ Y ≤ 1 / 2 ∧ E ≤ 65 * d / 16 ∧ Y ^ 2 ≤ E ∧
      (∫ t in (0 : ℝ)..1, y t ^ 2) ≤ E ∧
      (∫ t in (0 : ℝ)..1, v t ^ 2) ≤ 4 * Y ∧
      (∫ t in (0 : ℝ)..1, (1 - t) * v t ^ 2) ≤ d / 4 ∧
      ν ^ 2 ≤ d / 4 ∧ a₂.im ^ 2 ≤ d := by
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ha₂ ha₃ ⊢
  let y (t : ℝ) := (1 - (η t).re) / 2
  let v (t : ℝ) := (η t).im
  let Y := ∫ t, y t ∂μ₁
  let ν := ∫ t, v t ∂μ₁
  let E := ∫ t, ((1 - t) * y t + t * y t ^ 2) ∂μ₁
  have hy_meas : Measurable y := by
    dsimp only [y]
    fun_prop
  have hv_meas : Measurable v := by
    dsimp only [v]
    fun_prop
  have hy (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : 0 ≤ y t ∧ y t ≤ 1 := by
    have hre := Complex.abs_re_le_norm (η t)
    rw [hunit t ht] at hre
    obtain ⟨hlo, hhi⟩ := abs_le.mp hre
    dsimp only [y]
    constructor <;> linarith
  have hnorm (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : (η t).re ^ 2 + (η t).im ^ 2 = 1 := by
    have hs : ‖η t‖ ^ 2 = 1 := by simp [hunit t ht]
    rw [Complex.sq_norm, Complex.normSq_apply] at hs
    nlinarith only [hs]
  have hvsq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : v t ^ 2 = 4 * y t * (1 - y t) := by
    dsimp only [y, v]
    nlinarith only [hnorm t ht]
  have hηInt : Integrable η μ₁ := Integrable.of_bound hη.aestronglyMeasurable 1 <|
    ae_mem_driving_interval.mono fun t ht ↦ (hunit t ht).le
  have hweightedInt : Integrable (fun t : ℝ ↦ (t : ℂ) * η t ^ 2) μ₁ :=
    Integrable.of_bound (by fun_prop) 1 <| ae_mem_driving_interval.mono fun t ht ↦ by
      rw [norm_mul, norm_pow, hunit t ht, Complex.norm_of_nonneg ht.1.le]
      simpa using ht.2
  have hyInt : Integrable y μ₁ := integrable_driving_of_bound hy_meas 1 fun t ht ↦ by
    rw [abs_of_nonneg (hy t ht).1]
    exact (hy t ht).2
  have hη_re : (∫ t, η t ∂μ₁).re = 1 - 2 * Y := by
    have hcomm : (∫ t, (η t).re ∂μ₁) = (∫ t, η t ∂μ₁).re := by
      simpa only [Complex.reCLM_apply] using Complex.reCLM.integral_comp_comm hηInt
    rw [← hcomm]
    have hident (t : ℝ) : (η t).re = 1 - 2 * y t := by dsimp only [y]; ring
    simp_rw [hident]
    rw [integral_sub (integrable_const _) (hyInt.const_mul 2), driving_integral_const, integral_const_mul]
  have ha₂re : a₂.re = 2 * (1 - 2 * Y) := by
    rw [ha₂, Complex.mul_re, hη_re]
    norm_num
  have ha₂im : a₂.im = 2 * ν := by
    have hcomm : ν = (∫ t, η t ∂μ₁).im := by
      simpa only [ν, v, Complex.imCLM_apply] using Complex.imCLM.integral_comp_comm hηInt
    rw [ha₂, Complex.mul_im, ← hcomm]
    norm_num
  have hY : Y ≤ 1 / 2 := by linarith only [ha₂re, ha₂sign]
  have hEInt : Integrable (fun t ↦ (1 - t) * y t + t * y t ^ 2) μ₁ :=
    integrable_driving_of_bound (by fun_prop) 1 fun t ht ↦ by
      have ⟨hlo, hhi⟩ := hy t ht
      have hw : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
      rw [abs_of_nonneg (add_nonneg (mul_nonneg hw hlo) (mul_nonneg ht.1.le (sq_nonneg _)))]
      nlinarith only [hhi, mul_nonneg (mul_nonneg ht.1.le hlo) (sub_nonneg.mpr hhi)]
  have hηweighted : (∫ t, (t : ℂ) * η t ^ 2 ∂μ₁).re = 1 / 2 - 8 * (Y - E) := by
    have hcomm : (∫ t, ((t : ℂ) * η t ^ 2).re ∂μ₁) =
        (∫ t, (t : ℂ) * η t ^ 2 ∂μ₁).re := by
      simpa only [Complex.reCLM_apply] using Complex.reCLM.integral_comp_comm hweightedInt
    rw [← hcomm]
    calc
      _ = ∫ t, (t - 8 * (y t - ((1 - t) * y t + t * y t ^ 2))) ∂μ₁ := by
        apply integral_congr_ae
        filter_upwards [ae_mem_driving_interval] with t ht
        have hre : (η t ^ 2).re = 1 - 8 * y t * (1 - y t) := by
          simp only [pow_two, Complex.mul_re, y]
          nlinarith only [hnorm t ht]
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hre]
        ring
      _ = _ := by
        rw [integral_sub (f := fun t ↦ t)
          (g := fun t ↦ 8 * (y t - ((1 - t) * y t + t * y t ^ 2)))
          integrable_driving_id ((hyInt.sub hEInt).const_mul 8), driving_integral_id,
          integral_const_mul, integral_sub hyInt hEInt]
  have ha₃re : a₃.re = a₂.re ^ 2 - a₂.im ^ 2 - 2 * (1 / 2 - 8 * (Y - E)) := by
    have hsq : (a₂ ^ 2).re = a₂.re ^ 2 - a₂.im ^ 2 := by rw [pow_two, Complex.mul_re]; ring
    rw [ha₃, Complex.sub_re, hsq, Complex.mul_re, hηweighted]
    norm_num
  have hdef : 3 - a₃.re = 16 * (E - Y ^ 2) + 4 * ν ^ 2 := by
    rw [ha₃re, ha₂re, ha₂im]
    ring
  have hY' : (∫ t in (0 : ℝ)..1, y t) ≤ 1 / 2 := by
    rwa [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hEst := quadratic_driving_estimates hy_meas hv_meas hy hvsq hY'
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hEst
  obtain ⟨_, hY₀, _, hE, hY₂, hy₂, hv₂, hWeight, hsharp⟩ := hEst
  change 0 ≤ Y ∧ Y ≤ 1 / 2 ∧ E ≤ 65 * (3 - a₃.re) / 16 ∧ Y ^ 2 ≤ E ∧
    (∫ t, y t ^ 2 ∂μ₁) ≤ E ∧ (∫ t, v t ^ 2 ∂μ₁) ≤ 4 * Y ∧
    (∫ t, (1 - t) * v t ^ 2 ∂μ₁) ≤ (3 - a₃.re) / 4 ∧
    ν ^ 2 ≤ (3 - a₃.re) / 4 ∧ a₂.im ^ 2 ≤ 3 - a₃.re
  rw [hdef, ha₂im]
  exact ⟨hY₀, hY, hE, hY₂, hy₂, hv₂, hWeight, by nlinarith only [hsharp], hsharp⟩

/-- The first low-degree estimate under the reverse Löwner formulas for the second and
third coefficients. The sign condition is the one obtained by a half-turn rotation. -/
theorem im_second_sq_le_third_deficit_of_driving_of_nonneg {η : ℝ → ℂ} {a₂ a₃ : ℂ}
    (hη : Measurable η) (hunit : ∀ t ∈ Ioc (0 : ℝ) 1, ‖η t‖ = 1)
    (ha₂ : a₂ = 2 * ∫ t in (0 : ℝ)..1, η t)
    (ha₃ : a₃ = a₂ ^ 2 - 2 * ∫ t in (0 : ℝ)..1, (t : ℂ) * η t ^ 2)
    (ha₂sign : 0 ≤ a₂.re) :
    a₂.im ^ 2 ≤ 3 - a₃.re := by
  obtain ⟨_, _, _, _, _, _, _, _, h⟩ := quadratic_moments_of_unit_driving hη hunit ha₂ ha₃ ha₂sign
  exact h

/-- The first low-degree estimate for coefficients represented by a unit driving function. -/
theorem im_second_sq_le_third_deficit_of_driving {η : ℝ → ℂ} {a₂ a₃ : ℂ}
    (hη : Measurable η) (hunit : ∀ t ∈ Ioc (0 : ℝ) 1, ‖η t‖ = 1)
    (ha₂ : a₂ = 2 * ∫ t in (0 : ℝ)..1, η t)
    (ha₃ : a₃ = a₂ ^ 2 - 2 * ∫ t in (0 : ℝ)..1, (t : ℂ) * η t ^ 2) :
    a₂.im ^ 2 ≤ 3 - a₃.re := by
  by_cases hsign : 0 ≤ a₂.re
  · exact im_second_sq_le_third_deficit_of_driving_of_nonneg hη hunit ha₂ ha₃ hsign
  · have hη' : Measurable (fun t ↦ -η t) := hη.neg
    have hn (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : ‖-η t‖ = 1 := by simpa using hunit t ht
    have ha₂' : -a₂ = 2 * ∫ t in (0 : ℝ)..1, -η t := by
      rw [intervalIntegral.integral_neg, mul_neg, ← ha₂]
    have ha₃' : a₃ = (-a₂) ^ 2 - 2 * ∫ t in (0 : ℝ)..1, (t : ℂ) * (-η t) ^ 2 := by
      simpa only [neg_sq] using ha₃
    have hsign' : 0 ≤ (-a₂).re := by rw [Complex.neg_re]; exact neg_nonneg.mpr (le_of_not_ge hsign)
    simpa only [Complex.neg_im, neg_sq] using
      im_second_sq_le_third_deficit_of_driving_of_nonneg hη' hn ha₂' ha₃' hsign'

end Zalcman
