/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.FourthOrderKernel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integral domination of the fourth-order mixed remainder
-/

public section

namespace Zalcman

open MeasureTheory Set

/-- The mixed triangular error is bounded by products of one-dimensional means. -/
theorem abs_fourth_order_remainder_integral_le {y v : ℝ → ℝ} {R : ℝ → ℝ → ℝ}
    (hy : IntervalIntegrable y volume 0 1) (hv : IntervalIntegrable v volume 0 1)
    (hyv : IntervalIntegrable (fun t ↦ y t * |v t|) volume 0 1)
    (hy₀ : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ y t)
    (hInner : ∀ t ∈ Ioo (0 : ℝ) 1, IntervalIntegrable (fun s ↦ R s t) volume 0 t)
    (hOuter : IntervalIntegrable (fun t ↦ ∫ s in (0 : ℝ)..t, R s t) volume 0 1)
    (hR : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Ioo (0 : ℝ) t,
      |R s t| ≤ 512 * y s * y t + 48 * y s * |v s| * |v t| + 32 * y t * |v s| * |v t|) :
    |∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, R s t| ≤
      512 * (∫ t in (0 : ℝ)..1, y t) ^ 2 +
        80 * (∫ t in (0 : ℝ)..1, y t * |v t|) * (∫ t in (0 : ℝ)..1, |v t|) := by
  let Y := ∫ t in (0 : ℝ)..1, y t
  let I := ∫ t in (0 : ℝ)..1, |v t|
  let M := ∫ t in (0 : ℝ)..1, y t * |v t|
  have hypos : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] y :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ hy₀)
  have hyvpos : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] (fun t ↦ y t * |v t|) :=
    hypos.mono fun t ht ↦ mul_nonneg ht (abs_nonneg _)
  have hBound (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      |∫ s in (0 : ℝ)..t, R s t| ≤ (512 * Y) * y t + (48 * M) * |v t| + (32 * I) * (y t * |v t|) := by
    have hty : 0 ≤ y t := hy₀ t ⟨ht.1, ht.2.le⟩
    have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
      rw [uIcc_of_le ht.1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc_right ht.2.le
    let A := 512 * y t
    let B := 48 * |v t|
    let C := 32 * y t * |v t|
    have hA : 0 ≤ A := mul_nonneg (by norm_num) hty
    have hB : 0 ≤ B := mul_nonneg (by norm_num) (abs_nonneg _)
    have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by norm_num) hty) (abs_nonneg _)
    have hya := (hy.mono_set hsub).const_mul A
    have hyvb := (hyv.mono_set hsub).const_mul B
    have hvc := (hv.abs.mono_set hsub).const_mul C
    calc
      _ ≤ ∫ s in (0 : ℝ)..t, |R s t| := intervalIntegral.abs_integral_le_integral_abs ht.1.le
      _ ≤ ∫ s in (0 : ℝ)..t, A * y s + B * (y s * |v s|) + C * |v s| := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo ht.1.le (hInner t ht).abs
          ((hya.add hyvb).add hvc)
        intro s hs
        have h := hR t ht s hs
        change |R s t| ≤ A * y s + B * (y s * |v s|) + C * |v s|
        dsimp only [A, B, C]
        nlinarith only [h]
      _ = A * (∫ s in (0 : ℝ)..t, y s) + B * (∫ s in (0 : ℝ)..t, y s * |v s|) +
          C * (∫ s in (0 : ℝ)..t, |v s|) := by
        rw [intervalIntegral.integral_add (hya.add hyvb) hvc, intervalIntegral.integral_add hya hyvb]
        simp only [intervalIntegral.integral_const_mul]
      _ ≤ A * Y + B * M + C * I := by
        refine add_le_add (add_le_add (mul_le_mul_of_nonneg_left ?_ hA)
          (mul_le_mul_of_nonneg_left ?_ hB)) (mul_le_mul_of_nonneg_left ?_ hC)
        · exact intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2.le hypos hy
        · exact intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2.le hyvpos hyv
        · exact intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2.le
            (ae_of_all _ fun _ ↦ abs_nonneg _) hv.abs
      _ = _ := by dsimp only [A, B, C]; ring
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, |∫ s in (0 : ℝ)..t, R s t| :=
      intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, (512 * Y) * y t + (48 * M) * |v t| + (32 * I) * (y t * |v t|) := by
      exact intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hOuter.abs
        (((hy.const_mul _).add (hv.abs.const_mul _)).add (hyv.const_mul _)) hBound
    _ = _ := by
      rw [intervalIntegral.integral_add ((hy.const_mul (512 * Y)).add (hv.abs.const_mul (48 * M)))
        (hyv.const_mul (32 * I)), intervalIntegral.integral_add (hy.const_mul (512 * Y))
        (hv.abs.const_mul (48 * M))]
      simp only [intervalIntegral.integral_const_mul]
      change (512 * Y) * Y + (48 * M) * I + (32 * I) * M = 512 * Y ^ 2 + 80 * M * I
      ring

/-- The quadratic energy controls the product of mixed first moments. -/
theorem mixed_fourth_order_moments_le {y v : ℝ → ℝ} {E : ℝ}
    (hy : IntervalIntegrable y volume 0 1) (hv : IntervalIntegrable v volume 0 1)
    (hy₂ : IntervalIntegrable (fun t ↦ y t ^ 2) volume 0 1)
    (hv₂ : IntervalIntegrable (fun t ↦ v t ^ 2) volume 0 1)
    (hy₀ : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ y t)
    (hY₂ : (∫ t in (0 : ℝ)..1, y t) ^ 2 ≤ E)
    (hEY : (∫ t in (0 : ℝ)..1, y t ^ 2) ≤ E)
    (hVY : (∫ t in (0 : ℝ)..1, v t ^ 2) ≤ 4 * (∫ t in (0 : ℝ)..1, y t)) :
    (∫ t in (0 : ℝ)..1, y t * |v t|) * (∫ t in (0 : ℝ)..1, |v t|) ≤ 4 * E := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let Y := ∫ t in (0 : ℝ)..1, y t
  let I := ∫ t in (0 : ℝ)..1, |v t|
  let M := ∫ t in (0 : ℝ)..1, y t * |v t|
  let V₂ := ∫ t in (0 : ℝ)..1, v t ^ 2
  have hypos : 0 ≤ᵐ[μ] y := (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ hy₀)
  have hY₀ : 0 ≤ Y := by
    unfold Y
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact integral_nonneg_of_ae hypos
  have hE₀ : 0 ≤ E := (sq_nonneg _).trans hY₂
  have hV₂₀ : 0 ≤ V₂ := intervalIntegral.integral_nonneg_of_forall zero_le_one fun _ ↦ sq_nonneg _
  have hyMem : MemLp y (ENNReal.ofReal 2) μ := by
    have h := (memLp_two_iff_integrable_sq hy.1.aestronglyMeasurable).mpr hy₂.1
    simpa using h
  have hvMem : MemLp (fun t ↦ |v t|) (ENNReal.ofReal 2) μ := by
    have hvAbsSq : Integrable (fun t ↦ |v t| ^ 2) μ := by
      have hvSq : Integrable (fun t ↦ v t ^ 2) μ := hv₂.1.integrable
      simpa only [sq_abs] using hvSq
    have h := (memLp_two_iff_integrable_sq hv.abs.1.aestronglyMeasurable).mpr hvAbsSq
    simpa using h
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hypos
    (ae_of_all μ fun t ↦ abs_nonneg (v t)) hyMem hvMem
  have hM : M ≤ Real.sqrt E * Real.sqrt V₂ := by
    have h : M ≤ Real.sqrt (∫ t in (0 : ℝ)..1, y t ^ 2) * Real.sqrt V₂ := by
      simpa only [M, V₂, intervalIntegral.integral_of_le zero_le_one, Real.rpow_two,
        ← Real.sqrt_eq_rpow, sq_abs] using hCS
    exact h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hEY) (Real.sqrt_nonneg _))
  have hI₀ : 0 ≤ I := intervalIntegral.integral_nonneg_of_forall zero_le_one fun _ ↦ abs_nonneg _
  have hI : I ≤ Real.sqrt V₂ := by
    have h := unit_intervalIntegral_sq_le_integral_sq hv.abs
      (show IntervalIntegrable (fun t ↦ |v t| ^ 2) volume 0 1 by simpa only [sq_abs] using hv₂)
    have h' : I ^ 2 ≤ V₂ := by simpa only [I, V₂, sq_abs] using h
    apply (sq_le_sq₀ hI₀ (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hV₂₀]
    exact h'
  have hY : Y ≤ Real.sqrt E := by
    apply (sq_le_sq₀ hY₀ (Real.sqrt_nonneg _)).mp
    rwa [Real.sq_sqrt hE₀]
  change M * I ≤ 4 * E
  calc
    _ ≤ (Real.sqrt E * Real.sqrt V₂) * Real.sqrt V₂ :=
      mul_le_mul hM hI hI₀ (by positivity)
    _ = Real.sqrt E * V₂ := by rw [mul_assoc, Real.mul_self_sqrt hV₂₀]
    _ ≤ Real.sqrt E * (4 * Y) := mul_le_mul_of_nonneg_left hVY (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt E * (4 * Real.sqrt E) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY (by norm_num)) (Real.sqrt_nonneg _)
    _ = _ := by nlinarith only [Real.sq_sqrt hE₀]

end Zalcman
