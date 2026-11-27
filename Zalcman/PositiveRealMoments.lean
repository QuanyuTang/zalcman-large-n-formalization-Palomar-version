/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Basic
public import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Circle moments of the real part of a holomorphic function

Cauchy's formula computes the analytic term of each positive moment. The
conjugate term has zero circle average by the mean value property.
-/

public section

namespace Zalcman

open Complex Filter MeasureTheory Real Set
open scoped ComplexConjugate Real Topology

private theorem circleAverage_inv_pow_eq_coeff {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 r)) (n : ℕ) :
    circleAverage (fun z ↦ z⁻¹ ^ n * f z) 0 r = coeff f n := by
  rw [circleAverage_eq_circleIntegral hr.ne']
  have hrewrite : (fun z : ℂ ↦ (z - 0)⁻¹ • (z⁻¹ ^ n * f z)) =
      fun z : ℂ ↦ (1 / (z - 0) ^ (n + 1)) • f z := by
    funext z
    simp only [sub_zero, smul_eq_mul, one_div]
    rw [← inv_pow, pow_succ', mul_assoc]
  rw [hrewrite, hf.circleIntegral_one_div_sub_center_pow_smul hr n, coeff]
  have hne : (2 * (π : ℂ) * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  rw [smul_eq_mul, smul_eq_mul, div_eq_mul_inv, ← mul_assoc, ← mul_assoc,
    inv_mul_cancel₀ hne, one_mul]

/-- The circle average of the real part of a holomorphic function is its real part at zero. -/
theorem circleAverage_re_eq_center {f : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 r)) :
    circleAverage (fun z ↦ (f z).re) 0 r = (f 0).re := by
  have hCl : DiffContOnCl ℂ f (Metric.ball 0 |r|) := by
    rw [abs_of_nonneg hr]
    exact (hf.mono Metric.closure_ball_subset_closedBall).diffContOnCl
  have hCi : CircleIntegrable f 0 r :=
    (hf.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable hr
  change circleAverage (Complex.reCLM ∘ f) 0 r = _
  rw [Complex.reCLM.circleAverage_comp_comm hCi, hCl.circleAverage, Complex.reCLM_apply]

/-- The positive moments of the real part carry half the Taylor coefficient. -/
theorem circleAverage_re_inv_pow_succ {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 r)) (n : ℕ) :
    circleAverage (fun z ↦ z⁻¹ ^ (n + 1) * ((f z).re : ℂ)) 0 r = coeff f (n + 1) / 2 := by
  let A : ℂ → ℂ := fun z ↦ z⁻¹ ^ (n + 1) * f z
  let B : ℂ → ℂ := fun z ↦ z⁻¹ ^ (n + 1) * conj (f z)
  let Q : ℂ → ℂ := fun z ↦ (((r : ℂ) ^ 2)⁻¹ * z) ^ (n + 1) * f z
  have hs : Metric.sphere (0 : ℂ) |r| ⊆ Metric.closedBall 0 r := by
    rw [abs_of_nonneg hr.le]
    exact Metric.sphere_subset_closedBall
  have hzNe : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, z ≠ 0 := by
    intro z hz hz₀
    subst z
    have heq : (0 : ℝ) = r := by simpa [Metric.mem_sphere, abs_of_nonneg hr.le] using hz
    exact hr.ne' heq.symm
  have hPow : ContinuousOn (fun z : ℂ ↦ z⁻¹ ^ (n + 1)) (Metric.sphere 0 |r|) :=
    (continuousOn_id.inv₀ hzNe).pow _
  have hA : CircleIntegrable A 0 r :=
    (hPow.mul (hf.continuousOn.mono hs)).circleIntegrable'
  have hB : CircleIntegrable B 0 r :=
    (hPow.mul (Complex.continuous_conj.comp_continuousOn (hf.continuousOn.mono hs))).circleIntegrable'
  have hQD : DifferentiableOn ℂ Q (Metric.closedBall 0 r) := by
    apply DifferentiableOn.mul _ hf
    fun_prop
  have hQCi : CircleIntegrable Q 0 r := (hQD.continuousOn.mono hs).circleIntegrable'
  have hQCl : DiffContOnCl ℂ Q (Metric.ball 0 |r|) := by
    rw [abs_of_nonneg hr.le]
    exact (hQD.mono Metric.closure_ball_subset_closedBall).diffContOnCl
  have hQ₀ : Q 0 = 0 := by simp [Q]
  have hQavg : circleAverage Q 0 r = 0 := hQCl.circleAverage.trans hQ₀
  have hBavg : circleAverage B 0 r = 0 := by
    let L := Complex.conjCLE.toContinuousLinearMap
    have hBconj : EqOn B (L ∘ Q) (Metric.sphere 0 |r|) := by
      intro z hz
      have hzn : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_zero_right, abs_of_nonneg hr.le] using hz
      have hprod : z * conj z = (r : ℂ) ^ 2 := by
        rw [Complex.mul_conj, ← Complex.sq_norm, hzn, Complex.ofReal_pow]
      have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
      have hinv : z⁻¹ = ((r : ℂ) ^ 2)⁻¹ * conj z := by
        apply mul_right_cancel₀ (hzNe z hz)
        rw [inv_mul_cancel₀ (hzNe z hz), mul_assoc, mul_comm (conj z) z, hprod,
          inv_mul_cancel₀ (pow_ne_zero _ hrC)]
      change z⁻¹ ^ (n + 1) * conj (f z) = conj ((((r : ℂ) ^ 2)⁻¹ * z) ^ (n + 1) * f z)
      rw [map_mul, map_pow, map_mul, map_inv₀, map_pow, Complex.conj_ofReal, ← hinv]
    rw [circleAverage_congr_sphere hBconj, L.circleAverage_comp_comm hQCi, hQavg, map_zero]
  have hsplit : (fun z : ℂ ↦ z⁻¹ ^ (n + 1) * ((f z).re : ℂ)) =
      fun z ↦ (1 / 2 : ℂ) • (A z + B z) := by
    funext z
    have hre : (f z + conj (f z)) = (2 : ℂ) * ((f z).re : ℂ) := by
      simpa using Complex.add_conj (f z)
    simp only [smul_eq_mul, A, B, ← mul_add, hre]
    ring
  have hAavg : circleAverage A 0 r = coeff f (n + 1) := circleAverage_inv_pow_eq_coeff hr hf _
  rw [hsplit, circleAverage_fun_smul, circleAverage_fun_add hA hB,
    hAavg, hBavg, add_zero, smul_eq_mul]
  ring

/-- A normalized holomorphic function with nonnegative real part has Taylor
coefficients of modulus at most two in every positive degree. -/
theorem norm_coeff_succ_le_of_nonneg_re {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisk)
    (h₀ : f 0 = 1) (hRe : ∀ z ∈ unitDisk, 0 ≤ (f z).re) (n : ℕ) :
    ‖coeff f (n + 1)‖ ≤ 2 := by
  have haux {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
      ‖coeff f (n + 1)‖ / 2 ≤ r⁻¹ ^ (n + 1) := by
    have hsub : Metric.closedBall (0 : ℂ) r ⊆ unitDisk := Metric.closedBall_subset_ball hr₁
    have hSphere : Metric.sphere (0 : ℂ) |r| ⊆ unitDisk := by
      rw [abs_of_nonneg hr.le]
      exact Metric.sphere_subset_closedBall.trans hsub
    let g : ℂ → ℂ := fun z ↦ z⁻¹ ^ (n + 1) * ((f z).re : ℂ)
    have hnorm : Set.EqOn (fun z ↦ ‖g z‖) (fun z ↦ r⁻¹ ^ (n + 1) • (f z).re)
        (Metric.sphere 0 |r|) := by
      intro z hz
      have hzn : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_zero_right, abs_of_nonneg hr.le] using hz
      change ‖z⁻¹ ^ (n + 1) * ((f z).re : ℂ)‖ = r⁻¹ ^ (n + 1) • (f z).re
      rw [norm_mul, norm_pow, norm_inv, hzn, Complex.norm_of_nonneg (hRe z (hSphere hz)), smul_eq_mul]
    have hAvg := norm_circleAverage_le_circleAverage_norm (f := g) (c := 0) (R := r)
    rw [show circleAverage g 0 r = coeff f (n + 1) / 2 from
        circleAverage_re_inv_pow_succ hr (hf.mono hsub) n,
      norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num,
      circleAverage_congr_sphere hnorm, circleAverage_fun_smul,
      circleAverage_re_eq_center hr.le (hf.mono hsub), h₀, Complex.one_re, smul_eq_mul, mul_one] at hAvg
    exact hAvg
  have hlim : Tendsto (fun r : ℝ ↦ r⁻¹ ^ (n + 1)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun r : ℝ ↦ r⁻¹ ^ (n + 1)) 1 :=
      (continuousAt_id.inv₀ one_ne_zero).pow _
    simpa only [inv_one, one_pow] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hm : ‖coeff f (n + 1)‖ / 2 ≤ 1 := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one))] with r hlt hr
    exact haux hr hlt
  exact (div_le_one (show (0 : ℝ) < 2 by norm_num)).mp hm

end Zalcman
