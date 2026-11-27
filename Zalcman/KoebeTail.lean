/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Area
public import Zalcman.LogarithmicCoefficients
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Error from replacing the terminal map by Koebe

On a compact subdisk, a transition to large conformal radius takes values
near zero. Uniform second-order control then shows that attaching a Koebe
continuation has vanishing effect on the initial function.
-/

public section

namespace Zalcman

open Filter Set
open scoped Asymptotics Topology

/-- The linear Taylor approximation is uniform over the normalized univalent class. -/
theorem NormalizedUnivalent.norm_sub_id_le_sq {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {z : ℂ} (hz : ‖z‖ < 1 / 2) : ‖f z - z‖ ≤ 12 * ‖z‖ ^ 2 := by
  let g (w : ℂ) := f w - w
  have h₀ : g 0 = 0 := by simp [g, hf.map_zero]
  have hsubset : Metric.ball (0 : ℂ) (1 / 2) ⊆ unitDisk :=
    Metric.ball_subset_ball (by norm_num)
  have hhol : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) (1 / 2)) :=
    (hf.holomorphic.sub differentiableOn_id).mono hsubset
  have hMaps : MapsTo g (Metric.ball (0 : ℂ) (1 / 2)) (Metric.closedBall (g 0) 3) := by
    intro w hw
    have hw' : ‖w‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hw
    have h := upper_growth hf (hsubset hw)
    have hbound : ‖w‖ / (1 - ‖w‖) ^ 2 ≤ 2 := calc
      _ ≤ (1 / 2 : ℝ) / (1 / 2) ^ 2 := by gcongr <;> linarith
      _ = _ := by norm_num
    rw [h₀, Metric.mem_closedBall, dist_zero_right]
    exact (norm_sub_le _ _).trans (by linarith only [h.trans hbound, hw'])
  have hfd : HasDerivAt f 1 0 :=
    hf.deriv_zero ▸ (hf.holomorphic.differentiableAt
      (unitDisk_isOpen.mem_nhds zero_mem_unitDisk)).hasDerivAt
  have hd : HasDerivAt g 0 0 := by
    simpa only [g, id, sub_self] using hfd.fun_sub (hasDerivAt_id (0 : ℂ))
  have hsmall : (fun w => g w - g 0) =o[𝓝 0] (fun w => ‖w - 0‖ ^ (1 : ℕ)) := by
    simpa only [zero_smul, smul_zero, sub_zero, pow_one] using hd.isLittleO.norm_right
  have hzball : z ∈ Metric.ball (0 : ℂ) (1 / 2) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have h := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hhol hMaps hsmall hzball
  simp only [h₀, dist_zero_right] at h
  dsimp only [g] at h
  exact h.trans_eq (by ring)

/-- A transition to radius `exp T` controls the error of replacing its endpoint by Koebe. -/
theorem koebe_tail_norm_sub_le {f g φ : ℂ → ℂ} (hg : NormalizedUnivalent g)
    {T : ℝ} {z : ℂ} (hφ : φ z ∈ unitDisk)
    (he : f z = (Real.exp T : ℂ) * g (φ z))
    (hsmall : 4 * Real.exp (-T) * ‖f z‖ < 1 / 2) :
    ‖(Real.exp T : ℂ) * koebe (φ z) - f z‖ ≤ 384 * Real.exp (-T) * ‖f z‖ ^ 2 := by
  have hnorm : ‖f z‖ = Real.exp T * ‖g (φ z)‖ := by
    rw [he, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have hcancel : Real.exp (-T) * Real.exp T = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hsmall' : ‖φ z‖ ≤ 4 * Real.exp (-T) * ‖f z‖ := by
    rw [hnorm, ← mul_assoc (4 * Real.exp (-T)), mul_assoc 4, hcancel, mul_one]
    linarith only [lower_growth hg hφ]
  have hp : ‖φ z‖ < 1 / 2 := hsmall'.trans_lt hsmall
  have hdiff : ‖koebe (φ z) - g (φ z)‖ ≤ 24 * ‖φ z‖ ^ 2 := calc
    _ = ‖(koebe (φ z) - φ z) + (φ z - g (φ z))‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖koebe (φ z) - φ z‖ + ‖g (φ z) - φ z‖ := by
      simpa only [norm_sub_rev _ (g (φ z))] using norm_add_le (koebe (φ z) - φ z) (φ z - g (φ z))
    _ ≤ _ := by
      linarith only [koebe_normalizedUnivalent.norm_sub_id_le_sq hp, hg.norm_sub_id_le_sq hp]
  rw [show (Real.exp T : ℂ) * koebe (φ z) - f z =
    (Real.exp T : ℂ) * (koebe (φ z) - g (φ z)) by rw [he, mul_sub],
    norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp T * (24 * ‖φ z‖ ^ 2) := mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
    _ ≤ Real.exp T * (24 * (4 * Real.exp (-T) * ‖f z‖) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hsmall' 2) (by norm_num)) (Real.exp_pos _).le
    _ = 384 * (Real.exp (-T) * Real.exp T) * Real.exp (-T) * ‖f z‖ ^ 2 := by ring
    _ = _ := by rw [hcancel, mul_one]

/-- The initial map after a Koebe continuation is normalized and univalent. -/
theorem normalizedUnivalent_koebe_tail {φ : ℂ → ℂ} {T : ℝ}
    (hφ : DifferentiableOn ℂ φ unitDisk) (hφm : MapsTo φ unitDisk unitDisk)
    (hφi : InjOn φ unitDisk) (hφ₀ : φ 0 = 0) (hφd : deriv φ 0 = (Real.exp (-T) : ℂ)) :
    NormalizedUnivalent (fun z => (Real.exp T : ℂ) * koebe (φ z)) := by
  have hk := koebe_normalizedUnivalent
  refine ⟨(differentiableOn_const _).mul (hk.holomorphic.comp hφ hφm), ?_, ?_, ?_⟩
  · intro z hz w hw he
    exact hφi hz hw (hk.injective (hφm hz) (hφm hw)
      (mul_left_cancel₀ (by exact_mod_cast Real.exp_ne_zero T) he))
  · simp [hφ₀, hk.map_zero]
  · have hφ' := (hφ.differentiableAt (unitDisk_isOpen.mem_nhds zero_mem_unitDisk)).hasDerivAt
    have hk' : HasDerivAt koebe 1 (φ 0) := by
      simpa only [hφ₀, hk.deriv_zero] using (hk.holomorphic.differentiableAt
        (unitDisk_isOpen.mem_nhds zero_mem_unitDisk)).hasDerivAt
    have h := (hk'.comp 0 hφ').const_mul (Real.exp T : ℂ)
    have hc : (Real.exp T : ℂ) * (Real.exp (-T) : ℂ) = 1 := by
      exact_mod_cast (show Real.exp T * Real.exp (-T) = 1 by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero])
    simpa only [Function.comp_def, one_mul, hφd, hc] using h.deriv

/-- Koebe continuations at large time approximate the initial map locally uniformly. -/
theorem tendstoLocallyUniformlyOn_koebe_tail {f : ℂ → ℂ} {g φ : ℝ → ℂ → ℂ}
    (hf : ContinuousOn f unitDisk)
    (hg : ∀ᶠ T : ℝ in atTop, NormalizedUnivalent (g T))
    (hφ : ∀ᶠ T : ℝ in atTop, MapsTo (φ T) unitDisk unitDisk)
    (he : ∀ᶠ T : ℝ in atTop, EqOn f (fun z => (Real.exp T : ℂ) * g T (φ T z)) unitDisk) :
    TendstoLocallyUniformlyOn (fun (T : ℝ) z => (Real.exp T : ℂ) * koebe (φ T z)) f atTop unitDisk := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact unitDisk_isOpen).mpr
  intro S hS hcompact
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn (hf.mono hS)
  let B := max 1 M
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hExp (C : ℝ) : Tendsto (fun T : ℝ => C * Real.exp (-T)) atTop (𝓝 0) := by
    simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  have hnear : ∀ᶠ T : ℝ in atTop, (4 * B) * Real.exp (-T) < 1 / 2 :=
    (hExp (4 * B)).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have herr : ∀ᶠ T : ℝ in atTop, (384 * B ^ 2) * Real.exp (-T) < ε :=
    (hExp (384 * B ^ 2)).eventually (Iio_mem_nhds hε)
  filter_upwards [hg, hφ, he, hnear, herr] with T hgT hφT heT hnearT herrT
  intro z hz
  have hzB : ‖f z‖ ≤ B := (hM z hz).trans (le_max_right _ _)
  have hlocal : 4 * Real.exp (-T) * ‖f z‖ < 1 / 2 :=
    (mul_le_mul_of_nonneg_left hzB (by positivity)).trans_lt
      (by convert hnearT using 1; ring)
  rw [dist_comm, dist_eq_norm]
  calc
    _ ≤ 384 * Real.exp (-T) * ‖f z‖ ^ 2 :=
      koebe_tail_norm_sub_le hgT (hφT (hS hz)) (heT (hS hz)) hlocal
    _ ≤ 384 * Real.exp (-T) * B ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hzB 2) (by positivity)
    _ < ε := by convert herrT using 1; ring

end Zalcman
