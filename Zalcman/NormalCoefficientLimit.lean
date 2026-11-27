/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Area
public import Zalcman.CoefficientVelocity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# From coefficient convergence to locally uniform convergence

The growth theorem bounds coefficients uniformly by Cauchy's estimate.
The geometric majorant on a smaller disk converts convergence of individual
coefficients into locally uniform convergence of normalized univalent maps.
-/

public section

namespace Zalcman

open Filter Set
open scoped Topology

private theorem hasSum_coeff_unitDisk {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisk)
    {z : ℂ} (hz : z ∈ unitDisk) : HasSum (fun j : ℕ => coeff f j * z ^ j) (f z) := by
  convert Complex.hasSum_taylorSeries_on_ball hf hz using 1
  funext j
  simp only [coeff, sub_zero, smul_eq_mul]
  ring

/-- A uniform Cauchy bound available before any use of the Milin inequality. -/
theorem norm_coeff_le_of_radius {f : ℂ → ℂ} (hf : NormalizedUnivalent f) {r : ℝ}
    (hr : 0 < r) (hr₁ : r < 1) (n : ℕ) :
    ‖coeff f n‖ ≤ (r / (1 - r) ^ 2) / r ^ n := by
  have h : coeff (fun _ : ℂ => (0 : ℂ)) n = 0 := by simp [coeff]
  have hbound (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) r) :
      ‖f z - (fun _ : ℂ => (0 : ℂ)) z‖ ≤ r / (1 - r) ^ 2 := by
    have hz' : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hzD : z ∈ unitDisk := mem_unitDisk.mpr (hz'.symm ▸ hr₁)
    simpa only [sub_zero, hz'] using upper_growth hf hzD
  simpa only [h, sub_zero] using norm_coeff_sub_le hf.holomorphic
    (differentiableOn_const 0) hr hr₁ hbound n

/-- A simple absolute bound for each fixed normalized coefficient. -/
theorem norm_coeff_le_two_pow_of_normalized {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ) :
    ‖coeff f n‖ ≤ (2 : ℝ) ^ (n + 1) := by
  have h := norm_coeff_le_of_radius hf (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) n
  calc
    _ ≤ ((1 / 2 : ℝ) / (1 - 1 / 2) ^ 2) / (1 / 2) ^ n := h
    _ = _ := by rw [show (1 / 2 : ℝ) / (1 - 1 / 2) ^ 2 = 2 by norm_num,
      one_div, inv_pow, div_inv_eq_mul, pow_succ, mul_comm]

/-- On the normalized univalent class, coefficientwise limits with normalized target
are locally uniform limits on the disk. -/
theorem tendstoLocallyUniformlyOn_of_tendsto_coeff {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ i, NormalizedUnivalent (F i)) (hf : NormalizedUnivalent f)
    (hCoe : ∀ j, Tendsto (fun i => coeff (F i) j) l (𝓝 (coeff f j))) :
    TendstoLocallyUniformlyOn F f l unitDisk := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact unitDisk_isOpen).mpr
  intro K hK hCompact
  rcases Set.eq_empty_or_nonempty K with rfl | hne
  · exact tendstoUniformlyOn_empty
  obtain ⟨z₀, hz₀, hmax⟩ := hCompact.exists_isMaxOn hne
    (continuous_norm : Continuous (norm : ℂ → ℝ)).continuousOn
  let r := ‖z₀‖
  let R := (r + 1) / 2
  let M := 2 * R / (1 - R) ^ 2
  have hr₀ : 0 ≤ r := norm_nonneg _
  have hr₁ : r < 1 := mem_unitDisk.mp (hK hz₀)
  have hR₀ : 0 < R := by dsimp only [R]; linarith
  have hR₁ : R < 1 := by dsimp only [R]; linarith
  have hrR : r < R := by dsimp only [R]; linarith
  have hbound (i : ι) (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) R) : ‖F i z - f z‖ ≤ M := by
    have hzR : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hzD : z ∈ unitDisk := mem_unitDisk.mpr (hzR.symm ▸ hR₁)
    have h1 := upper_growth (hF i) hzD
    have h2 := upper_growth hf hzD
    rw [hzR] at h1 h2
    exact (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq (by dsimp [M]; ring))
  let d (i : ι) (j : ℕ) := coeff (F i) j - coeff f j
  let U (i : ι) (j : ℕ) := ‖d i j‖ * r ^ j
  let B (j : ℕ) := M * (r / R) ^ j
  have hGeo : Summable B :=
    (summable_geometric_of_lt_one (div_nonneg hr₀ hR₀.le) ((div_lt_one hR₀).mpr hrR)).mul_left M
  have hUB (i : ι) (j : ℕ) : U i j ≤ B j := calc
    _ ≤ (M / R ^ j) * r ^ j := mul_le_mul_of_nonneg_right
      (norm_coeff_sub_le (hF i).holomorphic hf.holomorphic hR₀ hR₁ (hbound i) j) (by positivity)
    _ = _ := by
      calc
        M / R ^ j * r ^ j = M * (r ^ j / R ^ j) := by
          rw [div_mul_eq_mul_div, mul_div_assoc]
        _ = M * (r / R) ^ j := congrArg (M * ·) (div_pow r R j).symm
  have hUpos (i : ι) (j : ℕ) : 0 ≤ U i j := mul_nonneg (norm_nonneg _) (pow_nonneg hr₀ _)
  have hUSum (i : ι) : Summable (U i) := hGeo.of_nonneg_of_le (hUpos i) (hUB i)
  have hUlim (j : ℕ) : Tendsto (fun i => U i j) l (𝓝 0) := by
    have h := (hCoe j).sub (tendsto_const_nhds (x := coeff f j))
    simpa only [d, sub_self, U, norm_zero, zero_mul] using h.norm.mul_const (r ^ j)
  have hsumlim : Tendsto (fun i => ∑' j, U i j) l (𝓝 (0 : ℝ)) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hGeo hUlim
      (Eventually.of_forall (fun i j => by rw [Real.norm_of_nonneg (hUpos i j)]; exact hUB i j))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(hsumlim.eventually (Iio_mem_nhds hε))] with i hi
  intro z hz
  have hzD := hK hz
  have hzR : ‖z‖ ≤ r := hmax hz
  have hseries : HasSum (fun j : ℕ => d i j * z ^ j) (F i z - f z) := by
    simpa only [d, sub_mul] using
      (hasSum_coeff_unitDisk (hF i).holomorphic hzD).sub (hasSum_coeff_unitDisk hf.holomorphic hzD)
  have hn (j : ℕ) : ‖d i j * z ^ j‖ ≤ U i j := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hzR _) (norm_nonneg _)
  have hNs : Summable (fun j : ℕ => ‖d i j * z ^ j‖) :=
    (hUSum i).of_nonneg_of_le (fun _ => norm_nonneg _) hn
  rw [dist_comm, dist_eq_norm, ← hseries.tsum_eq]
  exact (norm_tsum_le_tsum_norm hNs).trans_lt ((hNs.tsum_le_tsum hn (hUSum i)).trans_lt hi)

end Zalcman
