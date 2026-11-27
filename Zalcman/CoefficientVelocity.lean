/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CoefficientContinuity
public import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Time differences of analytic coefficients

Cauchy's estimate transfers compact-disk bounds to individual coefficients. A locally
uniform time derivative of a holomorphic family gives the derivative of each coefficient.
-/

public section

namespace Zalcman

open Filter
open scoped NNReal Topology

theorem coeff_sub {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisk)
    (hg : DifferentiableOn ℂ g unitDisk) (n : ℕ) :
    coeff (fun z => f z - g z) n = coeff f n - coeff g n := by
  have hf' : ContDiffAt ℂ n f 0 :=
    (hf.analyticAt (unitDisk_isOpen.mem_nhds zero_mem_unitDisk)).contDiffAt
  have hg' : ContDiffAt ℂ n g 0 :=
    (hg.analyticAt (unitDisk_isOpen.mem_nhds zero_mem_unitDisk)).contDiffAt
  unfold coeff
  rw [iteratedDeriv_fun_sub hf' hg', mul_sub]

theorem coeff_const_mul (c : ℂ) (f : ℂ → ℂ) (n : ℕ) :
    coeff (fun z => c * f z) n = c * coeff f n := by
  unfold coeff
  rw [iteratedDeriv_const_mul_field]
  ring

/-- Division by `z` after subtracting the constant term shifts Taylor coefficients. -/
theorem coeff_dslope {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisk) (n : ℕ) :
    coeff f (n + 1) = coeff (dslope f 0) n := by
  let F := dslope f 0
  let K : ℂ → ℂ := fun z ↦ z * F z
  have hF : DifferentiableOn ℂ F unitDisk :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds zero_mem_unitDisk)).mpr hf
  have hF0 : AnalyticAt ℂ F 0 := hF.analyticOnNhd Metric.isOpen_ball _ zero_mem_unitDisk
  have hfK : f = fun z ↦ f 0 + K z := by
    funext z
    have hz := sub_smul_dslope f (0 : ℂ) z
    rw [sub_zero, smul_eq_mul] at hz
    dsimp only [K, F]
    rw [hz]
    ring
  have hD₀ : iteratedDeriv (n + 1) f 0 = iteratedDeriv (n + 1) K 0 := by
    simp only [iteratedDeriv_succ']
    have hd : deriv f = deriv K := calc
      _ = deriv (fun z ↦ f 0 + K z) := congrArg deriv hfK
      _ = _ := deriv_const_add' (f 0)
    rw [hd]
  have hD : iteratedDeriv (n + 1) f 0 = (↑(n + 1) : ℂ) * iteratedDeriv n F 0 := by
    rw [hD₀]
    change iteratedDeriv (n + 1) (fun z ↦ id z * F z) 0 = _
    rw [iteratedDeriv_fun_mul (contDiffAt_id (𝕜 := ℂ)) hF0.contDiffAt, Finset.sum_eq_single 1]
    · simp
    · intro i _ hi
      have hz : iteratedDeriv i id (0 : ℂ) = 0 := by simp [iteratedDeriv_id, hi]
      simp [hz]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  rw [coeff, coeff, hD, Nat.factorial_succ, Nat.cast_mul]
  field_simp
  rfl

/-- Cauchy's estimate for the difference of the `n`th coefficients. -/
theorem norm_coeff_sub_le {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisk)
    (hg : DifferentiableOn ℂ g unitDisk) {r B : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (hB : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z - g z‖ ≤ B) (n : ℕ) :
    ‖coeff f n - coeff g n‖ ≤ B / r ^ n := by
  have hsub : Metric.closedBall (0 : ℂ) r ⊆ unitDisk := by
    intro z hz
    have hz' : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    exact mem_unitDisk.mpr (hz'.trans_lt hr₁)
  have hdiff : DiffContOnCl ℂ (fun z => f z - g z) (Metric.ball (0 : ℂ) r) :=
    ((hf.sub hg).mono (Metric.closure_ball_subset_closedBall.trans hsub)).diffContOnCl
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hdiff hB
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [← coeff_sub hf hg, coeff, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (n.factorial : ℝ)⁻¹ * ((n.factorial : ℝ) * B / r ^ n) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

/-- Uniform Lipschitz dependence on the time parameter over a fixed circle gives Lipschitz
dependence of each Taylor coefficient on the same time set. -/
theorem lipschitzOnWith_coeff {F : ℝ → ℂ → ℂ} {s : Set ℝ} {K r : ℝ≥0}
    (hr : 0 < r) (hr₁ : (r : ℝ) < 1) (hF : ∀ t ∈ s, DifferentiableOn ℂ (F t) unitDisk)
    (hLip : ∀ z ∈ Metric.sphere (0 : ℂ) r, LipschitzOnWith K (fun t => F t z) s) (n : ℕ) :
    LipschitzOnWith (K / r ^ n) (fun t => coeff (F t) n) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht u hu
  have hB (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) r) :
      ‖F t z - F u z‖ ≤ (K : ℝ) * dist t u := by
    simpa only [dist_eq_norm] using (hLip z hz).dist_le_mul t ht u hu
  rw [dist_eq_norm, NNReal.coe_div, NNReal.coe_pow]
  exact (norm_coeff_sub_le (hF t ht) (hF u hu) (by exact_mod_cast hr) hr₁ hB n).trans_eq
    (by ring)

/-- The Taylor coefficient of a locally uniform limit of the real-time slopes is the
real-time derivative of the corresponding Taylor coefficient of the family. -/
theorem hasDerivAt_coeff_of_locallyUniform_slope {F : ℝ → ℂ → ℂ} {g : ℂ → ℂ} {u : ℝ}
    (hF : ∀ t, DifferentiableOn ℂ (F t) unitDisk)
    (h : TendstoLocallyUniformlyOn (fun t z => slope (fun s => F s z) u t)
      g (𝓝[≠] u) unitDisk) (n : ℕ) :
    HasDerivAt (fun t => coeff (F t) n) (coeff g n) u := by
  have hslope (t : ℝ) (z : ℂ) : slope (fun s => F s z) u t =
      ((t - u)⁻¹ : ℝ) * (F t z - F u z) := by
    rw [slope_def_module, Complex.real_smul]
  have hs (t : ℝ) : DifferentiableOn ℂ (fun z => slope (fun s => F s z) u t) unitDisk := by
    simp_rw [hslope]
    exact (differentiableOn_const _).mul ((hF t).sub (hF u))
  have hlimit := tendsto_coeff h (Eventually.of_forall hs) n
  refine hasDerivAt_iff_tendsto_slope.mpr (hlimit.congr (fun t => ?_))
  simp only [hslope, coeff_const_mul, coeff_sub (hF t) (hF u), slope_def_module,
    Complex.real_smul]

end Zalcman
