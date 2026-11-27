/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.DiskTransition
public import Zalcman.Upstream.Brennan.Distortion
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Time increments of normalized radial chains

The transition map of a nested pair controls their difference on each compact
subdisk by the difference of their conformal radii.
-/

namespace Zalcman

/-- A two-time estimate for a pair with normalized conformal radii exp(s) and exp(t). -/
theorem norm_radial_chain_increment_le {f g phi : ℂ → ℂ} (hg : NormalizedUnivalent g)
    {s t : ℝ} (hst : s < t)
    (hphi : DifferentiableOn ℂ phi unitDisk) (hmap : Set.MapsTo phi unitDisk unitDisk)
    (hzero : phi 0 = 0) (hderiv : deriv phi 0 = (Real.exp (s - t) : ℂ))
    (htransition : Set.EqOn (fun z ↦ (Real.exp s : ℂ) * f z)
      (fun z ↦ (Real.exp t : ℂ) * g (phi z)) unitDisk)
    {r : ℝ} (hr : r < 1) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖(Real.exp t : ℂ) * g z - (Real.exp s : ℂ) * f z‖ ≤
      (2 / (1 - r) ^ 3 * (r * (1 + r) / (1 - r))) * (Real.exp t - Real.exp s) := by
  have hzD : z ∈ unitDisk := mem_unitDisk.mpr (hz.trans_lt hr)
  have hr₀ : 0 ≤ r := (norm_nonneg z).trans hz
  have hclose : Set.MapsTo phi (Metric.ball (0 : ℂ) 1) (Metric.closedBall (0 : ℂ) 1) :=
    fun _ hv ↦ Metric.ball_subset_closedBall (hmap hv)
  have hdist : ‖phi z‖ ≤ ‖z‖ :=
    Complex.norm_le_norm_of_mapsTo_ball hphi hclose hzero (mem_unitDisk.mp hzD)
  have hsch : OAI.Brennan.Schlicht g :=
    ⟨⟨hg.holomorphic, hg.injective⟩, hg.map_zero, hg.deriv_zero⟩
  have hLip := OAI.Brennan.schlicht_lipschitz_bound hsch hr hz (hdist.trans hz)
  have hA : Real.exp (s - t) < 1 := Real.exp_lt_one_iff.mpr (sub_neg.mpr hst)
  have hnear := norm_sub_id_of_disk_transition hphi hmap hzero
    (Real.exp_pos _).le hA hderiv hzD
  have hpoly : ‖z‖ * (1 + ‖z‖) ≤ r * (1 + r) := by
    apply mul_le_mul hz (by linarith only [hz])
    · positivity
    · exact hr₀
  have hrange : ‖z‖ * (1 + ‖z‖) / (1 - ‖z‖) ≤ r * (1 + r) / (1 - r) := by
    exact (div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hr)
      (by linarith only [hz])).trans (div_le_div_of_nonneg_right hpoly (sub_nonneg.mpr hr.le))
  have hgap : 0 ≤ 1 - Real.exp (s - t) := sub_nonneg.mpr hA.le
  have hnear' := hnear.trans (mul_le_mul_of_nonneg_left hrange hgap)
  have hcoef : 0 ≤ 2 / (1 - r) ^ 3 := by positivity
  have htime : Real.exp t * (1 - Real.exp (s - t)) = Real.exp t - Real.exp s := by
    rw [Real.exp_sub, mul_sub, mul_one, mul_comm (Real.exp t) (Real.exp s / Real.exp t),
      div_mul_cancel₀ _ (Real.exp_ne_zero _)]
  have hvalue : (Real.exp s : ℂ) * f z = (Real.exp t : ℂ) * g (phi z) := htransition hzD
  rw [hvalue, ← mul_sub, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp t * (2 / (1 - r) ^ 3 * ‖z - phi z‖) :=
      mul_le_mul_of_nonneg_left hLip (Real.exp_pos _).le
    _ ≤ Real.exp t * (2 / (1 - r) ^ 3 *
          ((1 - Real.exp (s - t)) * (r * (1 + r) / (1 - r)))) := by
      rw [norm_sub_rev]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnear' hcoef) (Real.exp_pos _).le
    _ = _ := by
      rw [← htime]
      ring

end Zalcman
