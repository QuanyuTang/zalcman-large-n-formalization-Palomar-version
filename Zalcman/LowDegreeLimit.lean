/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CoefficientContinuity
import Mathlib.Tactic.Ring

/-!
# Half-turn invariance and continuity of the low-degree deficit estimate

The fourth-order real-part estimate can be proved with nonnegative real second
coefficient on a rotation-closed class, then passed through limits.
-/

public section

namespace Zalcman

open Filter
open scoped Topology

/-- A half-turn preserves the two quantities in the fourth-order estimate. -/
theorem low_degree_quantities_rotate_neg_one (f : ℂ → ℂ) :
    (coeff (rotate (-1) f) 2).re = -(coeff f 2).re ∧
    (coeff (rotate (-1) f) 3).re = (coeff f 3).re ∧
    |(coeff (rotate (-1) f) 4 - 2 * coeff (rotate (-1) f) 2).re| =
      |(coeff f 4 - 2 * coeff f 2).re| := by
  have hu : ‖(-1 : ℂ)‖ = 1 := by simp
  rw [coeff_rotate f hu (show 1 ≤ 2 by decide), coeff_rotate f hu (show 1 ≤ 3 by decide),
    coeff_rotate f hu (show 1 ≤ 4 by decide)]
  norm_num
  rw [show -(coeff f 4).re + 2 * (coeff f 2).re =
    -((coeff f 4).re - 2 * (coeff f 2).re) by ring, abs_neg]

/-- The fourth-order estimate survives locally uniform approximation on the unit disk. -/
theorem abs_re_coeff_four_sub_two_le_of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {C : ℝ}
    (h : TendstoLocallyUniformlyOn F f l unitDisk)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) unitDisk)
    (hB : ∀ᶠ i in l, |(coeff (F i) 4 - 2 * coeff (F i) 2).re| ≤
      C * (3 - (coeff (F i) 3).re)) :
    |(coeff f 4 - 2 * coeff f 2).re| ≤ C * (3 - (coeff f 3).re) := by
  have hs := (tendsto_coeff h hF 4).sub ((tendsto_coeff h hF 2).const_mul (2 : ℂ))
  have hRe := Complex.continuous_re.continuousAt.tendsto.comp hs
  have hLeft := continuous_abs.continuousAt.tendsto.comp hRe
  have hr := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_coeff h hF 3)
  have hRight := ((tendsto_const_nhds (x := (3 : ℝ))).sub hr).const_mul C
  exact le_of_tendsto_of_tendsto hLeft hRight hB

end Zalcman
