/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.LowDegreeLimit
public import Zalcman.PointDriverDensity
import Zalcman.CoefficientBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Passing the low-degree estimate through finite driver approximation

Positive real second coefficient is preserved eventually. A half-turn
handles the negative case, and the zero case follows from the area bound.
-/

public section

namespace Zalcman

open Filter
open scoped Topology

/-- A uniform quartic estimate for finite driver chains gives the same kind
of estimate for every normalized univalent function. -/
theorem exists_quartic_bound_of_finite_driver_estimate {C : ℝ} (hC : 0 ≤ C)
    (hm : ∀ {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ), 0 ≤ (milinCoefficients hf).milinSum n)
    (hFinite : ∀ P : FiniteKoebeDriverChain, 0 < (coeff (P.chain.maps 0) 2).re →
      |(coeff (P.chain.maps 0) 4 - 2 * coeff (P.chain.maps 0) 2).re| ≤
        C * (3 - (coeff (P.chain.maps 0) 3).re)) :
    ∃ C' > 0, ∀ {f : ℂ → ℂ}, NormalizedUnivalent f →
      |(coeff f 4 - 2 * coeff f 2).re| ≤ C' * (3 - (coeff f 3).re) := by
  let C' := max C 4
  have hC' : 0 < C' := (by norm_num : (0 : ℝ) < 4).trans_le (le_max_right _ _)
  have hNonneg {f : ℂ → ℂ} (hf : NormalizedUnivalent f) : 0 ≤ 3 - (coeff f 3).re := by
    have h := norm_coeff_le_of_milinSum_nonneg hf (hm hf 3)
    exact sub_nonneg.mpr ((Complex.re_le_norm _).trans (by simpa only [Nat.cast_ofNat] using h))
  have hPos {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (h₂ : 0 < (coeff f 2).re) :
      |(coeff f 4 - 2 * coeff f 2).re| ≤ C' * (3 - (coeff f 3).re) := by
    obtain ⟨P, hP⟩ := exists_locallyUniform_finiteKoebeDriverChain hf
    have hd : ∀ᶠ i : ℕ in atTop, DifferentiableOn ℂ ((P i).chain.maps 0) unitDisk :=
      .of_forall fun i ↦ (P i).normalized_initial.holomorphic
    have ht := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_coeff hP hd 2)
    have hEventually := ht.eventually (Ioi_mem_nhds h₂)
    have he := abs_re_coeff_four_sub_two_le_of_tendsto hP hd
      (hEventually.mono fun i hi ↦ hFinite (P i) hi)
    exact he.trans (mul_le_mul_of_nonneg_right (le_max_left C 4) (hNonneg hf))
  refine ⟨C', hC', ?_⟩
  intro f hf
  rcases lt_trichotomy (coeff f 2).re 0 with hneg | hzero | hpos
  · obtain ⟨h₂, h₃, h₄⟩ := low_degree_quantities_rotate_neg_one f
    have hg := rotate_normalizedUnivalent hf (show ‖(-1 : ℂ)‖ = 1 by simp)
    have h := hPos hg (by rw [h₂]; exact neg_pos.mpr hneg)
    rw [h₄, h₃] at h
    exact h
  · have hArea := norm_coeff_two_sq_sub_coeff_three_le hf
    have hRe := neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hArea)
    simp only [pow_two, Complex.sub_re, Complex.mul_re, hzero, zero_mul] at hRe
    have hd : 2 ≤ 3 - (coeff f 3).re := by nlinarith only [hRe, sq_nonneg (coeff f 2).im]
    have hb : ‖coeff f 4‖ ≤ 4 := by
      simpa only [Nat.cast_ofNat] using norm_coeff_le_of_milinSum_nonneg hf (hm hf 4)
    have hq := norm_coeff_two_le hf
    have hL : |(coeff f 4 - 2 * coeff f 2).re| ≤ 8 := calc
      _ ≤ ‖coeff f 4 - 2 * coeff f 2‖ := Complex.abs_re_le_norm _
      _ ≤ ‖coeff f 4‖ + ‖2 * coeff f 2‖ := norm_sub_le _ _
      _ ≤ 8 := by rw [norm_mul, Complex.norm_ofNat]; linarith only [hb, hq]
    exact hL.trans (by
      have h := mul_le_mul (le_max_right C 4) hd (by norm_num : (0 : ℝ) ≤ 2) hC'.le
      norm_num at h
      exact h)
  · exact hPos hf hpos

end Zalcman
