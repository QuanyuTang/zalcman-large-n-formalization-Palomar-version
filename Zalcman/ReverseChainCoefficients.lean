/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.FiniteDriverContinuation
public import Zalcman.ReverseRadialTime
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Reverse radial coefficient equations

A finite driver chain continued by Koebe becomes constant for sufficiently
small reverse time. Away from the images of the finite seams, the ordinary
chain rule gives the differential equations through degree four.
-/

public section

namespace Zalcman

open Filter Finset MeasureTheory Set
open scoped BigOperators NNReal Topology

/-- Degree \(n+1\) at the original time, after exponential normalization. -/
@[expose] noncomputable def FiniteKoebeDriverChain.scaledCoeff
    (P : FiniteKoebeDriverChain) (n : ℕ) (u : ℝ) : ℂ :=
  coeff (fun z ↦ (Real.exp (-u) : ℂ) * P.chain.koebeContinuation u z) (n + 1)

/-- Degree \(n+1\) in reverse radial time. -/
@[expose] noncomputable def FiniteKoebeDriverChain.reverseCoeff
    (P : FiniteKoebeDriverChain) (n : ℕ) : ℝ → ℂ :=
  reverseRadialPath (P.scaledCoeff n) ((n : ℂ) + 1)

/-- The reversed unit-circle driver, including the Koebe continuation. -/
@[expose] noncomputable def FiniteKoebeDriverChain.reverseDriver
    (P : FiniteKoebeDriverChain) (t : ℝ) : ℂ :=
  if Real.exp (-P.duration) < t then -P.driver (-Real.log t) else 1

theorem FiniteKoebeDriverChain.measurable_reverseDriver (P : FiniteKoebeDriverChain) :
    Measurable P.reverseDriver := by
  have h : Measurable (fun t : ℝ ↦ -P.driver (-Real.log t)) :=
    (P.measurable_driver.comp Real.measurable_log.neg).neg
  exact Measurable.ite (measurableSet_Ioi (a := Real.exp (-P.duration))) h measurable_const

theorem FiniteKoebeDriverChain.norm_reverseDriver (P : FiniteKoebeDriverChain) (t : ℝ) :
    ‖P.reverseDriver t‖ = 1 := by
  by_cases ht : Real.exp (-P.duration) < t
  · simp only [reverseDriver, ite_eq_left ht, norm_neg, P.norm_driver]
  · simp only [reverseDriver, ite_eq_right ht, norm_one]

private theorem coeff_koebe_succ (n : ℕ) : coeff koebe (n + 1) = (n : ℂ) + 1 := by
  have hrotate : rotate (1 : ℂ) koebe = koebe := by
    funext z
    simp [rotate]
  simpa only [hrotate, one_pow, mul_one, Nat.cast_succ] using
    coeff_rotate_koebe (lam := (1 : ℂ)) (by simp) (n := n + 1) (by omega)

private theorem FiniteKoebeDriverChain.scaledCoeff_eq_koebe
    (P : FiniteKoebeDriverChain) (n : ℕ) {u : ℝ} (hu : P.duration ≤ u) :
    P.scaledCoeff n u = (n : ℂ) + 1 := by
  have hG : EqOn (P.chain.koebeContinuation u)
      (fun z ↦ (Real.exp u : ℂ) * koebe z) unitDisk := by
    rcases lt_or_eq_of_le hu with hlt | rfl
    · intro z _
      exact congrFun (P.chain.koebeContinuation_eq_koebe (fun hx ↦ hlt.not_ge hx.2)) z
    · rw [P.chain.koebeContinuation_eq ⟨P.duration_pos.le, le_rfl⟩]
      exact P.chain.terminal
  have hCancel : (Real.exp (-u) : ℂ) * (Real.exp u : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  have hScale : EqOn (fun z ↦ (Real.exp (-u) : ℂ) * P.chain.koebeContinuation u z)
      koebe unitDisk := by
    intro z hz
    change (Real.exp (-u) : ℂ) * P.chain.koebeContinuation u z = koebe z
    have hGz : P.chain.koebeContinuation u z = (Real.exp u : ℂ) * koebe z := hG hz
    rw [hGz, ← mul_assoc, hCancel, one_mul]
  exact (coeff_congr_on_unitDisk hScale (n + 1)).trans (coeff_koebe_succ n)

theorem FiniteKoebeDriverChain.reverseCoeff_at_zero
    (P : FiniteKoebeDriverChain) (n : ℕ) :
    P.reverseCoeff n 0 = (n : ℂ) + 1 := by
  simp [reverseCoeff, reverseRadialPath]

theorem FiniteKoebeDriverChain.reverseCoeff_at_one
    (P : FiniteKoebeDriverChain) (n : ℕ) :
    P.reverseCoeff n 1 = coeff (P.chain.maps 0) (n + 1) := by
  simp only [reverseCoeff, reverseRadialPath, ite_eq_left zero_lt_one, Real.log_one, neg_zero,
    scaledCoeff, Real.exp_zero, Complex.ofReal_one, one_mul,
    P.chain.koebeContinuation_eq ⟨le_rfl, P.duration_pos.le⟩]

theorem FiniteKoebeDriverChain.reverseCoeff_degree_one
    (P : FiniteKoebeDriverChain) (t : ℝ) : P.reverseCoeff 0 t = 1 := by
  have h (u : ℝ) : P.scaledCoeff 0 u = 1 := by
    have hu := (P.chain.koebeContinuation_map u).normalizedUnivalent
    simpa only [scaledCoeff, Nat.zero_add, coeff_one] using hu.deriv_zero
  by_cases ht : 0 < t
  · simp only [reverseCoeff, reverseRadialPath, ite_eq_left ht, h]
  · simp only [reverseCoeff, reverseRadialPath, ite_eq_right ht, Nat.cast_zero, zero_add]

theorem FiniteKoebeDriverChain.absolutelyContinuous_reverseCoeff
    (P : FiniteKoebeDriverChain) (n : ℕ) :
    AbsolutelyContinuousOnInterval (P.reverseCoeff n) 0 1 := by
  let r : ℝ≥0 := 1 / 2
  have hr : 0 < r := by norm_num [r]
  have hr' : (r : ℝ) < 1 := by norm_num [r]
  let G := P.chain.koebeContinuation
  have hG t := P.chain.koebeContinuation_map t
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_nested_chain (T := P.duration)
    (NNReal.coe_nonneg r) hr'
    (fun t _ ↦ (hG t).holomorphic) (fun t _ ↦ (hG t).injective)
    (fun t _ ↦ (hG t).map_zero) (fun t _ ↦ (hG t).deriv_zero)
    (fun _ hs _ ht hst ↦ P.chain.koebeContinuation_nested P.duration_pos.le hs ht hst)
  have hLip : ∀ z ∈ Metric.sphere (0 : ℂ) r,
      LipschitzOnWith K (fun t ↦ G t z) (Icc 0 P.duration) := by
    intro z hz
    have hz' : ‖z‖ = (r : ℝ) := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    exact hK z hz'.le
  obtain ⟨K', hK'⟩ := exists_lipschitzOnWith_exp_normalization P.duration_pos.le hr'
    (hG 0).holomorphic.continuousOn hLip
  have hB := lipschitzOnWith_coeff hr hr'
    (fun t _ ↦ (hG t).holomorphic.const_mul _) hK' (n + 1)
  exact absolutelyContinuousOnInterval_reverseRadialPath P.duration_pos.le hB
    (fun u hu ↦ P.scaledCoeff_eq_koebe n hu)

private theorem FiniteKoebeDriverChain.reverseCoeff_small
    (P : FiniteKoebeDriverChain) (n : ℕ) {t : ℝ} (ht₀ : 0 < t)
    (ht : t < Real.exp (-P.duration)) : P.reverseCoeff n t = (n : ℂ) + 1 := by
  have h := Real.log_lt_log ht₀ ht
  rw [Real.log_exp] at h
  rw [reverseCoeff, reverseRadialPath, ite_eq_left ht₀]
  have htime : P.duration < -Real.log t := by simpa only [neg_neg] using neg_lt_neg h
  exact P.scaledCoeff_eq_koebe n htime.le

private theorem FiniteKoebeDriverChain.hasDerivAt_reverseCoeff_small
    (P : FiniteKoebeDriverChain) (n : ℕ) {t : ℝ} (ht₀ : 0 < t)
    (ht : t < Real.exp (-P.duration)) : HasDerivAt (P.reverseCoeff n) 0 t := by
  have hNear : ∀ᶠ s in 𝓝 t, s ∈ Ioo 0 (Real.exp (-P.duration)) := Ioo_mem_nhds ht₀ ht
  exact (hasDerivAt_const t ((n : ℂ) + 1)).congr_of_eventuallyEq
    (hNear.mono fun _ hs ↦ P.reverseCoeff_small n hs.1 hs.2)

private theorem FiniteKoebeDriverChain.hasDerivAt_reverseCoeff_large
    (P : FiniteKoebeDriverChain) (n : ℕ) {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1)
    (ht : Real.exp (-P.duration) < t) (hSeam : -Real.log t ∉ P.chain.seams) :
    HasDerivAt (P.reverseCoeff n)
      ((-(n : ℂ) * P.reverseCoeff n t - 2 *
        ∑ j ∈ range n, ((j : ℂ) + 1) * P.reverseCoeff j t * (-P.reverseDriver t) ^ (n - j)) /
        (t : ℂ)) t := by
  let u := -Real.log t
  have hu₀ : 0 < u := neg_pos.mpr (Real.log_neg ht₀ ht₁)
  have huT : u < P.duration := by
    have h := Real.log_lt_log (Real.exp_pos _) ht
    rw [Real.log_exp] at h
    simpa only [neg_neg] using neg_lt_neg h
  obtain ⟨hκ, hS⟩ := P.chain.koebeContinuation_velocity_off_seams ⟨hu₀, huT⟩ hSeam
  have hU : HasDerivAt (fun s : ℝ ↦ -Real.log s) (-t⁻¹) t :=
    (Real.hasDerivAt_log ht₀.ne').fun_neg
  have hB : HasDerivAt (P.scaledCoeff n)
        ((n : ℂ) * P.scaledCoeff n u + 2 *
          ∑ j ∈ range n, ((j : ℂ) + 1) * P.scaledCoeff j u * P.driver u ^ (n - j)) u :=
    hasDerivAt_radialTaylorCoeff_exp_normalization hκ.le
      (fun s ↦ (P.chain.koebeContinuation_map s).holomorphic) hS n
  have hEq : P.reverseCoeff n =ᶠ[𝓝 t] P.scaledCoeff n ∘ (fun s ↦ -Real.log s) := by
    filter_upwards [Ioi_mem_nhds ht₀] with s hs
    simp only [reverseCoeff, reverseRadialPath, ite_eq_left (show 0 < s from hs), Function.comp_apply]
  have hD := (hB.scomp_of_eq t hU rfl).congr_of_eventuallyEq hEq
  have hb (j : ℕ) : P.reverseCoeff j t = P.scaledCoeff j u := by
    simp only [reverseCoeff, reverseRadialPath, ite_eq_left ht₀, u]
  have hη : P.driver u = -P.reverseDriver t := by
    simp only [reverseDriver, ite_eq_left ht, neg_neg, u]
  convert hD using 1
  simp only [← hb, hη, Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_inv, div_eq_mul_inv]
  ring

/-- The second, third and fourth reverse radial coefficient equations hold
almost everywhere on \([0,1]\), including the interval where the chain is Koebe. -/
theorem FiniteKoebeDriverChain.ae_reverseCoeff_eqs (P : FiniteKoebeDriverChain) :
    ∀ᵐ t : ℝ ∂volume, t ∈ uIoc (0 : ℝ) 1 →
      HasDerivAt (P.reverseCoeff 1) ((-P.reverseCoeff 1 t + 2 * P.reverseDriver t) / (t : ℂ)) t ∧
      HasDerivAt (P.reverseCoeff 2)
        ((-2 * P.reverseCoeff 2 t + 4 * P.reverseDriver t * P.reverseCoeff 1 t -
          2 * P.reverseDriver t ^ 2) / (t : ℂ)) t ∧
      HasDerivAt (P.reverseCoeff 3)
        ((-3 * P.reverseCoeff 3 t + 6 * P.reverseDriver t * P.reverseCoeff 2 t -
          4 * P.reverseDriver t ^ 2 * P.reverseCoeff 1 t + 2 * P.reverseDriver t ^ 3) / (t : ℂ)) t := by
  classical
  let a := Real.exp (-P.duration)
  let bad := insert 1 (insert a (P.chain.seams.image (fun u ↦ Real.exp (-u))))
  filter_upwards [bad.finite_toSet.countable.ae_notMem (volume : Measure ℝ)] with t hNot ht
  rw [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at ht
  have hNot' : t ∉ bad := hNot
  have h₁ : t ≠ 1 := fun h ↦ hNot' (by simp [bad, h])
  have ht₁ := lt_of_le_of_ne ht.2 h₁
  have hCut : t ≠ a := fun h ↦ hNot' (by simp [bad, h])
  rcases lt_or_gt_of_ne hCut with hsmall | hlarge
  · have hη : P.reverseDriver t = 1 := ite_eq_right (not_lt_of_ge hsmall.le)
    have h₂ := P.reverseCoeff_small 1 ht.1 hsmall
    have h₃ := P.reverseCoeff_small 2 ht.1 hsmall
    have h₄ := P.reverseCoeff_small 3 ht.1 hsmall
    refine ⟨?_, ?_, ?_⟩
    · convert P.hasDerivAt_reverseCoeff_small 1 ht.1 hsmall using 1
      norm_num [h₂, hη]
    · convert P.hasDerivAt_reverseCoeff_small 2 ht.1 hsmall using 1
      norm_num [h₂, h₃, hη]
    · convert P.hasDerivAt_reverseCoeff_small 3 ht.1 hsmall using 1
      norm_num [h₂, h₃, h₄, hη]
  · have hSeam : -Real.log t ∉ P.chain.seams := by
      intro hs
      apply hNot'
      refine mem_insert_of_mem (mem_insert_of_mem (mem_image.mpr ⟨-Real.log t, hs, ?_⟩))
      rw [neg_neg, Real.exp_log ht.1]
    refine ⟨?_, ?_, ?_⟩
    · convert P.hasDerivAt_reverseCoeff_large 1 ht.1 ht₁ hlarge hSeam using 1
      norm_num [sum_range_succ, P.reverseCoeff_degree_one]
    · convert P.hasDerivAt_reverseCoeff_large 2 ht.1 ht₁ hlarge hSeam using 1
      norm_num [sum_range_succ, P.reverseCoeff_degree_one]
      ring
    · convert P.hasDerivAt_reverseCoeff_large 3 ht.1 ht₁ hlarge hSeam using 1
      norm_num [sum_range_succ, P.reverseCoeff_degree_one]
      ring

end Zalcman
