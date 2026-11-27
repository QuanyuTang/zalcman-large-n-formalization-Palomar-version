/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.ChainCoefficientTime
public import Zalcman.ChainTransitionLimits
public import Zalcman.LimitingDriverMoments
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Measurable driving moments of a nested holomorphic disk chain

At every time where the map's Taylor coefficients are differentiable, the
finite moments of its limiting positive-real drivers belong to the closed
unit-moment hull. Measurable triangular inversion makes the moment paths
available simultaneously in all degrees.
-/
@[expose] public section

namespace Zalcman

open Filter Finset MeasureTheory Set
open scoped Topology

/-- The normalized Taylor coefficient of degree `n + 1` at time `u`. -/
noncomputable def normalizedChainCoeff (F : ℝ → ℂ → ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  (Real.exp (-u) : ℂ) * coeff (F u) (n + 1)

private theorem coeff_z_mul_deriv {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisk) (n : ℕ) :
    coeff (fun z ↦ z * deriv f z) n = (n : ℂ) * coeff f n := by
  cases n with
  | zero => simp
  | succ n =>
    have hd := hf.deriv unitDisk_isOpen
    have hG : DifferentiableOn ℂ (fun z ↦ z * deriv f z) unitDisk := differentiableOn_id.fun_mul hd
    have hds : dslope (fun z ↦ z * deriv f z) 0 = deriv f := by
      funext z
      by_cases hz : z = 0
      · subst z
        rw [dslope_same]
        have h := (hasDerivAt_id (0 : ℂ)).fun_mul
          (hd.differentiableAt (unitDisk_isOpen.mem_nhds zero_mem_unitDisk)).hasDerivAt
        simpa only [id, one_mul, zero_mul, add_zero] using h.deriv
      · rw [dslope_of_ne _ hz, slope_fun_def_field]
        simp only [zero_mul, sub_zero]
        exact mul_div_cancel_left₀ _ hz
    simpa only [hds, coeff_deriv, Nat.cast_succ] using (coeff_dslope hG n)

set_option backward.isDefEq.respectTransparency false in
private theorem hasDerivAt_exp_normalizing_factor (u : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (Real.exp (-t) : ℂ)) (-(Real.exp (-u) : ℂ)) u := by
  have h := (hasDerivAt_neg' u).exp
  simpa only [mul_neg, mul_one, Complex.ofReal_neg, Complex.ofRealCLM_apply,
    Function.comp_def] using! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u h

set_option maxHeartbeats 800000 in
/-- A nested chain with conformal radius `exp u` has measurable generalized
moments and a finite triangular normalized coefficient system. -/
theorem exists_measurable_hull_moments_of_nested_chain {F : ℝ → ℂ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Set.Ici (0 : ℝ), DifferentiableOn ℂ (F t) unitDisk)
    (hi : ∀ t ∈ Set.Ici (0 : ℝ), InjOn (F t) unitDisk) (h₀ : ∀ t ∈ Set.Ici (0 : ℝ), F t 0 = 0)
    (h₁ : ∀ t ∈ Set.Ici (0 : ℝ), deriv (F t) 0 = (Real.exp t : ℂ))
    (hsub : ∀ s ∈ Set.Ici (0 : ℝ), ∀ t ∈ Set.Ici (0 : ℝ), s ≤ t → F s '' unitDisk ⊆ F t '' unitDisk) :
    ∃ m : ℕ → ℝ → ℂ, (∀ n, Measurable (m n)) ∧
      (∀ M, ∀ᵐ u ∂volume.restrict (Set.Ioc 0 T), (fun k : Fin M ↦ m k u) ∈ closedUnitMomentHull M) ∧
      (∀ n, AbsolutelyContinuousOnInterval (normalizedChainCoeff F n) 0 T) ∧
      ∀ᵐ u : ℝ ∂volume, u ∈ Set.Ioo 0 T → ∀ n,
        HasDerivAt (normalizedChainCoeff F n)
          ((n : ℂ) * normalizedChainCoeff F n u + 2 * ∑ j ∈ range n,
            ((j : ℂ) + 1) * normalizedChainCoeff F j u * m (n - 1 - j) u) u := by
  obtain ⟨hAC, hD⟩ := nested_chain_coefficients_time_regular hT hd hi h₀ h₁ hsub
  let clamp (u : ℝ) := max 0 (min u T)
  let C (n : ℕ) (u : ℝ) := coeff (F (clamp u)) n
  let w (u : ℝ) : ℂ := Real.exp (-u)
  let B (u : ℝ) (i j : ℕ) := ((i + 1 - j : ℕ) : ℂ) * C (i + 1 - j) u
  let v (u : ℝ) (i : ℕ) := deriv (C (i + 1)) u
  let m (n : ℕ) (u : ℝ) := complexTriangularSolution (B u) (v u) (n + 1) / 2
  have hClamp : Continuous clamp := continuous_const.max (continuous_id.min continuous_const)
  have hClampMem (u : ℝ) : clamp u ∈ uIcc 0 T := by
    rw [uIcc_of_le hT]
    exact ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hKeep (n : ℕ) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) T) : C n u = coeff (F u) n := by
    simp only [C, clamp, min_eq_left hu.2, max_eq_right hu.1]
  have hCC (n : ℕ) : Continuous (C n) := (hAC n).continuousOn.comp_continuous hClamp hClampMem
  have hBM (i j : ℕ) : Measurable (fun u ↦ B u i j) := measurable_const.mul (hCC _).measurable
  have hvM (i : ℕ) : Measurable (fun u ↦ v u i) := measurable_deriv _
  have hmM (n : ℕ) : Measurable (m n) := (measurable_complexTriangularSolution hBM hvM (n + 1)).div_const 2
  have hwAC : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ Real.exp (-t)) 0 T := by
    have hReal : ContDiff ℝ 1 (fun t : ℝ ↦ Real.exp (-t)) := by fun_prop
    exact hReal.contDiffOn.absolutelyContinuousOnInterval
  have hNormAC (n : ℕ) : AbsolutelyContinuousOnInterval (normalizedChainCoeff F n) 0 T := by
    simpa only [normalizedChainCoeff, Complex.real_smul] using! hwAC.fun_smul (hAC (n + 1))
  have hPoint (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) T)
      (hGood : ∀ n, HasDerivAt (fun t ↦ coeff (F t) n) (deriv (fun t ↦ coeff (F t) n) u) u) :
      (∀ M, (fun k : Fin M ↦ m k u) ∈ closedUnitMomentHull M) ∧
      ∀ n, HasDerivAt (normalizedChainCoeff F n)
        ((n : ℂ) * normalizedChainCoeff F n u + 2 * ∑ j ∈ range n,
          ((j : ℂ) + 1) * normalizedChainCoeff F j u * m (n - 1 - j) u) u := by
    have hu' : u ∈ Set.Icc (0 : ℝ) T := ⟨hu.1.le, hu.2.le⟩
    have hVAt (n : ℕ) : HasDerivAt (fun t ↦ coeff (F t) (n + 1)) (v u n) u := by
      have hN : ∀ᶠ t in 𝓝 u, t ∈ Set.Icc (0 : ℝ) T := Icc_mem_nhds hu.1 hu.2
      have heq : C (n + 1) =ᶠ[𝓝 u] fun t ↦ coeff (F t) (n + 1) :=
        hN.mono fun t ht ↦ hKeep (n + 1) t ht
      have he := ((hGood (n + 1)).congr_of_eventuallyEq heq).deriv
      rw [show v u n = deriv (fun t ↦ coeff (F t) (n + 1)) u from he]
      exact hGood (n + 1)
    let A (t : ℝ) (z : ℂ) := slope (fun s ↦ F s z) u t
    let g (z : ℂ) := z * deriv (F u) z
    have hAd : ∀ᶠ t in 𝓝[>] u, DifferentiableOn ℂ (A t) unitDisk := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      change u < t at ht
      have hh := (hd t (hu.1.le.trans ht.le)).fun_sub (hd u hu.1.le)
      simpa only [A, slope_def_module, Complex.real_smul] using hh.const_mul (((t - u)⁻¹ : ℝ) : ℂ)
    have hAL (n : ℕ) : Tendsto (fun t ↦ coeff (A t) (n + 1)) (𝓝[>] u) (𝓝 (v u n)) := by
      have h : Tendsto (slope (fun t ↦ coeff (F t) (n + 1)) u) (𝓝[>] u) (𝓝 (v u n)) :=
        (hVAt n).tendsto_slope.mono_left (nhdsWithin_mono _ fun t ht ↦ ne_of_gt ht)
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      change u < t at ht
      simp only [A, slope_def_module, Complex.real_smul, coeff_const_mul,
        coeff_sub (hd t (hu.1.le.trans ht.le)) (hd u hu.1.le)]
    have hgd : DifferentiableOn ℂ g unitDisk :=
      (differentiableOn_id : DifferentiableOn ℂ (fun z : ℂ ↦ z) unitDisk).fun_mul
        ((hd u hu.1.le).deriv unitDisk_isOpen)
    have hg₀ : g 0 = 0 := zero_mul _
    have hg₁ : coeff g 1 ≠ 0 := by
      have he : coeff g 1 = coeff (F u) 1 := by
        simpa only [g, Nat.cast_one, one_mul] using coeff_z_mul_deriv (hd u hu.1.le) 1
      rw [he, coeff_one, h₁ u hu.1.le]
      exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u)
    have hB (i j : ℕ) : B u i j = coeff g (i + 1 - j) := by
      change ((i + 1 - j : ℕ) : ℂ) * C (i + 1 - j) u =
        coeff (fun z ↦ z * deriv (F u) z) (i + 1 - j)
      rw [hKeep _ _ hu', coeff_z_mul_deriv (hd u hu.1.le)]
    have hBfun : (fun i j ↦ coeff g (i + 1 - j)) = B u := funext fun i ↦ funext fun j ↦ (hB i j).symm
    obtain ⟨p, c, hp, hc, hR⟩ := exists_nested_chain_slope_approximation hu.1.le hd hi h₀ h₁ hsub
    have hLp (n : ℕ) : Tendsto (fun t ↦ coeff (p t) n) (𝓝[>] u)
        (𝓝 (complexTriangularSolution (B u) (v u) n)) := by
      simpa only [hBfun] using
        tendsto_driver_coeff_of_transition_error hAd (hp.mono fun _ h ↦ h.1) hgd hg₀ hg₁ hc hAL hR n
    have hM₀ : complexTriangularSolution (B u) (v u) 0 = 1 := by
      apply tendsto_nhds_unique (hLp 0)
      apply tendsto_const_nhds.congr'
      filter_upwards [hp] with t hpt
      simpa only [coeff_zero] using hpt.2.1.symm
    refine ⟨fun M ↦ limiting_driver_coeff_mem_closedUnitMomentHull hp hLp M, ?_⟩
    intro n
    have hDiag (i : ℕ) : B u i i ≠ 0 := by
      rw [hB, show i + 1 - i = 1 by omega]
      exact hg₁
    have hRec : v u n = ((n : ℂ) + 1) * coeff (F u) (n + 1) +
        2 * ∑ j ∈ range n, ((j : ℂ) + 1) * coeff (F u) (j + 1) * m (n - 1 - j) u := by
      have hsum : (∑ k ∈ range n, B u n (k + 1) * complexTriangularSolution (B u) (v u) (k + 1)) =
          2 * ∑ j ∈ range n, ((j : ℂ) + 1) * coeff (F u) (j + 1) * m (n - 1 - j) u := by
        rw [← sum_range_reflect (fun k ↦ B u n (k + 1) * complexTriangularSolution (B u) (v u) (k + 1)) n,
          mul_sum]
        apply sum_congr rfl
        intro j hj
        have hidx : n + 1 - (n - 1 - j + 1) = j + 1 := by have := mem_range.mp hj; omega
        rw [show B u n (n - 1 - j + 1) = ((j : ℂ) + 1) * coeff (F u) (j + 1) by
          simp only [B, hidx, Nat.cast_add, Nat.cast_one, hKeep _ _ hu']]
        simp only [m]
        ring
      have hdiag₀ : B u n 0 = ((n : ℂ) + 1) * coeff (F u) (n + 1) := by
        simp only [B, Nat.sub_zero, Nat.cast_add, Nat.cast_one, hKeep _ _ hu']
      rw [← sum_complexTriangularSolution (v u) hDiag n, sum_range_succ', hM₀, mul_one, hdiag₀, hsum]
      rw [add_comm]
    have hwD : HasDerivAt w (-w u) u := hasDerivAt_exp_normalizing_factor u
    have hDer := hwD.fun_mul (hVAt n)
    have hwSum : (∑ j ∈ range n, ((j : ℂ) + 1) * normalizedChainCoeff F j u * m (n - 1 - j) u) =
        w u * (∑ j ∈ range n, ((j : ℂ) + 1) * coeff (F u) (j + 1) * m (n - 1 - j) u) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ ↦ by dsimp only [normalizedChainCoeff, w]; ring
    have he : -w u * coeff (F u) (n + 1) + w u * v u n =
        (n : ℂ) * normalizedChainCoeff F n u + 2 * ∑ j ∈ range n,
          ((j : ℂ) + 1) * normalizedChainCoeff F j u * m (n - 1 - j) u := by
      rw [hRec, hwSum]
      dsimp only [normalizedChainCoeff, w]
      ring
    exact he ▸ hDer
  have hBoth := hD.mono fun u hu hI ↦ hPoint u hI (hu hI)
  refine ⟨m, hmM, fun M ↦ ?_, hNormAC, hBoth.mono fun _ hu hI ↦ (hu hI).2⟩
  rw [← restrict_Ioo_eq_restrict_Ioc, ae_restrict_iff' measurableSet_Ioo]
  exact hBoth.mono fun _ hu hI ↦ (hu hI).1 M

end Zalcman
