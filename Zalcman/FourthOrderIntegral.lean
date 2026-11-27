/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integrating the fourth-order coefficient system
-/

public section

namespace Zalcman

open MeasureTheory Set

/-- The fundamental theorem of calculus for a complex absolutely continuous
path whose derivative is given almost everywhere by an integrable function. -/
theorem integral_eq_sub_of_complex_absolutelyContinuousOnInterval
    {F G : ℝ → ℂ} {a b : ℝ} (hF : AbsolutelyContinuousOnInterval F a b)
    (hG : IntervalIntegrable G volume a b)
    (hD : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc a b → HasDerivAt F (G t) t) :
    (∫ t in a..b, G t) = F b - F a := by
  have hmap (L : ℂ →L[ℝ] ℝ) : L (∫ t in a..b, G t) = L (F b - F a) := by
    have hac : AbsolutelyContinuousOnInterval (fun t ↦ L (F t)) a b :=
      L.lipschitzWith.comp_absolutelyContinuousOnInterval hF
    calc
      _ = ∫ t in a..b, L (G t) := (L.intervalIntegral_comp_comm hG).symm
      _ = ∫ t in a..b, deriv (fun x ↦ L (F x)) t := by
        apply intervalIntegral.integral_congr_ae
        exact hD.mono fun t ht hmem ↦ (L.hasFDerivAt.comp_hasDerivAt t (ht hmem)).deriv.symm
      _ = L (F b) - L (F a) := hac.integral_deriv_eq_sub
      _ = _ := (L.map_sub _ _).symm
  exact Complex.ext (hmap Complex.reCLM) (hmap Complex.imCLM)

set_option maxHeartbeats 1000000 in
/-- Ordered iterated integral form of the fourth-order coefficient correction. -/
theorem fourth_order_integral_formula
    {A B C h₂ h₃ h₄ : ℝ → ℂ}
    (hA : IntervalIntegrable A volume 0 1) (hB : IntervalIntegrable B volume 0 1)
    (hC : IntervalIntegrable C volume 0 1)
    (h₂ac : AbsolutelyContinuousOnInterval h₂ 0 1)
    (h₃ac : AbsolutelyContinuousOnInterval h₃ 0 1)
    (h₄ac : AbsolutelyContinuousOnInterval h₄ 0 1)
    (h₂0 : h₂ 0 = 0) (h₃0 : h₃ 0 = 0) (h₄0 : h₄ 0 = 0)
    (hD : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc (0 : ℝ) 1 →
      HasDerivAt h₂ (A t) t ∧ HasDerivAt h₃ (B t + 2 * A t * h₂ t) t ∧
        HasDerivAt h₄ (C t + 2 * B t * h₂ t + 3 * A t * h₃ t) t) :
    let P (t : ℝ) := ∫ s in (0 : ℝ)..t, A s
    let Q (t : ℝ) := ∫ s in (0 : ℝ)..t, B s
    8 * h₂ 1 + 6 * h₃ 1 + h₄ 1 =
      (∫ t in (0 : ℝ)..1, 8 * A t + 6 * B t + C t) +
        (∫ t in (0 : ℝ)..1, 12 * A t * P t + (2 * B t * P t + 3 * A t * Q t)) + P 1 ^ 3 := by
  let P (t : ℝ) := ∫ s in (0 : ℝ)..t, A s
  let Q (t : ℝ) := ∫ s in (0 : ℝ)..t, B s
  change 8 * h₂ 1 + 6 * h₃ 1 + h₄ 1 =
    (∫ t in (0 : ℝ)..1, 8 * A t + 6 * B t + C t) +
      (∫ t in (0 : ℝ)..1, 12 * A t * P t + (2 * B t * P t + 3 * A t * Q t)) + P 1 ^ 3
  have hsubcc {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) 1) : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc_right ht.2
  have hsuboc {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) 1) : uIoc (0 : ℝ) t ⊆ uIoc 0 1 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [uIoc_of_le ht.1, uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Ioc_subset_Ioc_right ht.2
  have hP (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : h₂ t = P t := by
    have hD' : ∀ᵐ x : ℝ ∂volume, x ∈ uIoc 0 t → HasDerivAt h₂ (A x) x :=
      hD.mono fun _ hx hx' ↦ (hx (hsuboc ht hx')).1
    have h := integral_eq_sub_of_complex_absolutelyContinuousOnInterval
      (h₂ac.mono (hsubcc ht)) (hA.mono_set (hsubcc ht)) hD'
    simpa only [h₂0, sub_zero, P] using h.symm
  let R (t : ℝ) := h₃ t - h₂ t ^ 2
  have h₂sq : AbsolutelyContinuousOnInterval (fun t ↦ h₂ t ^ 2) 0 1 := by
    simpa only [pow_two, smul_eq_mul] using h₂ac.fun_smul h₂ac
  have h₂cube : AbsolutelyContinuousOnInterval (fun t ↦ h₂ t ^ 3) 0 1 := by
    simpa only [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, smul_eq_mul] using h₂sq.fun_smul h₂ac
  have hRac : AbsolutelyContinuousOnInterval R 0 1 := h₃ac.fun_sub h₂sq
  have hR0 : R 0 = 0 := by simp [R, h₃0, h₂0]
  have hRd : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc (0 : ℝ) 1 → HasDerivAt R (B t) t := by
    filter_upwards [hD] with t ht hmem
    obtain ⟨h2, h3, _⟩ := ht hmem
    have hd := h3.fun_sub (h2.fun_mul h2)
    have heq : B t + 2 * A t * h₂ t - (A t * h₂ t + h₂ t * A t) = B t := by ring
    rw [heq] at hd
    simpa only [R, pow_two] using hd
  have hQ (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : R t = Q t := by
    have hD' : ∀ᵐ x : ℝ ∂volume, x ∈ uIoc 0 t → HasDerivAt R (B x) x :=
      hRd.mono fun _ hx hx' ↦ hx (hsuboc ht hx')
    have h := integral_eq_sub_of_complex_absolutelyContinuousOnInterval
      (hRac.mono (hsubcc ht)) (hB.mono_set (hsubcc ht)) hD'
    simpa only [hR0, sub_zero, Q] using h.symm
  let K (t : ℝ) := 2 * B t * h₂ t + 3 * A t * R t
  have hK : IntervalIntegrable K volume 0 1 :=
    ((hB.const_mul 2).mul_continuousOn h₂ac.continuousOn).add
      ((hA.const_mul 3).mul_continuousOn hRac.continuousOn)
  let S (t : ℝ) := h₄ t - h₂ t ^ 3
  have hSac : AbsolutelyContinuousOnInterval S 0 1 := h₄ac.fun_sub h₂cube
  have hS0 : S 0 = 0 := by simp [S, h₄0, h₂0]
  have hSd : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc (0 : ℝ) 1 → HasDerivAt S (C t + K t) t := by
    filter_upwards [hD] with t ht hmem
    obtain ⟨h2, _, h4⟩ := ht hmem
    convert h4.fun_sub ((h2.fun_mul h2).fun_mul h2) using 1 <;>
      simp only [S, K, R, show (3 : ℕ) = 2 + 1 by rfl, pow_succ] <;> ring
  have hS_int : (∫ t in (0 : ℝ)..1, C t) + (∫ t in (0 : ℝ)..1, K t) = S 1 := by
    have h := integral_eq_sub_of_complex_absolutelyContinuousOnInterval hSac (hC.add hK) hSd
    simpa only [hS0, sub_zero, intervalIntegral.integral_add hC hK] using h
  have hAh₂ : IntervalIntegrable (fun t ↦ A t * h₂ t) volume 0 1 :=
    hA.mul_continuousOn h₂ac.continuousOn
  have hSqD : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc (0 : ℝ) 1 →
      HasDerivAt (fun x ↦ h₂ x ^ 2) (2 * (A t * h₂ t)) t := by
    filter_upwards [hD] with t ht hmem
    have h2 := (ht hmem).1
    have hd := h2.fun_mul h2
    have heq : A t * h₂ t + h₂ t * A t = 2 * (A t * h₂ t) := by ring
    rw [heq] at hd
    simpa only [pow_two] using hd
  have hSqInt : 2 * (∫ t in (0 : ℝ)..1, A t * h₂ t) = h₂ 1 ^ 2 := by
    have h := integral_eq_sub_of_complex_absolutelyContinuousOnInterval h₂sq (hAh₂.const_mul 2) hSqD
    simpa only [h₂0, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero,
      intervalIntegral.integral_const_mul] using h
  have hI₁ : (∫ t in (0 : ℝ)..1, 8 * A t + 6 * B t + C t) =
      8 * (∫ t in (0 : ℝ)..1, A t) + 6 * (∫ t in (0 : ℝ)..1, B t) +
        (∫ t in (0 : ℝ)..1, C t) := by
    rw [intervalIntegral.integral_add ((hA.const_mul 8).add (hB.const_mul 6)) hC,
      intervalIntegral.integral_add (hA.const_mul 8) (hB.const_mul 6),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hI₂ : (∫ t in (0 : ℝ)..1, 12 * A t * P t + (2 * B t * P t + 3 * A t * Q t)) =
      12 * (∫ t in (0 : ℝ)..1, A t * h₂ t) + (∫ t in (0 : ℝ)..1, K t) := by
    calc
      _ = ∫ t in (0 : ℝ)..1, 12 * (A t * h₂ t) + K t := by
        apply intervalIntegral.integral_congr
        intro t ht
        change 12 * A t * P t + (2 * B t * P t + 3 * A t * Q t) =
          12 * (A t * h₂ t) + K t
        rw [← hP t ht, ← hQ t ht]
        unfold K
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hAh₂.const_mul 12) hK, intervalIntegral.integral_const_mul]
  have h1 : (1 : ℝ) ∈ uIcc (0 : ℝ) 1 := right_mem_uIcc
  have hP1 : h₂ 1 = ∫ t in (0 : ℝ)..1, A t := hP 1 h1
  have hQ1 : h₃ 1 - h₂ 1 ^ 2 = ∫ t in (0 : ℝ)..1, B t := hQ 1 h1
  change (∫ t in (0 : ℝ)..1, C t) + (∫ t in (0 : ℝ)..1, K t) =
    h₄ 1 - h₂ 1 ^ 3 at hS_int
  rw [hI₁, hI₂, ← hP 1 h1]
  linear_combination 8 * hP1 + 6 * hQ1 - hS_int - 6 * hSqInt

end Zalcman
