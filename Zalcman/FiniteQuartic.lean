/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.ReverseChainCoefficients
public import Zalcman.ReverseQuartic
public import Zalcman.FourthOrderIntegral
public import Zalcman.FourthOrderBound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The fourth-order estimate for finite Koebe driver chains
-/

public section

noncomputable section

namespace Zalcman

open MeasureTheory Set

private lemma interval_absolutelyContinuous_const_complex (c : ℂ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ c) 0 1 :=
  (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval

private lemma absolutelyContinuous_koebe_germs {b₂ b₃ b₄ : ℝ → ℂ}
    (h₂ : AbsolutelyContinuousOnInterval b₂ 0 1)
    (h₃ : AbsolutelyContinuousOnInterval b₃ 0 1)
    (h₄ : AbsolutelyContinuousOnInterval b₄ 0 1) :
    AbsolutelyContinuousOnInterval (koebeGermTwo b₂) 0 1 ∧
      AbsolutelyContinuousOnInterval (koebeGermThree b₂ b₃) 0 1 ∧
      AbsolutelyContinuousOnInterval (koebeGermFour b₂ b₃ b₄) 0 1 := by
  have hT : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ t) 0 1 := by
    exact (contDiff_id : ContDiff ℝ 1 (fun t : ℝ ↦ t)).contDiffOn.absolutelyContinuousOnInterval
  have hT₂ : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ t ^ 2) 0 1 := by
    simpa only [pow_two] using hT.fun_mul hT
  have hT₃ : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ t ^ 3) 0 1 := by
    simpa only [show (3 : ℕ) = 2 + 1 by rfl, pow_succ] using hT₂.fun_mul hT
  refine ⟨?_, ?_, ?_⟩
  · simpa only [koebeGermTwo, Complex.real_smul] using!
      hT.fun_smul (h₂.fun_sub (interval_absolutelyContinuous_const_complex 2))
  · have hb := (h₃.fun_sub (h₂.const_smul (4 : ℂ))).fun_add
      (interval_absolutelyContinuous_const_complex 5)
    simpa only [koebeGermThree, Complex.real_smul, Complex.ofReal_pow] using! hT₂.fun_smul hb
  · have hb := (((h₄.fun_sub (h₃.const_smul (6 : ℂ))).fun_add (h₂.const_smul (14 : ℂ))).fun_sub
      (interval_absolutelyContinuous_const_complex 14))
    simpa only [koebeGermFour, Complex.real_smul, Complex.ofReal_pow] using! hT₃.fun_smul hb

set_option maxHeartbeats 1250000 in
/-- For a finite Koebe driver chain, the third coefficient deficit controls
the fourth-order real-part correction when the second coefficient has nonnegative real part. -/
theorem FiniteKoebeDriverChain.fourth_coeff_real_bound (S : FiniteKoebeDriverChain)
    (hsign : 0 ≤ (coeff (S.chain.maps 0) 2).re) :
    |(coeff (S.chain.maps 0) 4 - 2 * coeff (S.chain.maps 0) 2).re| ≤
      3800 * (3 - (coeff (S.chain.maps 0) 3).re) := by
  let η := S.reverseDriver
  let b₂ := S.reverseCoeff 1
  let b₃ := S.reverseCoeff 2
  let b₄ := S.reverseCoeff 3
  let h₂ := koebeGermTwo b₂
  let h₃ := koebeGermThree b₂ b₃
  let h₄ := koebeGermFour b₂ b₃ b₄
  let A (t : ℝ) := fourthDrivingA (η t)
  let B (t : ℝ) := fourthDrivingB t (η t)
  let C (t : ℝ) := fourthDrivingC t (η t)
  have hη : Measurable η := S.measurable_reverseDriver
  have hunit (t : ℝ) (_ : t ∈ Ioc (0 : ℝ) 1) : ‖η t‖ = 1 := S.norm_reverseDriver t
  obtain ⟨h₂ac, h₃ac, h₄ac⟩ := absolutelyContinuous_koebe_germs
    (S.absolutelyContinuous_reverseCoeff 1) (S.absolutelyContinuous_reverseCoeff 2)
    (S.absolutelyContinuous_reverseCoeff 3)
  have h₂0 : h₂ 0 = 0 := by simp [h₂, koebeGermTwo]
  have h₃0 : h₃ 0 = 0 := by simp [h₃, koebeGermThree]
  have h₄0 : h₄ 0 = 0 := by simp [h₄, koebeGermFour]
  have hA : IntervalIntegrable A volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit (fun p ↦ fourthDrivingA p.2)
      (by unfold fourthDrivingA; fun_prop)
  have hB : IntervalIntegrable B volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit (fun p ↦ fourthDrivingB p.1 p.2)
      (by unfold fourthDrivingB; fun_prop)
  have hC : IntervalIntegrable C volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit (fun p ↦ fourthDrivingC p.1 p.2)
      (by unfold fourthDrivingC; fun_prop)
  have hD : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc (0 : ℝ) 1 →
      HasDerivAt h₂ (A t) t ∧ HasDerivAt h₃ (B t + 2 * A t * h₂ t) t ∧
        HasDerivAt h₄ (C t + 2 * B t * h₂ t + 3 * A t * h₃ t) t := by
    filter_upwards [S.ae_reverseCoeff_eqs] with t ht hmem
    obtain ⟨hb₂, hb₃, hb₄⟩ := ht hmem
    have ht₀ : t ≠ 0 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hmem
      exact hmem.1.ne'
    simpa only [h₂, h₃, h₄, A, B, C, b₂, b₃, b₄, η, fourthDrivingA, fourthDrivingB,
      fourthDrivingC, koebeVelocityTwo, koebeVelocityThree, koebeVelocityFour, mul_assoc] using
      hasDerivAt_koebeGerm ht₀ hb₂ hb₃ hb₄
  have h₄form : b₄ 1 - 2 * b₂ 1 = fourthOrderIntegratedCorrection η := by
    rw [reverse_quartic_difference_eq]
    exact fourth_order_integral_formula hA hB hC h₂ac h₃ac h₄ac h₂0 h₃0 h₄0 hD
  have hηInt : IntervalIntegrable η volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit Prod.snd continuous_snd
  have hηSqInt : IntervalIntegrable (fun t ↦ (t : ℂ) * η t ^ 2) volume 0 1 :=
    intervalIntegrable_unit_driver_comp hη hunit (fun p ↦ (p.1 : ℂ) * p.2 ^ 2) (by fun_prop)
  have intA := integral_eq_sub_of_complex_absolutelyContinuousOnInterval h₂ac hA
    (hD.mono fun _ ht hmem ↦ (ht hmem).1)
  change (∫ t in (0 : ℝ)..1, A t) = h₂ 1 - h₂ 0 at intA
  rw [h₂0, sub_zero] at intA
  have intA_eq : (∫ t in (0 : ℝ)..1, A t) = 2 * (∫ t in (0 : ℝ)..1, η t) - 2 := by
    unfold A fourthDrivingA
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hηInt intervalIntegrable_const]
    norm_num [intervalIntegral.integral_const]
    ring
  have h₂form : b₂ 1 = 2 * (∫ t in (0 : ℝ)..1, η t) := by
    simp only [h₂, koebeGermTwo, Complex.ofReal_one, one_mul] at intA
    linear_combination -intA + intA_eq
  let R (t : ℝ) := h₃ t - h₂ t ^ 2
  have h₂sq : AbsolutelyContinuousOnInterval (fun t ↦ h₂ t ^ 2) 0 1 := by
    simpa only [pow_two, smul_eq_mul] using! h₂ac.fun_smul h₂ac
  have hRac : AbsolutelyContinuousOnInterval R 0 1 := h₃ac.fun_sub h₂sq
  have hRd : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc (0 : ℝ) 1 → HasDerivAt R (B t) t := by
    filter_upwards [hD] with t ht hmem
    obtain ⟨h2, h3, _⟩ := ht hmem
    have hh := h3.fun_sub (h2.fun_mul h2)
    rw [show B t + 2 * A t * h₂ t - (A t * h₂ t + h₂ t * A t) = B t by ring] at hh
    simpa only [R, pow_two] using hh
  have intB := integral_eq_sub_of_complex_absolutelyContinuousOnInterval hRac hB hRd
  change (∫ t in (0 : ℝ)..1, B t) = R 1 - R 0 at intB
  have hR₀ : R 0 = 0 := by simp [R, h₂0, h₃0]
  rw [hR₀, sub_zero] at intB
  have hId : (∫ t in (0 : ℝ)..1, (t : ℂ)) = (1 / 2 : ℂ) := by
    have h := Complex.ofRealLI.intervalIntegral_comp_comm (a := (0 : ℝ)) (b := 1) (μ := volume)
      (fun t : ℝ ↦ t)
    simp only [Complex.ofRealLI_apply] at h
    rw [h, integral_id]
    norm_num
  have hIdInt : IntervalIntegrable (fun t : ℝ ↦ (t : ℂ)) volume 0 1 :=
    Complex.continuous_ofReal.intervalIntegrable 0 1
  have intB_eq : (∫ t in (0 : ℝ)..1, B t) =
      1 - 2 * (∫ t in (0 : ℝ)..1, (t : ℂ) * η t ^ 2) := by
    have hh (t : ℝ) : B t = -2 * ((t : ℂ) * η t ^ 2 - (t : ℂ)) := by
      dsimp only [B, fourthDrivingB]
      ring
    simp_rw [hh]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hηSqInt hIdInt, hId]
    ring
  have h₃form : b₃ 1 = b₂ 1 ^ 2 - 2 * (∫ t in (0 : ℝ)..1, (t : ℂ) * η t ^ 2) := by
    simp only [R, h₂, h₃, koebeGermTwo, koebeGermThree, Complex.ofReal_one, one_pow, one_mul]
      at intB
    linear_combination -intB + intB_eq
  have h₂terminal : b₂ 1 = coeff (S.chain.maps 0) 2 := S.reverseCoeff_at_one 1
  have h₃terminal : b₃ 1 = coeff (S.chain.maps 0) 3 := S.reverseCoeff_at_one 2
  have h₄terminal : b₄ 1 = coeff (S.chain.maps 0) 4 := S.reverseCoeff_at_one 3
  have hsgn : 0 ≤ (b₂ 1).re := h₂terminal.symm ▸ hsign
  have h := abs_fourth_coeff_sub_two_second_re_le_of_unit_driving
    hη hunit h₂form h₃form h₄form hsgn
  simpa only [h₂terminal, h₃terminal, h₄terminal] using h

end Zalcman
