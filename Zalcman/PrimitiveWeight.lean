/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.FourthOrderIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted estimates from a primitive bound

Integration by parts transfers a uniform primitive bound to a weighted
integral against an absolutely continuous complex path.
-/

@[expose] public section

namespace Zalcman

open Filter MeasureTheory Set
open scoped NNReal

/-- The primitive of an essentially bounded complex function is Lipschitz on
the interval on which the bound holds. -/
theorem lipschitzOnWith_interval_primitive {g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hI : IntervalIntegrable g volume a b) {B : ℝ≥0}
    (hB : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖g t‖ ≤ (B : ℝ)) :
    LipschitzOnWith B (fun t ↦ ∫ s in a..t, g s) (Icc a b) := by
  let P (t : ℝ) := ∫ s in a..t, g s
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have hx' : x ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hx
  have hy' : y ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hy
  have hay := hI.mono_set (uIcc_subset_uIcc left_mem_uIcc hy')
  have hyx := hI.mono_set (uIcc_subset_uIcc hy' hx')
  have hAdd := intervalIntegral.integral_add_adjacent_intervals hay hyx
  have hDiff : P x - P y = ∫ s in y..x, g s := by
    dsimp only [P]
    linear_combination -hAdd
  have hyxSubset : uIoc y x ⊆ Ioc a b := by
    intro s hs
    change s ∈ Ioc (min y x) (max y x) at hs
    exact ⟨(le_min hy.1 hx.1).trans_lt hs.1, hs.2.trans (max_le hy.2 hx.2)⟩
  have hN : ∀ᵐ s ∂volume, s ∈ uIoc y x → ‖g s‖ ≤ (B : ℝ) :=
    (ae_restrict_iff' measurableSet_uIoc).mp <|
      ae_mono (Measure.restrict_mono_set volume hyxSubset) hB
  change dist (P x) (P y) ≤ (B : ℝ) * dist x y
  rw [dist_eq_norm, hDiff, Real.dist_eq]
  exact intervalIntegral.norm_integral_le_of_norm_le_const_ae hN

/-- A uniform primitive bound controls the integral of `g` after multiplying
by an absolutely continuous weight. -/
theorem norm_intervalIntegral_mul_le_of_primitive_bound {g F F' : ℝ → ℂ}
    {a b ε : ℝ} (hab : a ≤ b) (hg : IntervalIntegrable g volume a b)
    (hF : AbsolutelyContinuousOnInterval F a b) (hF'I : IntervalIntegrable F' volume a b)
    (hF'D : ∀ᵐ t ∂volume, t ∈ uIoc a b → HasDerivAt F (F' t) t)
    {B : ℝ≥0} (hgB : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖g t‖ ≤ (B : ℝ))
    (hε : ∀ t ∈ Icc a b, ‖∫ s in a..t, g s‖ ≤ ε) :
    ‖∫ t in a..b, F t * g t‖ ≤ ε * (‖F b‖ + ∫ t in a..b, ‖F' t‖) := by
  let P (t : ℝ) := ∫ s in a..t, g s
  have hP : AbsolutelyContinuousOnInterval P a b := by
    have hLip : LipschitzOnWith B P (uIcc a b) := by
      rw [uIcc_of_le hab]
      exact lipschitzOnWith_interval_primitive hab hg hgB
    exact hLip.absolutelyContinuousOnInterval
  have hI₁ : IntervalIntegrable (fun t ↦ F' t * P t) volume a b := hF'I.mul_continuousOn hP.continuousOn
  have hI₂ : IntervalIntegrable (fun t ↦ F t * g t) volume a b := hg.continuousOn_mul hF.continuousOn
  have hD : ∀ᵐ t ∂volume, t ∈ uIoc a b →
      HasDerivAt (fun s ↦ F s * P s) (F' t * P t + F t * g t) t := by
    filter_upwards [hF'D, hg.ae_hasDerivAt_integral] with t htF htP ht
    exact (htF ht).fun_mul (htP (uIoc_subset_uIcc ht) a left_mem_uIcc)
  have hProdAC : AbsolutelyContinuousOnInterval (fun u ↦ F u * P u) a b := by
    simpa only [smul_eq_mul] using hF.fun_smul hP
  have hFTC := integral_eq_sub_of_complex_absolutelyContinuousOnInterval hProdAC (hI₁.add hI₂) hD
  have hPa : P a = 0 := by simp [P]
  rw [intervalIntegral.integral_add hI₁ hI₂, hPa, mul_zero, sub_zero] at hFTC
  have hparts : (∫ t in a..b, F t * g t) = F b * P b - (∫ t in a..b, F' t * P t) := by
    linear_combination hFTC
  have htail : ‖∫ t in a..b, F' t * P t‖ ≤ ε * (∫ t in a..b, ‖F' t‖) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le hab ?_ (hF'I.norm.const_mul ε)
    refine .of_forall fun t ht ↦ ?_
    rw [norm_mul, mul_comm ε]
    exact mul_le_mul_of_nonneg_left (hε _ ⟨ht.1.le, ht.2⟩) (norm_nonneg _)
  rw [hparts]
  calc
    _ ≤ ‖F b * P b‖ + ‖∫ t in a..b, F' t * P t‖ := norm_sub_le _ _
    _ ≤ ‖F b‖ * ε + ε * (∫ t in a..b, ‖F' t‖) := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hε _ ⟨hab, le_rfl⟩) (norm_nonneg _)) htail
    _ = _ := by ring


/-- A bound on the primitive anchored at `a` controls every terminal subinterval.
The factor two comes from subtracting two values of the anchored primitive. -/
theorem norm_intervalIntegral_mul_le_of_anchored_primitive {g F F' : ℝ → ℂ}
    {a t b ε : ℝ} (hat : a ≤ t) (htb : t ≤ b) (hg : IntervalIntegrable g volume a b)
    (hF : AbsolutelyContinuousOnInterval F t b) (hF'I : IntervalIntegrable F' volume t b)
    (hF'D : ∀ᵐ u ∂volume, u ∈ uIoc t b → HasDerivAt F (F' u) u)
    {B : ℝ≥0} (hgB : ∀ᵐ u ∂volume.restrict (Ioc a b), ‖g u‖ ≤ (B : ℝ))
    (hε : ∀ u ∈ Icc a b, ‖∫ s in a..u, g s‖ ≤ ε) :
    ‖∫ u in t..b, F u * g u‖ ≤ (2 * ε) * (‖F b‖ + ∫ u in t..b, ‖F' u‖) := by
  have hab := hat.trans htb
  have hgsub (u : ℝ) (htu : t ≤ u) (hub : u ≤ b) : IntervalIntegrable g volume t u :=
    hg.mono_set <| by
      rw [uIcc_of_le htu, uIcc_of_le hab]
      exact Icc_subset_Icc hat hub
  have hgB' : ∀ᵐ u ∂volume.restrict (Ioc t b), ‖g u‖ ≤ (B : ℝ) :=
    ae_mono (Measure.restrict_mono_set _ (Ioc_subset_Ioc_left hat)) hgB
  apply norm_intervalIntegral_mul_le_of_primitive_bound htb (hgsub b htb le_rfl) hF hF'I hF'D hgB'
  intro u hu
  have hgt : IntervalIntegrable g volume a t :=
    hg.mono_set <| by
      rw [uIcc_of_le hat, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl htb
  have heq : (∫ s in t..u, g s) = (∫ s in a..u, g s) - (∫ s in a..t, g s) := by
    have he := intervalIntegral.integral_add_adjacent_intervals hgt (hgsub u hu.1 hu.2)
    linear_combination he
  rw [heq, two_mul]
  exact (norm_sub_le _ _).trans (add_le_add (hε _ ⟨hat.trans hu.1, hu.2⟩) (hε _ ⟨hat, htb⟩))

/-- The exponential integrating factor for a terminal-value equation on `[t,T]`. -/
noncomputable def backwardExpWeight (q t u : ℝ) : ℂ := (Real.exp (q * (t - u)) : ℂ)

@[simp] theorem backwardExpWeight_at_start (q t : ℝ) : backwardExpWeight q t t = 1 := by
  simp [backwardExpWeight]

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_backwardExpWeight (q t u : ℝ) :
    HasDerivAt (backwardExpWeight q t) (((-q : ℝ) : ℂ) * backwardExpWeight q t u) u := by
  have h : HasDerivAt (fun v : ℝ ↦ q * (t - v)) (-q) u := by
    simpa only [id, zero_sub, mul_neg, mul_one] using
      (((hasDerivAt_const u t).fun_sub (hasDerivAt_id u)).const_mul q)
  simpa only [backwardExpWeight, Complex.ofReal_mul, mul_comm, Complex.ofRealCLM_apply,
    Function.comp_def] using! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u h.exp

theorem contDiff_backwardExpWeight (q t : ℝ) : ContDiff ℝ 1 (backwardExpWeight q t) := by
  have h : ContDiff ℝ 1 (fun u : ℝ ↦ Real.exp (q * (t - u))) := by fun_prop
  exact Complex.ofRealCLM.contDiff.comp h

theorem norm_backwardExpWeight_le_one {q t u : ℝ} (hq : 0 ≤ q) (hu : t ≤ u) :
    ‖backwardExpWeight q t u‖ ≤ 1 := by
  rw [backwardExpWeight, Complex.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hq (sub_nonpos.mpr hu))

/-- Exponential backward variation of constants preserves primitive control of
forcing against a bounded absolutely continuous coefficient. -/
theorem norm_exponential_weighted_forcing_le {g F F' : ℝ → ℂ} {t T q C ε : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) (hq : 0 ≤ q) (hε₀ : 0 ≤ ε)
    (hg : IntervalIntegrable g volume 0 T) {B : ℝ≥0}
    (hgB : ∀ᵐ u ∂volume.restrict (Ioc 0 T), ‖g u‖ ≤ (B : ℝ))
    (hε : ∀ u ∈ Icc 0 T, ‖∫ s in 0..u, g s‖ ≤ ε)
    (hF : AbsolutelyContinuousOnInterval F 0 T) (hF'I : IntervalIntegrable F' volume 0 T)
    (hF'D : ∀ᵐ u ∂volume, u ∈ uIoc 0 T → HasDerivAt F (F' u) u)
    (hC : ∀ u ∈ Icc 0 T, ‖F u‖ ≤ C) :
    ‖∫ u in t..T, (Real.exp (q * (t - u)) : ℂ) * F u * g u‖ ≤
      (2 * ε) * (C + (∫ u in 0..T, ‖F' u‖) + q * C * T) := by
  let w := backwardExpWeight q t
  let W (u : ℝ) : ℂ := w u * F u
  let W' (u : ℝ) : ℂ := ((-q : ℝ) : ℂ) * w u * F u + w u * F' u
  have hTT : 0 ≤ T := ht.trans htT
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC _ ⟨hTT, le_rfl⟩)
  have hsub : uIcc t T ⊆ uIcc 0 T := by
    rw [uIcc_of_le htT, uIcc_of_le hTT]
    exact Icc_subset_Icc_left ht
  have hsub' : uIoc t T ⊆ uIoc 0 T := by
    rw [uIoc_of_le htT, uIoc_of_le hTT]
    exact Ioc_subset_Ioc_left ht
  have wSmooth : ContDiff ℝ 1 w := contDiff_backwardExpWeight q t
  have hFt := hF.mono hsub
  have hFW : AbsolutelyContinuousOnInterval W t T := by
    simpa only [W, smul_eq_mul] using wSmooth.contDiffOn.absolutelyContinuousOnInterval.fun_smul hFt
  have hFIt := hF'I.mono_set hsub
  have hwC : ContinuousOn w (uIcc t T) := wSmooth.continuous.continuousOn
  have hWI : IntervalIntegrable W' volume t T := by
    refine IntervalIntegrable.add ?_ (hFIt.continuousOn_mul hwC)
    exact ((continuousOn_const.mul hwC).mul hFt.continuousOn).intervalIntegrable
  have hWD : ∀ᵐ u ∂volume, u ∈ uIoc t T → HasDerivAt W (W' u) u := by
    filter_upwards [hF'D] with u hu htu
    exact (hasDerivAt_backwardExpWeight q t u).fun_mul (hu (hsub' htu))
  have hFIa : IntervalIntegrable F' volume 0 t :=
    hF'I.mono_set (uIcc_subset_uIcc left_mem_uIcc (by rw [uIcc_of_le hTT]; exact ⟨ht, htT⟩))
  have hF'Ibound : (∫ u in t..T, ‖F' u‖) ≤ ∫ u in 0..T, ‖F' u‖ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hFIa.norm hFIt.norm]
    exact le_add_of_nonneg_left (intervalIntegral.integral_nonneg_of_forall ht (fun _ ↦ norm_nonneg _))
  have hWIbound : (∫ u in t..T, ‖W' u‖) ≤ (∫ u in t..T, ‖F' u‖) + q * C * T := by
    calc
      _ ≤ ∫ u in t..T, ‖F' u‖ + q * C := by
        apply intervalIntegral.integral_mono_on htT hWI.norm (hFIt.norm.add intervalIntegrable_const)
        intro u hu
        have hu' : u ∈ Icc 0 T := ⟨ht.trans hu.1, hu.2⟩
        have hq' : ‖((-q : ℝ) : ℂ)‖ = q := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hq]
        have hwu := norm_backwardExpWeight_le_one hq hu.1
        have h₁ : q * ‖w u‖ * ‖F u‖ ≤ q * C := by
          calc
            _ ≤ q * 1 * ‖F u‖ := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hwu hq) (norm_nonneg _)
            _ ≤ q * C := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hC u hu') hq
        have h₂ : ‖w u‖ * ‖F' u‖ ≤ ‖F' u‖ := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hwu (norm_nonneg (F' u))
        unfold W'
        exact (norm_add_le _ _).trans (by
          simp only [norm_mul, hq']
          rw [add_comm ‖F' u‖]
          exact add_le_add h₁ h₂)
      _ = (∫ u in t..T, ‖F' u‖) + (T - t) * (q * C) := by
        rw [intervalIntegral.integral_add hFIt.norm intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right (sub_le_self T ht) (mul_nonneg hq hC₀)
        have h' : (T - t) * (q * C) ≤ q * C * T := h.trans_eq (mul_comm T (q * C))
        exact add_le_add (le_refl _) h'
  have hWF : ‖W T‖ ≤ C := by
    rw [show W T = w T * F T from rfl, norm_mul]
    exact (mul_le_mul_of_nonneg_right (norm_backwardExpWeight_le_one hq htT) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hC T ⟨hTT, le_rfl⟩)
  have hbound := norm_intervalIntegral_mul_le_of_anchored_primitive ht htT hg hFW hWI hWD hgB hε
  calc
    _ ≤ (2 * ε) * (‖W T‖ + ∫ u in t..T, ‖W' u‖) := hbound
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Exact backward variation of constants for an absolutely continuous complex path. -/
theorem eq_terminal_mul_sub_integral_of_hasDerivAt {F G : ℝ → ℂ} {q t T : ℝ}
    (hF : AbsolutelyContinuousOnInterval F t T) (hG : IntervalIntegrable G volume t T)
    (hD : ∀ᵐ u ∂volume, u ∈ uIoc t T → HasDerivAt F ((q : ℂ) * F u + G u) u) :
    F t = backwardExpWeight q t T * F T - ∫ u in t..T, backwardExpWeight q t u * G u := by
  let w := backwardExpWeight q t
  have hc := contDiff_backwardExpWeight q t
  have hI : IntervalIntegrable (fun u ↦ w u * G u) volume t T :=
    hG.continuousOn_mul hc.continuous.continuousOn
  have hD' : ∀ᵐ u ∂volume, u ∈ uIoc t T →
      HasDerivAt (fun s ↦ w s * F s) (w u * G u) u := by
    filter_upwards [hD] with u hu hmem
    have h := (hasDerivAt_backwardExpWeight q t u).fun_mul (hu hmem)
    have he : ((-q : ℝ) : ℂ) * w u * F u + w u * ((q : ℂ) * F u + G u) = w u * G u := by
      rw [Complex.ofReal_neg]
      ring
    exact he ▸ h
  have hAC : AbsolutelyContinuousOnInterval (fun s ↦ w s * F s) t T := by
    simpa only [smul_eq_mul] using hc.contDiffOn.absolutelyContinuousOnInterval.fun_smul hF
  have hFTC := integral_eq_sub_of_complex_absolutelyContinuousOnInterval hAC hI hD'
  have hStart : w t = 1 := backwardExpWeight_at_start _ _
  simp only [hStart, one_mul] at hFTC
  change F t = w T * F T - ∫ u in t..T, w u * G u
  linear_combination hFTC

end Zalcman
