/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.HyperbolicTranslate
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Differentiating the translated Taylor coefficients

The derivative of tanh makes its composition operator triangular on low
derivatives. The translation identity then expresses the ratios of derivatives
of the radial trace in terms of the normalized Taylor coefficients.
-/

public section

namespace Zalcman

private noncomputable def tanhC (x : ℝ) : ℂ := (Real.tanh x : ℂ)

private noncomputable def tanhFactor (x : ℝ) : ℂ := 1 - tanhC x ^ 2

private theorem hasDerivAt_tanhC (x : ℝ) : HasDerivAt tanhC (tanhFactor x) x := by
  change HasDerivAt (fun y : ℝ ↦ (Real.tanh y : ℂ)) (1 - (Real.tanh x : ℂ) ^ 2) x
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_pow] using!
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_real_tanh x)

private theorem hasDerivAt_tanhFactor (x : ℝ) :
    HasDerivAt tanhFactor (-2 * tanhC x * tanhFactor x) x := by
  have h := (hasDerivAt_const x (1 : ℂ)).fun_sub ((hasDerivAt_tanhC x).fun_pow 2)
  convert h using 1 <;> try rfl
  simp only [Nat.cast_ofNat, zero_sub]
  ring

private theorem differentiableOn_iteratedDeriv {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisk) (n : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv n f) unitDisk := by
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv unitDisk_isOpen

private lemma hasDerivAt_radialSpatialJet {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisk) (n : ℕ) (x : ℝ) :
    HasDerivAt (radialTrace (iteratedDeriv n f))
      (tanhFactor x * radialTrace (iteratedDeriv (n + 1) f) x) x := by
  simpa only [tanhFactor, tanhC, radialTrace, iteratedDeriv_succ] using
    hasDerivAt_radialTrace_of_differentiableOn (differentiableOn_iteratedDeriv hf n) x

private theorem coeff_mul_factorial {f : ℂ → ℂ} (n : ℕ) :
    iteratedDeriv n f 0 = (n.factorial : ℂ) * coeff f n := by
  rw [coeff, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), one_mul]

/-- The second through fourth real derivatives of a radial trace at zero. -/
theorem radialTrace_jets_zero {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    iteratedDeriv 2 (radialTrace f) 0 = 2 * coeff f 2 ∧
    iteratedDeriv 3 (radialTrace f) 0 = 6 * coeff f 3 - 2 ∧
    iteratedDeriv 4 (radialTrace f) 0 = 24 * coeff f 4 - 16 * coeff f 2 := by
  let p (n : ℕ) : ℝ → ℂ := radialTrace (iteratedDeriv n f)
  let t := tanhC
  let M := tanhFactor
  have ht (x : ℝ) : HasDerivAt t (M x) x := hasDerivAt_tanhC x
  have hM (x : ℝ) : HasDerivAt M (-2 * t x * M x) x := hasDerivAt_tanhFactor x
  have hp (n : ℕ) (x : ℝ) : HasDerivAt (p n) (M x * p (n + 1) x) x :=
    hasDerivAt_radialSpatialJet hf.holomorphic n x
  have h₁ : iteratedDeriv 1 (radialTrace f) = fun x => M x * p 1 x := by
    rw [iteratedDeriv_one]
    exact funext (fun x => by simpa only [p, iteratedDeriv_zero] using (hp 0 x).deriv)
  have h₂' (x : ℝ) : HasDerivAt (iteratedDeriv 1 (radialTrace f))
      (-2 * t x * M x * p 1 x + M x ^ 2 * p 2 x) x := by
    rw [h₁]
    convert (hM x).fun_mul (hp 1 x) using 1 <;> try rfl
    ring
  have h₂ : iteratedDeriv 2 (radialTrace f) =
      fun x => -2 * t x * M x * p 1 x + M x ^ 2 * p 2 x := by
    rw [iteratedDeriv_succ (n := 1)]
    exact funext fun x => (h₂' x).deriv
  have h₃' (x : ℝ) : HasDerivAt (iteratedDeriv 2 (radialTrace f))
      ((-2 * M x ^ 2 + 4 * t x ^ 2 * M x) * p 1 x -
        6 * t x * M x ^ 2 * p 2 x + M x ^ 3 * p 3 x) x := by
    rw [h₂]
    have hA := (((ht x).const_mul (-2 : ℂ)).fun_mul (hM x)).fun_mul (hp 1 x)
    have hB := ((hM x).fun_pow 2).fun_mul (hp 2 x)
    convert hA.fun_add hB using 1 <;> try rfl
    norm_num
    ring
  have h₃ : iteratedDeriv 3 (radialTrace f) =
      fun x => (-2 * M x ^ 2 + 4 * t x ^ 2 * M x) * p 1 x -
        6 * t x * M x ^ 2 * p 2 x + M x ^ 3 * p 3 x := by
    rw [iteratedDeriv_succ (n := 2)]
    exact funext fun x => (h₃' x).deriv
  have ht₀ : t 0 = 0 := by simp [t, tanhC]
  have hM₀ : M 0 = 1 := by simp [M, tanhFactor, tanhC]
  have h₄' : HasDerivAt (iteratedDeriv 3 (radialTrace f))
      (p 4 0 - 8 * p 2 0) 0 := by
    rw [h₃]
    have hA := (((hM 0).fun_pow 2).const_mul (-2 : ℂ)).fun_add
      ((((ht 0).fun_pow 2).const_mul (4 : ℂ)).fun_mul (hM 0))
    have hB := (((ht 0).const_mul (6 : ℂ)).fun_mul ((hM 0).fun_pow 2)).fun_mul (hp 2 0)
    have hC := ((hM 0).fun_pow 3).fun_mul (hp 3 0)
    convert (((hA.fun_mul (hp 1 0)).fun_sub hB).fun_add hC) using 1 <;> try rfl
    simp only [ht₀, hM₀, one_pow, zero_pow (by decide : (1 : ℕ) ≠ 0), mul_zero, zero_mul, one_mul,
      mul_one, add_zero, zero_add]
    ring
  have hpn (n : ℕ) : p n 0 = (n.factorial : ℂ) * coeff f n := by
    simpa only [p, radialTrace, Real.tanh_zero, Complex.ofReal_zero] using coeff_mul_factorial (f := f) n
  have hCoeff₁ : coeff f 1 = 1 := by simp [hf.deriv_zero]
  refine ⟨?_, ?_, ?_⟩
  · simp only [h₂, ht₀, hM₀, hpn]
    norm_num
  · simp only [h₃, ht₀, hM₀, hpn, hCoeff₁]
    norm_num <;> ring
  · rw [iteratedDeriv_succ (n := 3), h₄'.deriv, hpn, hpn]
    norm_num
    ring

private theorem radialTrace_jet_shift {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (x : ℝ)
    {n : ℕ} (hn : 0 < n) : iteratedDeriv n (radialTrace f) x =
      deriv (radialTrace f) x * iteratedDeriv n (radialTrace (hyperbolicTranslate f x)) 0 := by
  have hfun : (fun v => radialTrace f (x + v)) =
      fun v => radialTrace f x + deriv (radialTrace f) x *
        radialTrace (hyperbolicTranslate f x) v := funext (radialTrace_add hf x)
  have h := congrArg (fun G : ℝ → ℂ => iteratedDeriv n G 0) hfun
  simpa only [iteratedDeriv_comp_const_add, iteratedDeriv_const_add hn,
    iteratedDeriv_const_mul_field, add_zero] using h

/-- The higher real derivatives of the trace are normalized by the translated coefficients. -/
theorem radialTrace_iteratedDeriv_of_translate {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    (x : ℝ) : let g := hyperbolicTranslate f x
      iteratedDeriv 2 (radialTrace f) x = deriv (radialTrace f) x * (2 * coeff g 2) ∧
      iteratedDeriv 3 (radialTrace f) x = deriv (radialTrace f) x * (6 * coeff g 3 - 2) ∧
      iteratedDeriv 4 (radialTrace f) x = deriv (radialTrace f) x * (24 * coeff g 4 - 16 * coeff g 2) := by
  have h := radialTrace_jets_zero (hf.hyperbolicTranslate x)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [h.1] using radialTrace_jet_shift hf x (show 0 < 2 by decide)
  · simpa only [h.2.1] using radialTrace_jet_shift hf x (show 0 < 3 by decide)
  · simpa only [h.2.2] using radialTrace_jet_shift hf x (show 0 < 4 by decide)

private theorem contDiff_radialTrace {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisk) (n : ℕ) :
    ContDiff ℝ n (radialTrace f) := by
  have hT : ContDiff ℝ n Real.tanh := by
    rw [show Real.tanh = (fun y ↦ Real.sinh y / Real.cosh y) from
      funext Real.tanh_eq_sinh_div_cosh]
    exact Real.contDiff_sinh.div Real.contDiff_cosh (fun x => (Real.cosh_pos x).ne')
  have hTc : ContDiff ℝ n (fun x : ℝ => (Real.tanh x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hT
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hfx : ContDiffAt ℂ n f (Real.tanh x : ℂ) :=
    (hf.analyticOnNhd unitDisk_isOpen _ (tanh_mem_unitDisk x)).contDiffAt
  exact (hfx.restrict_scalars ℝ).comp x hTc.contDiffAt

theorem hasDerivAt_radialTrace_iteratedDeriv {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisk) (n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv n (radialTrace f)) (iteratedDeriv (n + 1) (radialTrace f) x) x := by
  rw [iteratedDeriv_succ]
  have h := (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp
    (contDiff_radialTrace hf (n + 1))).2
  exact (h.differentiable (by decide) x).hasDerivAt

theorem radialTrace_deriv_ne_zero {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (x : ℝ) :
    deriv (radialTrace f) x ≠ 0 := by
  rw [(hasDerivAt_radialTrace hf x).deriv]
  apply mul_ne_zero _ (hf.deriv_ne_zero (tanh_mem_unitDisk x))
  exact_mod_cast (sub_pos.mpr (Real.tanh_sq_lt_one x)).ne'

/-- The translated second and third coefficients have the claimed differential equations. -/
theorem hasDerivAt_translate_coeffs {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (x : ℝ) :
    let q : ℝ → ℂ := fun y => coeff (hyperbolicTranslate f y) 2
    let a : ℝ → ℂ := fun y => coeff (hyperbolicTranslate f y) 3
    let b : ℝ → ℂ := fun y => coeff (hyperbolicTranslate f y) 4
    HasDerivAt q (3 * a x - 2 * (q x) ^ 2 - 1) x ∧
    HasDerivAt a (4 * b x - 2 * q x - 2 * q x * a x) x := by
  let F := radialTrace f
  let q : ℝ → ℂ := fun y => coeff (hyperbolicTranslate f y) 2
  let a : ℝ → ℂ := fun y => coeff (hyperbolicTranslate f y) 3
  let b : ℝ → ℂ := fun y => coeff (hyperbolicTranslate f y) 4
  change HasDerivAt q (3 * a x - 2 * (q x) ^ 2 - 1) x ∧
    HasDerivAt a (4 * b x - 2 * q x - 2 * q x * a x) x
  have h₁ (y : ℝ) : iteratedDeriv 1 F y = deriv F y := by rw [iteratedDeriv_one]
  have hh₁ (y : ℝ) : iteratedDeriv 1 F y ≠ 0 := (h₁ y).symm ▸ radialTrace_deriv_ne_zero hf y
  have h₂ (y : ℝ) : iteratedDeriv 2 F y = iteratedDeriv 1 F y * (2 * q y) := by
    rw [h₁]
    exact (radialTrace_iteratedDeriv_of_translate hf y).1
  have h₃ (y : ℝ) : iteratedDeriv 3 F y = iteratedDeriv 1 F y * (6 * a y - 2) := by
    rw [h₁]
    exact (radialTrace_iteratedDeriv_of_translate hf y).2.1
  have h₄ (y : ℝ) : iteratedDeriv 4 F y = iteratedDeriv 1 F y * (24 * b y - 16 * q y) := by
    rw [h₁]
    exact (radialTrace_iteratedDeriv_of_translate hf y).2.2
  have hq : q = fun y => (iteratedDeriv 2 F y / iteratedDeriv 1 F y) / 2 := by
    funext y
    change q y = iteratedDeriv 2 F y / iteratedDeriv 1 F y / 2
    rw [h₂, mul_div_cancel_left₀ _ (hh₁ y)]
    ring
  have ha : a = fun y => (iteratedDeriv 3 F y / iteratedDeriv 1 F y + 2) / 6 := by
    funext y
    change a y = (iteratedDeriv 3 F y / iteratedDeriv 1 F y + 2) / 6
    rw [h₃, mul_div_cancel_left₀ _ (hh₁ y)]
    ring
  have D₁ : HasDerivAt (iteratedDeriv 1 F) (iteratedDeriv 2 F x) x :=
    hasDerivAt_radialTrace_iteratedDeriv hf.holomorphic 1 x
  have D₂ : HasDerivAt (iteratedDeriv 2 F) (iteratedDeriv 3 F x) x :=
    hasDerivAt_radialTrace_iteratedDeriv hf.holomorphic 2 x
  have D₃ : HasDerivAt (iteratedDeriv 3 F) (iteratedDeriv 4 F x) x :=
    hasDerivAt_radialTrace_iteratedDeriv hf.holomorphic 3 x
  constructor
  · have h := (D₂.fun_div D₁ (hh₁ x)).div_const (2 : ℂ)
    rw [← hq] at h
    convert h using 1 <;> try rfl
    rw [h₂, h₃]
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
    apply (eq_div_iff (pow_ne_zero 2 (hh₁ x))).mpr
    ring
  · have h := ((D₃.fun_div D₁ (hh₁ x)).add_const (2 : ℂ)).div_const (6 : ℂ)
    rw [← ha] at h
    convert h using 1 <;> try rfl
    rw [h₂, h₃, h₄]
    apply (eq_div_iff (by norm_num : (6 : ℂ) ≠ 0)).mpr
    apply (eq_div_iff (pow_ne_zero 2 (hh₁ x))).mpr
    ring

end Zalcman
