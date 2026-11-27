/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Area
public import Zalcman.LogarithmicCoefficients
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The normalized translates on a real diameter

The disk automorphisms along a real diameter form the hyperbolic translation
group. Their normalized Koebe transforms retain univalence and express the
radial trace at an increment of hyperbolic distance.
-/

@[expose] public section

noncomputable section

namespace Zalcman

open OAI.Brennan (disk diskAutomorphism diskKoebe)

/-- The radial trace in hyperbolic coordinates. -/
def radialTrace (f : ℂ → ℂ) (x : ℝ) : ℂ := f (Real.tanh x : ℂ)

/-- The normalized translate based at the hyperbolic coordinate `x`. -/
def hyperbolicTranslate (f : ℂ → ℂ) (x : ℝ) : ℂ → ℂ := diskKoebe f (Real.tanh x : ℂ)

theorem tanh_mem_unitDisk (x : ℝ) : (Real.tanh x : ℂ) ∈ unitDisk := by
  rw [mem_unitDisk, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_tanh_lt_one x

/-- A normalized hyperbolic translate belongs to the same univalent class. -/
theorem NormalizedUnivalent.hyperbolicTranslate {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    (x : ℝ) : NormalizedUnivalent (Zalcman.hyperbolicTranslate f x) := by
  have hx : (Real.tanh x : ℂ) ∈ disk := tanh_mem_unitDisk x
  have h := OAI.Brennan.diskKoebe_schlicht ⟨hf.holomorphic, hf.injective⟩ hx
    (hf.deriv_ne_zero (tanh_mem_unitDisk x))
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

theorem hasDerivAt_real_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hcosh := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hcosh
  have hfun : Real.tanh = fun t => Real.sinh t / Real.cosh t := funext Real.tanh_eq_sinh_div_cosh
  rw [hfun]
  convert h using 1
  field_simp

set_option backward.isDefEq.respectTransparency false in
/-- Derivative of the radial trace with respect to the hyperbolic coordinate. -/
theorem hasDerivAt_radialTrace_of_differentiableOn {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisk) (x : ℝ) :
    HasDerivAt (radialTrace f) ((1 - (Real.tanh x : ℂ) ^ 2) * deriv f (Real.tanh x : ℂ)) x := by
  have hf' := (hf.differentiableAt
    (unitDisk_isOpen.mem_nhds (tanh_mem_unitDisk x))).hasDerivAt.comp_ofReal
  have h := hf'.scomp x (hasDerivAt_real_tanh x)
  unfold radialTrace
  simpa only [Function.comp_def, Complex.real_smul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_pow] using h

/-- Derivative of the trace of a normalized univalent map. -/
theorem hasDerivAt_radialTrace {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (x : ℝ) :
    HasDerivAt (radialTrace f) ((1 - (Real.tanh x : ℂ) ^ 2) * deriv f (Real.tanh x : ℂ)) x :=
  hasDerivAt_radialTrace_of_differentiableOn hf.holomorphic x

private theorem tanh_add_formula (x y : ℝ) :
    Real.tanh (x + y) = (Real.tanh x + Real.tanh y) / (1 + Real.tanh x * Real.tanh y) := by
  simp only [Real.tanh_eq_sinh_div_cosh, Real.sinh_add, Real.cosh_add]
  have h₁ := (Real.cosh_pos x).ne'
  have h₂ := (Real.cosh_pos y).ne'
  have h₃ : Real.cosh x * Real.cosh y + Real.sinh x * Real.sinh y ≠ 0 := by
    rw [← Real.cosh_add]
    exact (Real.cosh_pos _).ne'
  field_simp

/-- Addition of hyperbolic coordinates is exactly composition with the normalized translate. -/
theorem radialTrace_add {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (x v : ℝ) :
    radialTrace f (x + v) = radialTrace f x + deriv (radialTrace f) x *
      hyperbolicTranslate f x (Real.tanh v : ℂ) := by
  let t := Real.tanh x
  have hD := (hasDerivAt_radialTrace hf x).deriv
  have hL : (1 - (t : ℂ) ^ 2) * deriv f (t : ℂ) ≠ 0 := by
    apply mul_ne_zero _ (hf.deriv_ne_zero (tanh_mem_unitDisk x))
    exact_mod_cast (sub_pos.mpr (Real.tanh_sq_lt_one x)).ne'
  have hMap : diskAutomorphism (t : ℂ) (Real.tanh v : ℂ) = (Real.tanh (x + v) : ℂ) := by
    simp only [diskAutomorphism, Complex.conj_ofReal, tanh_add_formula, Complex.ofReal_div,
      Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul, t]
    rw [add_comm (Real.tanh v : ℂ)]
  rw [hD, hyperbolicTranslate, diskKoebe, hMap]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.ofReal_pow]
  change f (Real.tanh (x + v) : ℂ) = f (t : ℂ) +
    ((1 - (t : ℂ) ^ 2) * deriv f (t : ℂ)) *
      ((f (Real.tanh (x + v) : ℂ) - f (t : ℂ)) / ((1 - (t : ℂ) ^ 2) * deriv f (t : ℂ)))
  rw [mul_div_cancel₀ _ hL]
  ring

/-- In hyperbolic coordinates the Koebe expression has exact exponential growth. -/
theorem koebe_tanh_eq (x : ℝ) :
    koebe (Real.tanh x : ℂ) = ((Real.exp (4 * x) - 1) / 4 : ℝ) := by
  unfold koebe
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_div]
  apply congrArg Complex.ofReal
  rw [Real.tanh_eq]
  let a := Real.exp x
  let b := Real.exp (-x)
  have hp : 0 < a + b := add_pos (Real.exp_pos _) (Real.exp_pos _)
  have hb : b ≠ 0 := (Real.exp_pos _).ne'
  have heq : 1 - (a - b) / (a + b) = (2 * b) / (a + b) := by
    field_simp
    ring
  change (a - b) / (a + b) / (1 - (a - b) / (a + b)) ^ 2 = (Real.exp (4 * x) - 1) / 4
  have hex : (a / b) ^ 2 = Real.exp (4 * x) := by
    dsimp only [a, b]
    rw [← Real.exp_sub, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [heq, ← hex]
  field_simp; ring

end Zalcman
