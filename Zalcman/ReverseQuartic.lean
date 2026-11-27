/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Fourth-order coefficient equations in Koebe coordinates

The first three coefficients after the linear term in the Koebe-coordinate
germ are polynomial expressions in the first three ordinary coefficients.
The reverse-time system transforms by differentiating those expressions.
-/

@[expose] public section

namespace Zalcman

/-- The degree-two coefficient in the reverse Koebe coordinate. -/
def koebeGermTwo (b₂ : ℝ → ℂ) (t : ℝ) : ℂ := (t : ℂ) * (b₂ t - 2)

/-- The degree-three coefficient in the reverse Koebe coordinate. -/
def koebeGermThree (b₂ b₃ : ℝ → ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ 2 * (b₃ t - 4 * b₂ t + 5)

/-- The degree-four coefficient in the reverse Koebe coordinate. -/
def koebeGermFour (b₂ b₃ b₄ : ℝ → ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ 3 * (b₄ t - 6 * b₃ t + 14 * b₂ t - 14)

/-- The coefficient at order two of the reverse velocity field. -/
def koebeVelocityTwo (η : ℂ) : ℂ := 2 * (η - 1)

/-- The coefficient at order three of the reverse velocity field. -/
def koebeVelocityThree (η : ℂ) (t : ℝ) : ℂ := -2 * (t : ℂ) * (η ^ 2 - 1)

/-- The coefficient at order four of the reverse velocity field. -/
def koebeVelocityFour (η : ℂ) (t : ℝ) : ℂ := 2 * (t : ℂ) ^ 2 * (η ^ 2 - 1) * (η + 2)

set_option backward.isDefEq.respectTransparency false in
private lemma hasDerivAt_ofReal_id (t : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
  simpa only [id, Complex.ofReal_one] using (hasDerivAt_id t).ofReal_comp

/-- The triangular reverse coefficient equations have the stated Koebe-coordinate form. -/
theorem hasDerivAt_koebeGerm {b₂ b₃ b₄ : ℝ → ℂ} {η : ℂ} {t : ℝ} (ht : t ≠ 0)
    (h₂ : HasDerivAt b₂ ((-b₂ t + 2 * η) / (t : ℂ)) t)
    (h₃ : HasDerivAt b₃ ((-2 * b₃ t + 4 * η * b₂ t - 2 * η ^ 2) / (t : ℂ)) t)
    (h₄ : HasDerivAt b₄ ((-3 * b₄ t + 6 * η * b₃ t - 4 * η ^ 2 * b₂ t + 2 * η ^ 3) /
      (t : ℂ)) t) :
    HasDerivAt (koebeGermTwo b₂) (koebeVelocityTwo η) t ∧
    HasDerivAt (koebeGermThree b₂ b₃)
      (koebeVelocityThree η t + 2 * koebeVelocityTwo η * koebeGermTwo b₂ t) t ∧
    HasDerivAt (koebeGermFour b₂ b₃ b₄)
      (koebeVelocityFour η t + 2 * koebeVelocityThree η t * koebeGermTwo b₂ t +
        3 * koebeVelocityTwo η * koebeGermThree b₂ b₃ t) t := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have ht' := hasDerivAt_ofReal_id t
  refine ⟨?_, ?_, ?_⟩
  · convert ht'.fun_mul (h₂.sub_const (2 : ℂ)) using 1 <;> try rfl
    simp only [koebeVelocityTwo]
    field_simp [htc]
    ring
  · have hb := h₃.fun_sub (h₂.const_mul (4 : ℂ))
    convert (ht'.pow 2).fun_mul (hb.add_const (5 : ℂ)) using 1 <;> try rfl
    simp only [koebeVelocityThree, koebeVelocityTwo, koebeGermTwo]
    norm_num
    field_simp [htc]
    ring
  · have hb := (h₄.fun_sub (h₃.const_mul (6 : ℂ))).fun_add (h₂.const_mul (14 : ℂ))
    convert (ht'.pow 3).fun_mul (hb.sub_const (14 : ℂ)) using 1 <;> try rfl
    simp only [koebeVelocityFour, koebeVelocityThree, koebeVelocityTwo, koebeGermTwo, koebeGermThree]
    norm_num
    field_simp [htc]
    ring

/-- The fourth-order difference is the fixed linear combination of the terminal germ coefficients. -/
theorem reverse_quartic_difference_eq (b₂ b₃ b₄ : ℝ → ℂ) :
    b₄ 1 - 2 * b₂ 1 = 8 * koebeGermTwo b₂ 1 + 6 * koebeGermThree b₂ b₃ 1 +
      koebeGermFour b₂ b₃ b₄ 1 := by
  simp only [koebeGermTwo, koebeGermThree, koebeGermFour, Complex.ofReal_one, one_pow, one_mul]
  ring

end Zalcman
