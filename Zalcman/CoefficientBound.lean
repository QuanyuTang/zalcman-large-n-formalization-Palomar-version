/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.LogarithmicCoefficients
public import Zalcman.Milin

/-!
# Taylor coefficients and the Milin sums

This file identifies the finite Lebedev–Milin calculation with the Taylor expansion of
a normalized univalent function. Nonnegativity of the Milin sums is the analytic input.
-/

@[expose] public section

namespace Zalcman

/-- The square-root and logarithmic Taylor coefficients of a normalized univalent function. -/
noncomputable def milinCoefficients {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    MilinCoefficients where
  c := rootCoeff hf
  t := logCoeff hf
  c_zero := rootCoeff_zero hf
  recursion j := by
    cases j with
    | zero => simp
    | succ n => simpa only [Nat.cast_succ] using (rootCoeff_succ_eq_sum_logCoeff hf n).symm

lemma milinCoefficients_squareCoeff {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ) :
    (milinCoefficients hf).squareCoeff n = coeff f n := by
  cases n with
  | zero => simp [MilinCoefficients.squareCoeff, hf.map_zero]
  | succ n => simpa [MilinCoefficients.squareCoeff, milinCoefficients] using
      (coeff_succ_eq_sum_rootCoeff hf n).symm

/-- A nonnegative Milin sum gives the coefficient bound at that index. -/
theorem norm_coeff_le_of_milinSum_nonneg {f : ℂ → ℂ} (hf : NormalizedUnivalent f) {n : ℕ}
    (hT : 0 ≤ (milinCoefficients hf).milinSum n) : ‖coeff f n‖ ≤ n := by
  cases n with
  | zero => simp [hf.map_zero]
  | succ n =>
    rw [← milinCoefficients_squareCoeff hf]
    exact (milinCoefficients hf).norm_squareCoeff_le_index (Nat.succ_pos _) hT

/-- Equality in the coefficient bound at any index `n ≥ 2` forces second-coefficient equality,
provided the Milin sum is nonnegative at that index. -/
theorem norm_coeff_two_eq_of_norm_coeff_eq {f : ℂ → ℂ} (hf : NormalizedUnivalent f) {n : ℕ}
    (hn : 2 ≤ n) (hT : 0 ≤ (milinCoefficients hf).milinSum n) (heq : ‖coeff f n‖ = n) :
    ‖coeff f 2‖ = 2 := by
  rw [← milinCoefficients_squareCoeff hf] at heq ⊢
  exact (milinCoefficients hf).norm_squareCoeff_two_of_norm_squareCoeff_eq_index hn hT heq

end Zalcman
