/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Basic
public import Zalcman.Reduction

/-!
# Equality for rotations of the Koebe function

The Koebe coefficient formula gives the equality direction of the conjecture
at every positive index.
-/

public section

namespace Zalcman

/-- A rotation of the Koebe function realizes the Zalcman bound. -/
theorem zalcman_eq_of_isKoebeRotation {f : ℂ → ℂ} (hf : IsKoebeRotation f)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff f n ^ 2 - coeff f (2 * n - 1)‖ = ((n : ℝ) - 1) ^ 2 := by
  obtain ⟨lam, hlam, ha⟩ := hf.coefficients
  rw [ha n hn, ha (2 * n - 1) (by omega)]
  exact koebe_pair_norm hn hlam

end Zalcman
