/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CyclicStability
public import Zalcman.CyclicWrap
public import Zalcman.GeometricExtension
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

namespace Zalcman

open Finset
open scoped ComplexConjugate

private theorem cyclicCorrelation_norm_ge {m : ℕ} [NeZero m] (b : ZMod m → ℂ)
    (h : ZMod m) {v : ℂ} (hv : ‖v‖ = 1) {E : ℝ}
    (he : (∑ j, ‖b (j + h) - v * b j‖ ^ 2) ≤ 4 * E) :
    (∑ j, ‖b j‖ ^ 2) - 2 * E ≤ ‖cyclicCorrelation b h‖ := by
  have hterm (j : ZMod m) : ‖b (j + h) - v * b j‖ ^ 2 =
      ‖b (j + h)‖ ^ 2 + ‖b j‖ ^ 2 - 2 * (conj v * (b (j + h) * conj (b j))).re := by
    have hcross : b (j + h) * conj (v * b j) = conj v * (b (j + h) * conj (b j)) := by
      rw [map_mul]
      ring
    rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      norm_mul, hv, one_mul, hcross]
  have hm : (∑ j, ‖b (j + h)‖ ^ 2) = ∑ j, ‖b j‖ ^ 2 := Fintype.sum_equiv (Equiv.addRight h) _ _
    (fun _ => rfl)
  simp only [hterm, sum_sub_distrib, sum_add_distrib, hm, ← mul_sum, ← Complex.re_sum] at he
  change (∑ j, ‖b j‖ ^ 2) + (∑ j, ‖b j‖ ^ 2) -
    2 * (conj v * cyclicCorrelation b h).re ≤ 4 * E at he
  have hnorm := Complex.re_le_norm (conj v * cyclicCorrelation b h)
  rw [norm_mul, Complex.norm_conj, hv, one_mul] at hnorm
  linarith only [he, hnorm]

/-- A block with controlled shifts is close to one geometric mode. -/
theorem exists_geometric_approximation_of_shifts (c : ℕ → ℂ) {n H : ℕ}
    (hH : 0 < H) (hnlo : 2 * H ≤ n) (hnhi : n ≤ 2 * H + 1) {E : ℝ} (hE : 0 ≤ E)
    (hshift : ∀ h ≤ H, ∃ v : ℂ, ‖v‖ = 1 ∧
      (∑ j ∈ range (n - h), ‖c (j + h) - v * c j‖ ^ 2) ≤ E) :
    ∃ (β lam : ℂ), ‖lam‖ = 1 ∧ (∑ j ∈ range n, ‖c j - β * lam ^ j‖ ^ 2) ≤ 34 * E := by
  let : NeZero H := ⟨hH.ne'⟩
  obtain ⟨vH, hunitH, hsvH⟩ := hshift H le_rfl
  let θ : ℝ := Complex.arg vH / (H : ℝ)
  let τ := Complex.exp ((θ : ℂ) * Complex.I)
  have hτ : ‖τ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hθ : (H : ℝ) * θ = Complex.arg vH := by
    dsimp only [θ]
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hH.ne')
  have hθComplex : (H : ℂ) * (θ : ℂ) = (Complex.arg vH : ℂ) := by
    exact_mod_cast hθ
  have hτH : τ ^ H = vH := by
    dsimp only [τ]
    rw [← Complex.exp_nat_mul, ← mul_assoc, hθComplex]
    simpa only [hunitH, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I vH
  have hτUnit : conj τ * τ = 1 := by
    rw [Complex.conj_mul', hτ]
    norm_num
  let b := cyclicPrefix (H := H) c τ
  have hcorr (h : ZMod H) : (∑ j, ‖b j‖ ^ 2) - 2 * E ≤ ‖cyclicCorrelation b h‖ := by
    obtain ⟨v, hv, he⟩ := hshift h.val (ZMod.val_lt h).le
    have hV : ‖conj τ ^ h.val * v‖ = 1 := by simp [norm_pow, hτ, hv]
    exact cyclicCorrelation_norm_ge b h hV (sum_cyclicPrefix_shift_le c hnlo hτ hτH h he hsvH)
  obtain ⟨k, β, hβ⟩ := exists_mode_error_le b (E := 2 * E) (by positivity) hcorr
  let ξ : ℂ := ZMod.stdAddChar k
  let lam := τ * ξ
  have hξ : ‖ξ‖ = 1 := by rw [show ξ = ZMod.stdAddChar k from rfl, ZMod.stdAddChar_apply, Circle.norm_coe]
  have hlam : ‖lam‖ = 1 := by simp [lam, hτ, hξ]
  have hξpow : ξ ^ H = 1 := by
    rw [show ξ = ZMod.stdAddChar k from rfl, ← AddChar.map_nsmul_eq_pow,
      nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
  have hlamH : lam ^ H = vH := by rw [show lam = τ * ξ from rfl, mul_pow, hτH, hξpow, mul_one]
  have hβ' : (∑ j ∈ range H, ‖c j - β * lam ^ j‖ ^ 2) ≤ 4 * E := by
    rw [sum_zmod_eq_sum_range] at hβ
    have hEquiv (j : ℕ) (hj : j < H) :
        b (j : ZMod H) - β * ZMod.stdAddChar ((j : ZMod H) * k) = conj τ ^ j * (c j - β * lam ^ j) := by
      have hchar : ZMod.stdAddChar ((j : ZMod H) * k) = ξ ^ j := by
        rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
      have hUn : conj τ ^ j * τ ^ j = 1 := by rw [← mul_pow, hτUnit, one_pow]
      rw [hchar, show b (j : ZMod H) = conj τ ^ j * c j by
        simp [b, cyclicPrefix, ZMod.val_natCast_of_lt hj],
        mul_sub, show lam ^ j = τ ^ j * ξ ^ j by simp [lam, mul_pow]]
      calc
        _ = conj τ ^ j * c j - (conj τ ^ j * τ ^ j) * (β * ξ ^ j) := by rw [hUn, one_mul]
        _ = _ := by ring
    have hh : (∑ j ∈ range H, ‖b (j : ZMod H) - β * ZMod.stdAddChar ((j : ZMod H) * k)‖ ^ 2) =
        ∑ j ∈ range H, ‖c j - β * lam ^ j‖ ^ 2 := by
      apply sum_congr rfl
      intro j hj
      rw [hEquiv j (mem_range.mp hj), norm_mul, norm_pow, Complex.norm_conj, hτ, one_pow, one_mul]
    rw [hh] at hβ
    linarith only [hβ]
  exact ⟨β, lam, hlam,
    (geometric_error_le_of_half_block c hH hnlo hnhi hunitH hlamH hβ' hsvH).trans_eq (by ring)⟩

end Zalcman
