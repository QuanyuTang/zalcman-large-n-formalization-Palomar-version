/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Basic
public import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Taylor coefficients of a composition at a fixed origin

Each term in a composed coefficient is indexed by a composition of its degree.
Isolating the one-block composition gives a triangular rule for the coefficients
of a radial transition map.
-/

public section

namespace Zalcman

open Finset

set_option backward.isDefEq.respectTransparency false in
private theorem hasFPowerSeriesAt_coeff {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ (coeff f)) 0 := by
  have he : (fun n : ℕ => iteratedDeriv n f 0 / (n.factorial : ℂ)) = coeff f := by
    funext n
    rw [coeff, div_eq_mul_inv, mul_comm]
  rw [← he]
  exact hf.hasFPowerSeriesAt

/-- The exact Taylor composition rule when the inner map fixes zero. -/
theorem coeff_comp {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (h₀ : g 0 = 0)
    (n : ℕ) : coeff (f ∘ g) n =
      ∑ c : Composition n, coeff f c.length * ∏ i : Fin c.length, coeff g (c.blocksFun i) := by
  let a := FormalMultilinearSeries.ofScalars ℂ (coeff f)
  let b := FormalMultilinearSeries.ofScalars ℂ (coeff g)
  have ha : HasFPowerSeriesAt f a (g 0) := h₀.symm ▸ hasFPowerSeriesAt_coeff hf
  have hb : HasFPowerSeriesAt g b 0 := hasFPowerSeriesAt_coeff hg
  have hcomp := ha.comp hb
  have hcomp' := hasFPowerSeriesAt_coeff hcomp.analyticAt
  have he := hcomp'.eq_formalMultilinearSeries hcomp
  have hs := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) he
  calc
    _ = (a.comp b).coeff n := by simpa only [FormalMultilinearSeries.coeff_ofScalars] using hs
    _ = _ := by
      change (∑ c : Composition n, a.compAlongComposition b c) (fun _ => 1) = _
      rw [_root_.sum_apply]
      apply sum_congr rfl
      intro c _
      simp only [FormalMultilinearSeries.compAlongComposition_apply,
        FormalMultilinearSeries.applyComposition, Function.comp_def, a, b,
        FormalMultilinearSeries.apply_eq_prod_smul_coeff, FormalMultilinearSeries.coeff_ofScalars,
        smul_eq_mul, prod_const, card_univ, Fintype.card_fin, one_pow, one_mul, mul_comm]

/-- The only term using the inner coefficient at the full order is linear in it. -/
theorem coeff_comp_eq_linear_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (h₀ : g 0 = 0) {n : ℕ} (hn : 0 < n) :
    coeff (f ∘ g) n = coeff f 1 * coeff g n +
      ∑ c ∈ (univ : Finset (Composition n)).erase (Composition.single n hn),
        coeff f c.length * ∏ i : Fin c.length, coeff g (c.blocksFun i) := by
  classical
  rw [coeff_comp hf hg h₀]
  rw [← add_sum_erase univ _ (mem_univ (Composition.single n hn))]
  have hp : (∏ i : Fin (Composition.single n hn).length,
      coeff g ((Composition.single n hn).blocksFun i)) =
      ∏ _ : Fin (Composition.single n hn).length, coeff g n := by
    exact prod_congr rfl (fun i _ => by rw [Composition.single_blocksFun])
  have hp₁ : (∏ _ : Fin (Composition.single n hn).length, coeff g n) = coeff g n := calc
    _ = ∏ _ : Fin 1, coeff g n := by rw [Composition.single_length]
    _ = _ := Fin.prod_univ_one _
  rw [hp, hp₁, Composition.single_length]

/-- Every inner coefficient in the triangular remainder has strictly lower order. -/
theorem composition_blocksFun_lt_of_mem_erase {n : ℕ} (hn : 0 < n) {c : Composition n}
    (hc : c ∈ (univ : Finset (Composition n)).erase (Composition.single n hn))
    (i : Fin c.length) : c.blocksFun i < n :=
  (Composition.ne_single_iff hn).mp (ne_of_mem_erase hc) i

end Zalcman
