/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.WeightIdentity
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The pointwise derivative in the de Branges–Weinstein identity

Index `k` denotes the manuscript coefficient with index `k + 1`.
The logarithmic coefficient equations determine a phase-adjusted velocity.
The ordinary product rule and the finite weighted identity then give the
derivative of the weighted potential.
-/

@[expose] public section

noncomputable section

namespace Zalcman

open Finset
open scoped BigOperators ComplexConjugate

/-- The logarithmic coefficient multiplied by its index and the corresponding conjugate phase. -/
def phasedLogCoeff (g : ℕ → ℂ) (κ : ℂ) (k : ℕ) : ℂ :=
  ((k : ℂ) + 1) * g k * conj κ ^ (k + 1)

/-- The sequence starting at one and increasing by twice each phased coefficient. -/
def logPhaseSum (g : ℕ → ℂ) (κ : ℂ) (k : ℕ) : ℂ :=
  1 + 2 * ∑ j ∈ range k, phasedLogCoeff g κ j

@[simp]
theorem logPhaseSum_zero (g : ℕ → ℂ) (κ : ℂ) : logPhaseSum g κ 0 = 1 := by
  simp [logPhaseSum]

theorem logPhaseSum_succ_sub (g : ℕ → ℂ) (κ : ℂ) (k : ℕ) :
    logPhaseSum g κ (k + 1) - logPhaseSum g κ k = 2 * phasedLogCoeff g κ k := by
  simp only [logPhaseSum, sum_range_succ]
  ring

private lemma conj_mul_eq_one {κ : ℂ} (hκ : ‖κ‖ = 1) : conj κ * κ = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hκ]
  norm_num

private lemma conj_pow_mul_pow_eq_one {κ : ℂ} (hκ : ‖κ‖ = 1) (k : ℕ) :
    conj κ ^ k * κ ^ k = 1 := by
  rw [← mul_pow, conj_mul_eq_one hκ, one_pow]

private lemma conj_pow_mul_pow_sub {κ : ℂ} (hκ : ‖κ‖ = 1) {j k : ℕ} (hjk : j ≤ k) :
    conj κ ^ (k + 1) * κ ^ (k - j) = conj κ ^ (j + 1) := by
  have h : k + 1 = (j + 1) + (k - j) := by omega
  rw [h, pow_add, mul_assoc, conj_pow_mul_pow_eq_one hκ, mul_one]

/-- A coefficient velocity from the logarithmic differential equation is an average of
successive phase sums after undoing its unit phase. -/
theorem phased_velocity_eq_average (g : ℕ → ℂ) {κ : ℂ} (hκ : ‖κ‖ = 1)
    (k : ℕ) {d : ℂ}
    (hd : d = κ ^ (k + 1) + ((k : ℂ) + 1) * g k +
      2 * ∑ j ∈ range k, ((j : ℂ) + 1) * g j * κ ^ (k - j)) :
    conj κ ^ (k + 1) * d = (logPhaseSum g κ (k + 1) + logPhaseSum g κ k) / 2 := by
  have hs : conj κ ^ (k + 1) * (∑ j ∈ range k, ((j : ℂ) + 1) * g j * κ ^ (k - j)) =
      ∑ j ∈ range k, phasedLogCoeff g κ j := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj ↦ ?_
    calc
      _ = ((j : ℂ) + 1) * g j * (conj κ ^ (k + 1) * κ ^ (k - j)) := by ring
      _ = _ := by rw [conj_pow_mul_pow_sub hκ (mem_range.mp hj).le, phasedLogCoeff]
  rw [hd]
  calc
    _ = conj κ ^ (k + 1) * κ ^ (k + 1) +
        conj κ ^ (k + 1) * (((k : ℂ) + 1) * g k) +
        2 * (conj κ ^ (k + 1) * (∑ j ∈ range k, ((j : ℂ) + 1) * g j * κ ^ (k - j))) := by
      ring
    _ = _ := by
      rw [conj_pow_mul_pow_eq_one hκ, hs]
      simp only [logPhaseSum, sum_range_succ, phasedLogCoeff]
      ring

private lemma hasDerivAt_complex_norm_sq {f : ℝ → ℂ} {d : ℂ} {u : ℝ}
    (h : HasDerivAt f d u) :
    HasDerivAt (fun t ↦ ‖f t‖ ^ 2) (2 * (d * conj (f u)).re) u := by
  have hre : HasDerivAt (fun t ↦ (f t).re) d.re u :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt u h
  have him : HasDerivAt (fun t ↦ (f t).im) d.im u :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt u h
  convert (hre.fun_mul hre).fun_add (him.fun_mul him) using 1
  · funext t
    rw [Complex.sq_norm, Complex.normSq_apply]
  · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring

private lemma re_mul_conj_phase_invariant {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (a : ℝ) (f d : ℂ) :
    ((ζ * d) * conj ((a : ℂ) * f * ζ)).re = a * (d * conj f).re := by
  rw [map_mul, map_mul, Complex.conj_ofReal]
  calc
    _ = (((a : ℂ) * (d * conj f)) * (conj ζ * ζ)).re := by congr 1; ring
    _ = _ := by rw [conj_mul_eq_one hζ, mul_one, Complex.re_ofReal_mul]

private lemma two_re_average_mul_conj_half_diff (a b : ℂ) :
    2 * (((b + a) / 2) * conj ((b - a) / 2)).re = (‖b‖ ^ 2 - ‖a‖ ^ 2) / 2 := by
  change 2 * (((b + a) / ((2 : ℝ) : ℂ)) * conj ((b - a) / ((2 : ℝ) : ℂ))).re =
    (‖b‖ ^ 2 - ‖a‖ ^ 2) / 2
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.div_ofReal_re,
    Complex.div_ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.sq_norm, Complex.normSq_apply]
  ring

private lemma norm_conj_phase_pow {κ : ℂ} (hκ : ‖κ‖ = 1) (n : ℕ) :
    ‖conj κ ^ n‖ = 1 := by
  rw [Complex.norm_pow, Complex.norm_conj, hκ, one_pow]

private lemma norm_phasedLogCoeff_sq (g : ℕ → ℂ) {κ : ℂ} (hκ : ‖κ‖ = 1) (k : ℕ) :
    ‖phasedLogCoeff g κ k‖ ^ 2 = ((k : ℝ) + 1) ^ 2 * ‖g k‖ ^ 2 := by
  have ha : 0 ≤ (k : ℝ) + 1 := by positivity
  unfold phasedLogCoeff
  have hcast : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by simp
  rw [hcast, norm_mul, norm_mul, norm_conj_phase_pow hκ, mul_one,
    Complex.norm_of_nonneg ha, mul_pow]

private lemma phasedLogCoeff_eq_half_diff (g : ℕ → ℂ) (κ : ℂ) (k : ℕ) :
    phasedLogCoeff g κ k = (logPhaseSum g κ (k + 1) - logPhaseSum g κ k) / 2 := by
  rw [logPhaseSum_succ_sub]
  ring

/-- The norm-square derivative of one logarithmic coefficient obeys the phase difference identity. -/
theorem hasDerivAt_logCoeff_energy (γ : ℕ → ℝ → ℂ) {κ : ℂ} (hκ : ‖κ‖ = 1)
    {u : ℝ} (k : ℕ) {d : ℂ} (hγ : HasDerivAt (γ k) d u)
    (hd : d = κ ^ (k + 1) + ((k : ℂ) + 1) * γ k u +
      2 * ∑ j ∈ range k, ((j : ℂ) + 1) * γ j u * κ ^ (k - j)) :
    HasDerivAt (fun t ↦ ((k : ℝ) + 1) * ‖γ k t‖ ^ 2)
      ((‖logPhaseSum (fun j ↦ γ j u) κ (k + 1)‖ ^ 2 -
        ‖logPhaseSum (fun j ↦ γ j u) κ k‖ ^ 2) / 2) u := by
  let g := fun j ↦ γ j u
  let v := logPhaseSum g κ
  have hre :
      ((conj κ ^ (k + 1) * d) * conj (phasedLogCoeff g κ k)).re =
        ((k : ℝ) + 1) * (d * conj (γ k u)).re := by
    simpa only [phasedLogCoeff, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one, g] using
      re_mul_conj_phase_invariant (norm_conj_phase_pow hκ (k + 1)) ((k : ℝ) + 1) (γ k u) d
  rw [phased_velocity_eq_average g hκ k hd, phasedLogCoeff_eq_half_diff] at hre
  have henergy :
      ((k : ℝ) + 1) * (2 * (d * conj (γ k u)).re) =
        (‖v (k + 1)‖ ^ 2 - ‖v k‖ ^ 2) / 2 := calc
    _ = 2 * (((k : ℝ) + 1) * (d * conj (γ k u)).re) := by ring
    _ = 2 * (((v (k + 1) + v k) / 2) * conj ((v (k + 1) - v k) / 2)).re :=
      congrArg (fun r : ℝ ↦ 2 * r) hre.symm
    _ = _ := two_re_average_mul_conj_half_diff (v k) (v (k + 1))
  rw [← henergy]
  exact (hasDerivAt_complex_norm_sq hγ).const_mul ((k : ℝ) + 1)

/-- The finite de Branges–Weinstein potential for the first `M` coefficients. -/
def weightedLogEnergy (γ : ℕ → ℝ → ℂ) (τ : ℕ → ℝ → ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ range M, τ k t * (((k : ℝ) + 1) * ‖γ k t‖ ^ 2 - 1 / ((k : ℝ) + 1))

/-- The pointwise derivative of the weighted potential, assuming the coefficient and weight
equations at the point where all derivatives are taken. -/
theorem hasDerivAt_weightedLogEnergy (γ : ℕ → ℝ → ℂ) (τ : ℕ → ℝ → ℝ)
    (L : ℕ → ℝ) (d : ℕ → ℂ) {κ : ℂ} (hκ : ‖κ‖ = 1) (M : ℕ) {u : ℝ}
    (hγ : ∀ k < M, HasDerivAt (γ k) (d k) u)
    (hd : ∀ k < M, d k = κ ^ (k + 1) + ((k : ℂ) + 1) * γ k u +
      2 * ∑ j ∈ range k, ((j : ℂ) + 1) * γ j u * κ ^ (k - j))
    (hτ : ∀ k < M, HasDerivAt (τ k) (-((k : ℝ) + 1) * L k) u)
    (hτ_sub : ∀ k < M, τ k u - τ (k + 1) u = L k + L (k + 1))
    (hτM : τ M u = 0) (hLM : L M = 0) :
    HasDerivAt (weightedLogEnergy γ τ M) (∑ k ∈ range M, L k * ‖d k‖ ^ 2) u := by
  let g := fun j ↦ γ j u
  let v := logPhaseSum g κ
  have hterm (k : ℕ) (hk : k ∈ range M) :
      HasDerivAt (fun t ↦ τ k t * (((k : ℝ) + 1) * ‖γ k t‖ ^ 2 - 1 / ((k : ℝ) + 1)))
        (τ k u * (‖v (k + 1)‖ ^ 2 - ‖v k‖ ^ 2) / 2 +
          L k * (1 - ‖(v (k + 1) - v k) / 2‖ ^ 2)) u := by
    have hk' := mem_range.mp hk
    have hγk := hasDerivAt_logCoeff_energy γ hκ k (hγ k hk') (hd k hk')
    have hτk := hτ k hk'
    have hpoint := hτk.fun_mul (hγk.sub_const (1 / ((k : ℝ) + 1)))
    have heq :
        (-((k : ℝ) + 1) * L k) * (((k : ℝ) + 1) * ‖γ k u‖ ^ 2 - 1 / ((k : ℝ) + 1)) +
            τ k u * ((‖v (k + 1)‖ ^ 2 - ‖v k‖ ^ 2) / 2) =
          τ k u * (‖v (k + 1)‖ ^ 2 - ‖v k‖ ^ 2) / 2 +
            L k * (1 - ‖(v (k + 1) - v k) / 2‖ ^ 2) := by
      have ha : (k : ℝ) + 1 ≠ 0 := by positivity
      rw [show (v (k + 1) - v k) / 2 = phasedLogCoeff g κ k from
        (phasedLogCoeff_eq_half_diff g κ k).symm, norm_phasedLogCoeff_sq g hκ]
      dsimp only [g, v]
      field_simp <;> ring
    have hpoint' :
        HasDerivAt (fun t ↦ τ k t * (((k : ℝ) + 1) * ‖γ k t‖ ^ 2 - 1 / ((k : ℝ) + 1)))
          ((-((k : ℝ) + 1) * L k) *
              (((k : ℝ) + 1) * ‖γ k u‖ ^ 2 - 1 / ((k : ℝ) + 1)) +
            τ k u * ((‖v (k + 1)‖ ^ 2 - ‖v k‖ ^ 2) / 2)) u := hpoint
    rwa [heq] at hpoint'
  have hv0 : ‖v 0‖ = 1 := by simp [v]
  have halgebra := weighted_coefficient_energy v (fun k ↦ τ k u) L M hv0 hτ_sub hτM hLM
  have hvel :
      ∑ k ∈ range M, L k * ‖(v (k + 1) + v k) / 2‖ ^ 2 =
        ∑ k ∈ range M, L k * ‖d k‖ ^ 2 := by
    refine sum_congr rfl fun k hk ↦ ?_
    rw [show (v (k + 1) + v k) / 2 = conj κ ^ (k + 1) * d k from
      (phased_velocity_eq_average g hκ k (hd k (mem_range.mp hk))).symm,
      norm_mul, norm_conj_phase_pow hκ, one_mul]
  rw [← hvel, ← halgebra]
  unfold weightedLogEnergy
  exact HasDerivAt.fun_sum hterm

end Zalcman
