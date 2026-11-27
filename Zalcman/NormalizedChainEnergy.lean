/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.ChainEnergy
public import Zalcman.CoefficientRegularity
public import Zalcman.KoebeLogCoeff
public import Zalcman.LoewnerLogODE
public import Zalcman.MilinRepresentation
import Mathlib.Tactic.Ring

/-!
# Milin representations from normalized Löwner chains

A compact time interval of a normalized chain suffices when its terminal map is Koebe.
Taylor coefficient regularity and the logarithmic velocity supply the hypotheses of the
finite energy identity. The common triangular representation then passes to limits of
the initial maps.
-/

public section

namespace Zalcman

open Filter MeasureTheory Set
open scoped BigOperators NNReal Topology

/-- A normalized chain terminating at Koebe, with uniform time regularity on a circle
and the radial logarithmic velocity almost everywhere. -/
structure KoebeTerminatingLogarithmicChain where
  maps : ℝ → ℂ → ℂ
  normalized : ∀ t, NormalizedUnivalent (maps t)
  duration : ℝ
  duration_nonneg : 0 ≤ duration
  terminal : EqOn (maps duration) koebe unitDisk
  driver : ℝ → ℂ
  time_lipschitz : ∃ K r : ℝ≥0, 0 < r ∧ (r : ℝ) < 1 ∧
    ∀ z ∈ Metric.sphere (0 : ℂ) r,
      LipschitzOnWith K (fun t ↦ maps t z) (Icc 0 duration)
  logarithmic_velocity :
    ∀ᵐ u : ℝ ∂volume, u ∈ Ioc 0 duration → ‖driver u‖ = 1 ∧
      TendstoLocallyUniformlyOn
        (fun t z ↦ slope (fun s ↦ normalizedLogarithm (normalized s) z) u t)
        (fun z ↦ (1 + z * deriv (normalizedLogarithm (normalized u)) z) *
          radialDriver (driver u) z - 1) (𝓝[≠] u) unitDisk

private theorem coeff_half_eq_div (L : ℂ → ℂ) (n : ℕ) :
    coeff (fun z ↦ L z / 2) n = coeff L n / 2 := by
  have hL : (fun z ↦ L z / 2) = fun z ↦ (2 : ℂ)⁻¹ * L z := by
    funext z
    ring
  rw [hL, coeff_const_mul]
  ring

/-- The initial map of a Koebe-terminating chain has a positive Milin representation. -/
theorem KoebeTerminatingLogarithmicChain.initial_milin_representation
    (P : KoebeTerminatingLogarithmicChain) :
    ∃ rho : ℕ → ℝ, rho 0 = 0 ∧ (∀ j, 0 ≤ rho j) ∧ ∀ M,
      (∑ j ∈ Finset.range (M + 1), connectionCoefficient M j * rho j) =
        (milinCoefficients (P.normalized 0)).milinSum (M + 1) := by
  let L (t : ℝ) : ℂ → ℂ := normalizedLogarithm (P.normalized t)
  let γ (k : ℕ) (t : ℝ) : ℂ := coeff (fun z ↦ L t z / 2) (k + 1)
  have hTaylorAC (n : ℕ) :
      AbsolutelyContinuousOnInterval (fun t ↦ coeff (P.maps t) n) 0 P.duration := by
    obtain ⟨K, r, hr, hr₁, hLip⟩ := P.time_lipschitz
    rw [← uIcc_of_le P.duration_nonneg] at hLip
    exact (lipschitzOnWith_coeff hr hr₁ (fun t _ ↦ (P.normalized t).holomorphic)
      hLip n).absolutelyContinuousOnInterval
  refine exists_nonnegative_triangular_milin_representation_of_logCoeffChain
    (milinCoefficients (P.normalized 0)) γ P.driver P.duration_nonneg ?_ ?_ ?_ ?_
  · intro k
    simp only [milinCoefficients, logCoeff, Nat.cast_succ, γ, L]
  · exact fun k ↦ coeff_half_normalizedLogarithm_eq_inv_of_eqOn_koebe
      (P.normalized P.duration) P.terminal k
  · exact absolutelyContinuousOnInterval_halfLogCoeff P.normalized hTaylorAC
  · filter_upwards [P.logarithmic_velocity] with u hu ht
    obtain ⟨hκ, hSlope⟩ := hu ht
    refine ⟨hκ, fun k ↦ ?_⟩
    have hκle : ‖P.driver u‖ ≤ 1 := hκ.le
    have hD := hasDerivAt_radialLogCoeff hκle
      (fun t ↦ normalizedLogarithm_holomorphic (P.normalized t)) hSlope k
    simpa only [γ, L, coeff_half_eq_div] using hD

/-- A locally uniform limit of the initial maps of Koebe-terminating chains has the same
positive triangular representation of its Milin sums. -/
theorem exists_nonnegative_milin_representation_of_locallyUniform_chain_limits
    {ι : Type*} {l : Filter ι} [NeBot l]
    (P : ι → KoebeTerminatingLogarithmicChain) {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    (hlim : TendstoLocallyUniformlyOn (fun i ↦ (P i).maps 0) f l unitDisk) :
    ∃ rho : ℕ → ℝ, rho 0 = 0 ∧ (∀ j, 0 ≤ rho j) ∧ ∀ M,
      (∑ j ∈ Finset.range (M + 1), connectionCoefficient M j * rho j) =
        (milinCoefficients hf).milinSum (M + 1) := by
  refine exists_nonnegative_milin_representation_of_tendsto hlim
    (fun i ↦ (P i).normalized 0) hf (B := connectionCoefficient) ?_ ?_
  · intro M
    rw [connectionCoefficient_diagonal]
    have hchoose : ((2 * M).choose M : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : M ≤ 2 * M)).ne'
    exact div_ne_zero (pow_ne_zero _ (by norm_num)) hchoose
  · intro i
    obtain ⟨rho, _, hpos, hrep⟩ := (P i).initial_milin_representation
    exact ⟨rho, hpos, hrep⟩

end Zalcman
