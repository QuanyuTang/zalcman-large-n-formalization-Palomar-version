/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.TargetPhase
public import Zalcman.PhaseAssembly
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Assembling quantitative estimates in rotated coordinates

The initial block estimate, radial deficit mass, and prefix phase estimates
are taken as analytic inputs. Their bounds can use one uniform multiplicative
constant, since the logarithm grows sublinearly.
-/

public section

namespace Zalcman

open Filter Finset
open scoped ComplexConjugate

private theorem exists_phase_mass_threshold {C : ℝ} (hC : 0 < C) :
    ∃ L : ℕ, ∀ n : ℕ, L ≤ n → 1 ≤ Real.log (n : ℝ) ∧
      192 * C * Real.log (n : ℝ) ≤ n := by
  have hLog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hSm := Real.isLittleO_log_id_atTop.def (show 0 < 1 / (192 * C) by positivity)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hLog.and hSm)
  obtain ⟨L, hL⟩ := exists_nat_ge x₀
  refine ⟨L, fun n hn => ?_⟩
  have ⟨hLog', hsmall⟩ := hx₀ (n : ℝ) (hL.trans (by exact_mod_cast hn))
  refine ⟨hLog', ?_⟩
  simp only [id, Real.norm_of_nonneg (zero_le_one.trans hLog'), Real.norm_of_nonneg (Nat.cast_nonneg n)] at hsmall
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 192 * C)] at hsmall
  nlinarith only [hsmall]

/-- The large-index bound follows from the triangular representation and the uniform
prefix and radial-mass estimates in the correct rotated coordinates. -/
theorem eventually_zalcman_of_representation_and_rotated_estimates
    (hR : ∀ {f : ℂ → ℂ} (hf : NormalizedUnivalent f),
      ∃ ρ : ℕ → ℝ, (∀ l, 0 ≤ ρ l) ∧
        ∀ M, positiveMilinRow ρ M = (milinCoefficients hf).milinSum (M + 1))
    {C : ℝ} {N₀ : ℕ} (hC : 0 < C)
    (hEst : ∀ {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ), N₀ ≤ n →
      let D := (n : ℝ) - ‖coeff f n‖
      D ≤ 3 → ∃ (lam : ℂ) (hlam : ‖lam‖ = 1) (α : ℂ), ‖α‖ = 1 ∧
        let g := rotate lam f
        let dg := milinCoefficients (rotate_normalizedUnivalent hf hlam)
        let M := C * D * Real.log (n : ℝ)
        let ω := coeff g n / (‖coeff g n‖ : ℂ)
        dg.blockError α n ≤ M ∧
          (∑ j ∈ (range (4 * n + 1)).filter Odd, dg.phaseDeficit α j) ≤ (n : ℝ) * M ∧
          ‖1 - α‖ ^ 2 + ‖ω - α ^ 2‖ ^ 2 ≤ M * Real.log (n : ℝ) / Real.sqrt (n : ℝ)) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ {f : ℂ → ℂ}, NormalizedUnivalent f → ∀ n : ℕ, N ≤ n →
      ‖coeff f n ^ 2 - coeff f (2 * n - 1)‖ ≤ ((n : ℝ) - 1) ^ 2 ∧
      (‖coeff f n ^ 2 - coeff f (2 * n - 1)‖ = ((n : ℝ) - 1) ^ 2 ↔ IsKoebeRotation f) := by
  have hMilin {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ) :
      0 ≤ (milinCoefficients hf).milinSum n := by
    obtain ⟨ρ, hρ, hrep⟩ := hR hf
    cases n with
    | zero => simp [MilinCoefficients.milinSum]
    | succ M =>
      rw [← hrep M, positiveMilinRow]
      exact sum_nonneg (fun i _ => mul_nonneg (connectionCoefficient_nonneg M i) (hρ i))
  obtain ⟨L, hL⟩ := exists_phase_mass_threshold hC
  apply eventually_zalcman_of_milin_nonnegative_and_phase_transfer hMilin
    (C := 2216 * C) (N₀ := max 32 (max L N₀)) (by positivity)
  intro f hf n hn hD
  let D := (n : ℝ) - ‖coeff f n‖
  let M := C * D * Real.log (n : ℝ)
  have hn₀ : 32 ≤ n := by omega
  have hnR : (32 : ℝ) ≤ n := by exact_mod_cast hn₀
  have hD₀ : 0 ≤ D := sub_nonneg.mpr (norm_coeff_le_of_milinSum_nonneg hf (hMilin hf n))
  have hL' := hL n (by omega)
  have hlog₀ : 0 ≤ Real.log (n : ℝ) := zero_le_one.trans hL'.1
  have hM₀ : 0 ≤ M := by dsimp [M]; positivity
  have hMsmall : 64 * M ≤ n := by
    dsimp only [M]
    nlinarith only [hL'.2, mul_nonneg (mul_nonneg hC.le hlog₀) (sub_nonneg.mpr hD)]
  obtain ⟨lam, hlam, α, hα, hb, hm, hPhase⟩ := hEst hf n (by omega) hD
  let g := rotate lam f
  let hg := rotate_normalizedUnivalent hf hlam
  let ω : ℂ := coeff g n / (‖coeff g n‖ : ℂ)
  have hnorm : ‖coeff g n‖ = ‖coeff f n‖ := by
    rw [show g = rotate lam f from rfl, coeff_rotate f hlam (show 1 ≤ n by omega),
      norm_mul, norm_pow, hlam, one_pow, one_mul]
  have hA : 0 < ‖coeff g n‖ := by rw [hnorm]; linarith only [hnR, hD]
  have hω : ‖ω‖ = 1 := by
    dsimp only [ω]
    rw [norm_div, Complex.norm_of_nonneg hA.le, div_self hA.ne']
  obtain ⟨ρ, hρ, hrep⟩ := hR hg
  have hTransfer := (milinCoefficients hg).phase_transfer_of_prefix_mass hα hω hρ hrep
    hn₀ hL'.1 hM₀ hMsmall hb hm hPhase
  simp only [milinCoefficients_squareCoeff hg] at hTransfer
  dsimp only [ω, g] at hTransfer
  rw [phaseAligned_coeff_rotate f hlam (show 1 ≤ n by omega)] at hTransfer
  exact hTransfer.trans_eq (by dsimp only [M, D]; ring)

end Zalcman
