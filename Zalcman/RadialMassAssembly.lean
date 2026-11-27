/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.RadialMass
public import Zalcman.PrefixMass
public import Zalcman.ProofAssembly
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Passing the radial mass estimate to the target phase

The radial series starts at Taylor degree one. The matching-parity prefix and
the final odd mass are therefore reindexed by one before the final assembly.
-/

public section

namespace Zalcman

open Filter Finset
open scoped ComplexConjugate

private lemma radialCoefficientDeficit_eq_phaseDeficit {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    (α : ℂ) (j : ℕ) :
    radialCoefficientDeficit f (α ^ 2) j = (milinCoefficients hf).phaseDeficit α (j + 1) := by
  rw [radialCoefficientDeficit, MilinCoefficients.phaseDeficit, milinCoefficients_squareCoeff hf,
    Nat.cast_add, Nat.cast_one]

private lemma sum_odd_phaseDeficit_eq_radial {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    (α : ℂ) (m : ℕ) :
    (∑ j ∈ (range (m + 1)).filter Odd, (milinCoefficients hf).phaseDeficit α j) =
      ∑ j ∈ range m, oddCoefficientDeficits (radialCoefficientDeficit f (α ^ 2)) j := by
  rw [Finset.sum_filter, Finset.sum_range_succ']
  simp only [Nat.not_odd_zero, ite_false, add_zero, oddCoefficientDeficits,
    Nat.odd_add_one, Nat.not_odd_iff_even, radialCoefficientDeficit_eq_phaseDeficit hf]

private lemma norm_one_sub_pow_two_sq_le {α : ℂ} (hα : ‖α‖ = 1) :
    ‖1 - α ^ 2‖ ^ 2 ≤ 4 * ‖1 - α‖ ^ 2 := by
  have hplus : ‖1 + α‖ ≤ 2 := by simpa only [norm_one, hα, one_add_one_eq_two] using norm_add_le 1 α
  have hfactor : (1 : ℂ) - α ^ 2 = (1 - α) * (1 + α) := by ring
  have hb : ‖1 - α ^ 2‖ ≤ 2 * ‖1 - α‖ := by
    rw [hfactor, norm_mul, mul_comm 2]
    exact mul_le_mul_of_nonneg_left hplus (norm_nonneg _)
  have h := pow_le_pow_left₀ (norm_nonneg _) hb 2
  nlinarith only [h]

private lemma natCast_modEq_two (j k : ℕ) :
    ((j : ℤ) ≡ (k : ℤ) [ZMOD 2]) ↔ j ≡ k [MOD 2] := by
  simpa only [Nat.cast_ofNat] using! (Int.natCast_modEq_iff (a := j) (b := k) (n := 2))

private lemma modEq_two_even {j k : ℕ} (hk : Even k) :
    ((j : ℤ) ≡ (k : ℤ) [ZMOD 2]) ↔ Even j := by
  rw [natCast_modEq_two, Nat.ModEq, Nat.even_iff.mp hk, ← Nat.even_iff]

private lemma modEq_two_odd {j k : ℕ} (hk : Odd k) :
    ((j : ℤ) ≡ (k : ℤ) [ZMOD 2]) ↔ ¬Even j := by
  rw [natCast_modEq_two, Nat.ModEq, Nat.odd_iff.mp hk, ← Nat.odd_iff, Nat.not_even_iff_odd]

set_option maxHeartbeats 1250000 in
/-- The positive representation, rotated prefix estimates and two-radius
propagation imply the eventual Zalcman inequality and rigidity. -/
theorem eventually_zalcman_of_representation_prefix_and_propagation
    (hR : ∀ {f : ℂ → ℂ} (hf : NormalizedUnivalent f),
      ∃ ρ : ℕ → ℝ, (∀ l, 0 ≤ ρ l) ∧
        ∀ M, positiveMilinRow ρ M = (milinCoefficients hf).milinSum (M + 1))
    {K B r₀ A P : ℝ} {N₀ : ℕ}
    (hK : 0 < K) (hB : 0 ≤ B) (hr₀ : r₀ < 1) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (hProp : ∀ {f : ℂ → ℂ}, NormalizedUnivalent f → ∀ {γ : ℂ}, ‖γ‖ = 1 →
      ∀ {r s : ℝ}, r₀ ≤ r → 0 < r → r ≤ s → s < 1 →
        radialPhaseDeficit f γ s ≤ K * ((1 - r) / (1 - s)) ^ B * radialPhaseDeficit f γ r ∧
        oddRadialPhaseDeficit f γ s ≤ K * ((1 - r) / (1 - s)) ^ B * oddRadialPhaseDeficit f γ r)
    (hPrefix : ∀ {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ), N₀ ≤ n →
      let D := (n : ℝ) - ‖coeff f n‖
      D ≤ 3 → ∃ (lam : ℂ) (hlam : ‖lam‖ = 1) (α : ℂ), ‖α‖ = 1 ∧
        let g := rotate lam f
        let dg := milinCoefficients (rotate_normalizedUnivalent hf hlam)
        let ω := coeff g n / (‖coeff g n‖ : ℂ)
        dg.blockError α n ≤ A * D ∧
          ‖1 - α‖ ^ 2 + ‖ω - α ^ 2‖ ^ 2 ≤
            P * D * Real.log (n : ℝ) ^ 2 / Real.sqrt (n : ℝ)) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ {f : ℂ → ℂ}, NormalizedUnivalent f → ∀ n : ℕ, N ≤ n →
      ‖coeff f n ^ 2 - coeff f (2 * n - 1)‖ ≤ ((n : ℝ) - 1) ^ 2 ∧
      (‖coeff f n ^ 2 - coeff f (2 * n - 1)‖ = ((n : ℝ) - 1) ^ 2 ↔ IsKoebeRotation f) := by
  obtain ⟨R, hR₀, N₁, hMass⟩ := exists_odd_radial_mass_bound hK hB hr₀
    (show 0 ≤ 6 + 2 * A by positivity) (show 0 ≤ 5 + 4 * A by positivity)
    (show 0 ≤ 4 * P by positivity) hProp
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)))
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge x₀
  let C := 1 + A + P + R
  have hC : 0 < C := by dsimp only [C]; positivity
  apply eventually_zalcman_of_representation_and_rotated_estimates hR
    (C := C) (N₀ := max 6 (max N₀ (max N₁ N₂))) hC
  intro f hf n hn
  let D : ℝ := (n : ℝ) - ‖coeff f n‖
  change D ≤ 3 → _
  intro hDmax
  have hn₆ : 6 ≤ n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  let L := Real.log (n : ℝ)
  have hL : 1 ≤ L := hx₀ (n : ℝ) (hN₂.trans (by exact_mod_cast (show N₂ ≤ n by omega)))
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  obtain ⟨lam, hlam, α, hα, hBlock, hPhase⟩ := hPrefix hf n (by omega) hDmax
  let g := rotate lam f
  let hg := rotate_normalizedUnivalent hf hlam
  let dg := milinCoefficients hg
  let γ := α ^ 2
  let q := radialCoefficientDeficit g γ
  let E := dg.blockError α n
  let ω : ℂ := coeff g n / (‖coeff g n‖ : ℂ)
  have hγ : ‖γ‖ = 1 := by simp [γ, norm_pow, hα]
  have hNorm : ‖coeff g n‖ = ‖coeff f n‖ := by
    rw [show g = rotate lam f from rfl, coeff_rotate f hlam (show 1 ≤ n by omega),
      norm_mul, norm_pow, hlam, one_pow, one_mul]
  have hDg : (n : ℝ) - ‖dg.squareCoeff n‖ = D := by
    rw [show dg.squareCoeff n = coeff g n from milinCoefficients_squareCoeff hg n, hNorm]
  change E ≤ A * D at hBlock
  change ‖1 - α‖ ^ 2 + ‖ω - α ^ 2‖ ^ 2 ≤ P * D * L ^ 2 / Real.sqrt (n : ℝ) at hPhase
  obtain ⟨ρ, hρ, hrep⟩ := hR hg
  have hT (j : ℕ) : 0 ≤ dg.milinSum j := by
    cases j with
    | zero => simp [MilinCoefficients.milinSum]
    | succ m =>
      rw [← hrep m, positiveMilinRow]
      exact sum_nonneg (fun i _ ↦ mul_nonneg (connectionCoefficient_nonneg m i) (hρ i))
  have hD₀ : 0 ≤ D := by
    rw [← hDg]
    exact sub_nonneg.mpr (dg.norm_squareCoeff_le_index (by omega) (hT n))
  have hCoeff (j : ℕ) : q j = dg.phaseDeficit α (j + 1) :=
    radialCoefficientDeficit_eq_phaseDeficit hg α j
  have hnEq : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hSameD : (↑(n - 1 + 1 : ℕ) : ℝ) - ‖dg.squareCoeff (n - 1 + 1)‖ ≤ 3 := by
    rw [hnEq, hDg]
    exact hDmax
  have hs := dg.sum_phaseDeficit_sameParity_le hα hρ hrep (N := n - 1) (by omega) hSameD
  dsimp only at hs
  rw [hnEq, hDg, Finset.sum_filter] at hs
  have hSame :
      (∑ j ∈ range n, if (j : ℤ) ≡ ((n - 1 : ℕ) : ℤ) [ZMOD 2] then dg.phaseDeficit α (j + 1) else 0) ≤
        (6 + 2 * A) * (n : ℝ) * D * L := by
    refine hs.trans ?_
    change (n : ℝ) * ((4 + 2 * L) * D + 2 * E) ≤ _
    have h₁ : 0 ≤ (L - 1) * D := mul_nonneg (sub_nonneg.mpr hL) hD₀
    have h₂ : 0 ≤ A * ((L - 1) * D) := mul_nonneg hA h₁
    have hcalc : (4 + 2 * L) * D + 2 * E ≤ (6 + 2 * A) * D * L := by
      nlinarith only [h₁, h₂, hBlock]
    calc
      _ ≤ (n : ℝ) * ((6 + 2 * A) * D * L) := mul_le_mul_of_nonneg_left hcalc hnR.le
      _ = _ := by ring
  have hOdd (ho : Odd n) : (∑ j ∈ range n, oddCoefficientDeficits q j) ≤
      (6 + 2 * A) * (n : ℝ) * D * L := by
    have hN : Even (n - 1) := by
      rw [Nat.even_iff]
      have h := Nat.odd_iff.mp ho
      omega
    calc
      _ = ∑ j ∈ range n, if (j : ℤ) ≡ ((n - 1 : ℕ) : ℤ) [ZMOD 2]
          then dg.phaseDeficit α (j + 1) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [oddCoefficientDeficits, modEq_two_even hN, hCoeff]
      _ ≤ _ := hSame
  have hEven (he : Even n) : (∑ j ∈ range n, evenCoefficientDeficits q j) ≤
      (6 + 2 * A) * (n : ℝ) * D * L := by
    have hN : Odd (n - 1) := by
      rw [Nat.odd_iff]
      have h := Nat.even_iff.mp he
      omega
    calc
      _ = ∑ j ∈ range n, if (j : ℤ) ≡ ((n - 1 : ℕ) : ℤ) [ZMOD 2]
          then dg.phaseDeficit α (j + 1) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [evenCoefficientDeficits, modEq_two_odd hN, ite_not, hCoeff]
      _ ≤ _ := hSame
  have hTotal : (∑ j ∈ range n, q j) ≤ (5 + 4 * A) * (n : ℝ) ^ 2 * Real.sqrt (D / n) := by
    simp only [hCoeff]
    have ht := dg.sum_phaseDeficit_prefix_le hα hT hn₆ (hDg.symm ▸ hDmax)
    rw [hDg] at ht
    let S := Real.sqrt ((n : ℝ) * D)
    have hS₀ : 0 ≤ S := Real.sqrt_nonneg _
    have hS₂ : S ^ 2 = (n : ℝ) * D := Real.sq_sqrt (mul_nonneg hnR.le hD₀)
    have hDle : D ≤ 2 * S := by
      apply (sq_le_sq₀ hD₀ (by positivity)).mp
      rw [mul_pow, hS₂]
      have hh := mul_nonneg (show 0 ≤ 4 * (n : ℝ) - D by linarith only [hn₁, hDmax]) hD₀
      nlinarith only [hh]
    have hroot : Real.sqrt (24 * (n : ℝ) * D) ≤ 5 * S := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [Real.sq_sqrt (by positivity), mul_pow, hS₂]
      nlinarith only [mul_nonneg hnR.le hD₀]
    have hscale : (n : ℝ) * Real.sqrt (D / n) = S := by
      apply (sq_eq_sq₀ (by positivity) hS₀).mp
      rw [mul_pow, Real.sq_sqrt (div_nonneg hD₀ hnR.le), hS₂]
      field_simp [hnR.ne']
    have hE : E ≤ 2 * A * S :=
      hBlock.trans ((mul_le_mul_of_nonneg_left hDle hA).trans_eq (by ring))
    calc
      _ ≤ (n : ℝ) * (Real.sqrt (24 * (n : ℝ) * D) + 2 * E) := ht
      _ ≤ (n : ℝ) * ((5 + 4 * A) * S) := by
        apply mul_le_mul_of_nonneg_left _ hnR.le
        nlinarith only [hroot, hE]
      _ = _ := by rw [← hscale]; ring
  have hγErr : ‖1 - γ‖ ^ 2 ≤ 4 * P * D * L ^ 2 / Real.sqrt (n : ℝ) := by
    have hαErr := (le_add_of_nonneg_right (sq_nonneg ‖ω - α ^ 2‖)).trans hPhase
    have hb := mul_le_mul_of_nonneg_left hαErr (show 0 ≤ (4 : ℝ) by norm_num)
    exact (norm_one_sub_pow_two_sq_le hα).trans (hb.trans_eq (by ring))
  have hMass' := hMass n (by omega) hg hT hγ hD₀ hDmax hOdd hEven hTotal hγErr
  have hOddMass : (∑ j ∈ (range (4 * n + 1)).filter Odd, dg.phaseDeficit α j) ≤
      R * (n : ℝ) * D * L := by
    rw [sum_odd_phaseDeficit_eq_radial hg]
    exact hMass'
  have hAC : A ≤ C := by dsimp only [C]; linarith only [hP, hR₀]
  have hPC : P ≤ C := by dsimp only [C]; linarith only [hA, hR₀]
  have hRC : R ≤ C := by dsimp only [C]; linarith only [hA, hP]
  refine ⟨lam, hlam, α, hα, ?_, ?_, ?_⟩
  · exact hBlock.trans
      ((mul_le_mul_of_nonneg_right hAC hD₀).trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hL (mul_nonneg hC.le hD₀)))
  · calc
      _ ≤ R * (n : ℝ) * D * L := hOddMass
      _ = R * ((n : ℝ) * D * L) := by ring
      _ ≤ C * ((n : ℝ) * D * L) := mul_le_mul_of_nonneg_right hRC (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ P * D * L ^ 2 / Real.sqrt (n : ℝ) := hPhase
      _ = P * (D * L ^ 2 / Real.sqrt (n : ℝ)) := by ring
      _ ≤ C * (D * L ^ 2 / Real.sqrt (n : ℝ)) := mul_le_mul_of_nonneg_right hPC (by positivity)
      _ = _ := by ring

end Zalcman
