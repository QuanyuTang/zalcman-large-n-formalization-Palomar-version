/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.EvenRadialTransfer
public import Zalcman.LogarithmicRadialMilin
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Propagation of the initial deficit mass

The full and odd phase deficits propagate to the larger radius. Absorption
uses only the initial parity class and the signed-radius Milin estimate.
-/

public section

namespace Zalcman

open Filter Finset Set

private theorem exists_log_le_sqrt_threshold {L : ℝ} (hL : 0 < L) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 ≤ Real.log (n : ℝ) ∧
      L * Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have hLog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hSmall := (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).def
    (show 0 < 1 / L by positivity)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hLog.and hSmall)
  obtain ⟨N, hN⟩ := exists_nat_ge x₀
  refine ⟨max 2 N, le_max_left _ _, fun n hn ↦ ?_⟩
  have hNn : N ≤ n := (le_max_right _ _).trans hn
  obtain ⟨hlog, h⟩ := hx₀ (n : ℝ) (hN.trans (by exact_mod_cast hNn))
  rw [← Real.sqrt_eq_rpow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (zero_le_one.trans hlog), div_mul_eq_mul_div, one_mul] at h
  exact ⟨hlog, by simpa only [mul_comm L] using (le_div_iff₀ hL).mp h⟩

/-- The estimates for the initial deficit sums imply an odd deficit bound
through degree `4*n`, uniformly in the function, phase and deficit. -/
theorem exists_odd_radial_mass_bound
    {K B r₀ P H Q : ℝ} (hK : 0 < K) (hB : 0 ≤ B) (hr₀ : r₀ < 1)
    (hP : 0 ≤ P) (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (hProp : ∀ {f : ℂ → ℂ}, NormalizedUnivalent f → ∀ {γ : ℂ}, ‖γ‖ = 1 →
      ∀ {r s : ℝ}, r₀ ≤ r → 0 < r → r ≤ s → s < 1 →
        radialPhaseDeficit f γ s ≤ K * ((1 - r) / (1 - s)) ^ B * radialPhaseDeficit f γ r ∧
        oddRadialPhaseDeficit f γ s ≤ K * ((1 - r) / (1 - s)) ^ B * oddRadialPhaseDeficit f γ r) :
    ∃ C > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
      (hm : ∀ j, 0 ≤ (milinCoefficients hf).milinSum j) {γ : ℂ} (hγ : ‖γ‖ = 1)
      {D : ℝ}, 0 ≤ D → D ≤ 3 →
      let d := radialCoefficientDeficit f γ
      let o := oddCoefficientDeficits d
      let e := evenCoefficientDeficits d
      (Odd n → (∑ j ∈ range n, o j) ≤ P * (n : ℝ) * D * Real.log (n : ℝ)) →
      (Even n → (∑ j ∈ range n, e j) ≤ P * (n : ℝ) * D * Real.log (n : ℝ)) →
      (∑ j ∈ range n, d j) ≤ H * (n : ℝ) ^ 2 * Real.sqrt (D / n) →
      ‖1 - γ‖ ^ 2 ≤ Q * D * Real.log (n : ℝ) ^ 2 / Real.sqrt (n : ℝ) →
      (∑ j ∈ range (4 * n), o j) ≤ C * (n : ℝ) * D * Real.log (n : ℝ) := by
  obtain ⟨R, hR, hSmall⟩ := exists_radialDeficitSeries_tail_ratio K B
  have hR₁ : 1 ≤ R := by linarith
  let A := K * R ^ B
  have hA : 0 < A := mul_pos hK (Real.rpow_pos_of_pos (by linarith) _)
  have hTail : 2 * A * R ^ 2 * Real.exp (-(R - 1)) ≤ 1 / 4 := by
    rw [Real.rpow_add (by linarith : 0 < R), Real.rpow_two] at hSmall
    dsimp only [A]
    linarith only [hSmall]
  have hTailFull : A * R ^ 2 * Real.exp (-(R - 1)) ≤ 1 / 4 := by
    nlinarith only [hTail, mul_nonneg (mul_nonneg hA.le (sq_nonneg R)) (Real.exp_nonneg (-(R - 1)))]
  let L₀ := 2 * A * R ^ 2 * H * Real.sqrt 3
  let L := 1 + 16 * L₀ + 256 * A * R ^ 2
  have hL₀ : 0 ≤ L₀ := by dsimp only [L₀]; positivity
  have hL : 0 < L := by dsimp only [L]; positivity
  obtain ⟨N₀, hN₀, hLog⟩ := exists_log_le_sqrt_threshold hL
  obtain ⟨N₁, _, hRadius⟩ := exists_radialDeficitSeries_radius_threshold (R := R) hr₀
  let C := Real.exp 6 * (1 + 4 * A * R ^ 2 * P + 2 * A * R ^ 2 * Q)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, max N₀ N₁, ?_⟩
  intro n hn f hf hm γ hγ D hD hDmax d o e hOdd hEven hTotal hPhase
  have hn₂ : 2 ≤ n := hN₀.trans ((le_max_left _ _).trans hn)
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn₀ : 0 < (n : ℝ) := zero_lt_one.trans_le hn₁
  let x := 1 / (n : ℝ)
  let r := Real.exp (-(R * x))
  let s := Real.exp (-x)
  let U := Real.log (n : ℝ)
  let J := Real.sqrt (n : ℝ)
  have hJ : 0 < J := Real.sqrt_pos_of_pos hn₀
  have hJJ : J ^ 2 = (n : ℝ) := Real.sq_sqrt hn₀.le
  have hJn : J ≤ (n : ℝ) := by
    dsimp only [J]
    simpa only [← Real.sqrt_eq_rpow, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn₁ (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hJn₂ : J ≤ (n : ℝ) ^ 2 := hJn.trans (by nlinarith only [mul_nonneg hn₀.le (sub_nonneg.mpr hn₁)])
  obtain ⟨hU, hLJ⟩ := hLog n ((le_max_left _ _).trans hn)
  change 1 ≤ U at hU
  change L * U ≤ J at hLJ
  have hU₀ : 0 ≤ U := zero_le_one.trans hU
  have hx : 0 < x := div_pos one_pos hn₀
  have hxR : 0 < R * x := mul_pos (zero_lt_one.trans_le hR₁) hx
  have hr : 0 < r := Real.exp_pos _
  have hs : 0 < s := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hxR)
  have hs1 : s < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
  have hrs : r ≤ s := Real.exp_le_exp.mpr (neg_le_neg (le_mul_of_one_le_left hx.le hR₁))
  have hr₀' : r₀ ≤ r := by
    simpa only [r, x, mul_one_div] using hRadius n ((le_max_right _ _).trans hn)
  have hγcoef (j : ℕ) : ‖coeff f j‖ ≤ j := norm_coeff_le_of_milinSum_nonneg hf (hm j)
  have hd (j : ℕ) := radialCoefficientDeficit_bounds hγ hγcoef j
  have ho (j : ℕ) : 0 ≤ o j ∧ o j ≤ d j := by
    by_cases hj : Even j
    · simpa only [o, oddCoefficientDeficits, ite_eq_left hj, le_rfl, and_true] using (hd j).1
    · simp only [o, oddCoefficientDeficits, ite_eq_right hj, le_rfl, true_and]
      exact (hd j).1
  have hod (j : ℕ) : o j ≤ 2 * ((j : ℝ) + 1) := (ho j).2.trans (hd j).2
  have hprop := hProp hf hγ hr₀' hr hrs hs1
  have hScale : K * ((1 - r) / (1 - s)) ^ B ≤ A := by
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (exp_radial_gap_ratio_le hR₁ hx) hB) hK.le
  have hdR : radialDeficitSeries d r = radialPhaseDeficit f γ r :=
    radialDeficitSeries_eq_radialPhaseDeficit hf γ (by rwa [abs_of_pos hr]) hr.ne'
  have hdS : radialDeficitSeries d s = radialPhaseDeficit f γ s :=
    radialDeficitSeries_eq_radialPhaseDeficit hf γ (by rwa [abs_of_pos hs]) hs.ne'
  have hdNeg : radialDeficitSeries d (-r) = radialPhaseDeficit f γ (-r) :=
    radialDeficitSeries_eq_radialPhaseDeficit hf γ (by rwa [abs_neg, abs_of_pos hr]) (neg_ne_zero.mpr hr.ne')
  have hPropFull : radialDeficitSeries d s ≤ A * radialDeficitSeries d r := by
    rw [← hdR, ← hdS] at hprop
    exact hprop.1.trans (mul_le_mul_of_nonneg_right hScale
      (radialDeficitSeries_nonneg (fun j ↦ (hd j).1) hr.le))
  have hPropOdd : radialDeficitSeries o s ≤ 2 * A * radialDeficitSeries o r := by
    have h := hprop.2
    rw [oddRadialPhaseDeficit_eq_series hf γ hs hs1, oddRadialPhaseDeficit_eq_series hf γ hr hr1] at h
    have hpS := (oddRadialPhaseDeficit_prefactor_bounds hs hs1).1
    have hpR := (oddRadialPhaseDeficit_prefactor_bounds hr hr1).2
    have hOr := radialDeficitSeries_nonneg (fun j ↦ (ho j).1) hr.le
    have hOs := radialDeficitSeries_nonneg (fun j ↦ (ho j).1) hs.le
    change _ * radialDeficitSeries o s ≤ _ * (_ * radialDeficitSeries o r) at h
    calc
      _ ≤ _ * radialDeficitSeries o s := le_mul_of_one_le_left hOs hpS
      _ ≤ _ := h
      _ ≤ A * (2 * radialDeficitSeries o r) :=
        mul_le_mul hScale (mul_le_mul_of_nonneg_right hpR hOr)
          (mul_nonneg (zero_le_one.trans (oddRadialPhaseDeficit_prefactor_bounds hr hr1).1) hOr) hA.le
      _ = _ := by ring
  have hEx : -((R - 1) * x) * (n : ℝ) = -(R - 1) := by
    dsimp only [x]
    field_simp [hn₀.ne']
  have hWeight : (R * x) ^ 2 = R ^ 2 / (n : ℝ) ^ 2 := by
    simp only [x, mul_one_div, div_pow]
  have hPrelim : radialDeficitSeries d s ≤ L₀ / J := by
    have h := radialDeficitSeries_exp_absorb (fun j ↦ (hd j).1) (fun j ↦ (hd j).2)
      n hR₁ hx hA.le hPropFull (by simpa only [hEx] using hTailFull)
    have hSqrt : Real.sqrt (D / n) ≤ Real.sqrt 3 / J := by
      rw [Real.sqrt_div hD]
      exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hDmax) hJ.le
    calc
      _ ≤ 2 * A * (R * x) ^ 2 * (H * (n : ℝ) ^ 2 * Real.sqrt (D / n)) :=
        h.trans (mul_le_mul_of_nonneg_left hTotal (by positivity))
      _ ≤ 2 * A * (R * x) ^ 2 * (H * (n : ℝ) ^ 2 * (Real.sqrt 3 / J)) := by gcongr
      _ = _ := by
        rw [hWeight]
        dsimp only [L₀]
        field_simp [hn₀.ne']
        <;> ring
  have hFullSmall : radialPhaseDeficit f γ s ≤ 1 / 2 := by
    have hL₀J : 16 * L₀ ≤ J := by
      dsimp only [L] at hLJ
      nlinarith only [hLJ, hU, hL₀, mul_nonneg hU₀ (mul_nonneg hA.le (sq_nonneg R)),
        mul_nonneg hL₀ (sub_nonneg.mpr hU)]
    rw [← hdS]
    exact hPrelim.trans ((div_le_iff₀ hJ).mpr (by linarith only [hL₀J, hL₀]))
  have hFullLogSmall : 4 * radialPhaseDeficit f γ s * U ≤ 1 / 4 := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPrelim (by norm_num : (0 : ℝ) ≤ 4)) hU₀
    rw [← hdS]
    apply h.trans
    rw [show 4 * (L₀ / J) * U = (4 * L₀ * U) / J by ring, div_le_iff₀ hJ]
    dsimp only [L] at hLJ
    nlinarith only [hLJ, hU₀, mul_nonneg hU₀ (mul_nonneg hA.le (sq_nonneg R))]
  have hNeg := negative_radialPhaseDeficit_at_exp_le hf hγ hm hn₂ hR₁
    (by simpa only [s, x] using hFullSmall) (by simpa only [s, x, U] using hFullLogSmall)
  have hNeg' : radialDeficitSeries d (-r) ≤ 64 * U * radialDeficitSeries d s +
      Q * D * U ^ 2 / J := by
    rw [hdNeg, hdS]
    have he : radialPhaseDeficit f γ (-r) ≤ ‖1 - γ‖ ^ 2 +
        64 * radialPhaseDeficit f γ s * U := by
      simpa only [r, s, x, U, mul_one_div] using hNeg
    change ‖1 - γ‖ ^ 2 ≤ Q * D * U ^ 2 / J at hPhase
    linarith only [he, hPhase]
  have hSmallEven : A * (R * x) ^ 2 * (64 * U) ≤ 1 / 4 := by
    rw [hWeight, show A * (R ^ 2 / (n : ℝ) ^ 2) * (64 * U) =
      (64 * A * R ^ 2 * U) / (n : ℝ) ^ 2 by ring, div_le_iff₀ (sq_pos_of_pos hn₀)]
    dsimp only [L] at hLJ
    nlinarith only [hLJ.trans hJn₂, hU₀, mul_nonneg hL₀ hU₀]
  have hRadial : radialDeficitSeries o s ≤ (4 * A * R ^ 2 * P + 2 * A * R ^ 2 * Q) * D * U / n := by
    rcases Nat.even_or_odd n with hnEven | hnOdd
    · have h := radialDeficitSeries_even_exp_absorb (fun j ↦ (hd j).1) (fun j ↦ (hd j).2) n
        hR₁ hx hA.le (by positivity : 0 ≤ 64 * U) (by positivity : 0 ≤ Q * D * U ^ 2 / J)
        hPropFull hNeg' (by simpa only [hEx] using hTail) hSmallEven
      have hLogSize : U ≤ (n : ℝ) * J := calc
        _ ≤ L * U := le_mul_of_one_le_left hU₀ (by
          dsimp only [L]
          nlinarith only [hL₀, mul_nonneg hA.le (sq_nonneg R)])
        _ ≤ J := hLJ
        _ ≤ _ := le_mul_of_one_le_left hJ.le hn₁
      have hRatio : U / ((n : ℝ) * J) ≤ 1 := (div_le_one (mul_pos hn₀ hJ)).mpr hLogSize
      have hEq : 4 * A * (R * x) ^ 2 * (P * (n : ℝ) * D * U) +
          2 * A * (R * x) ^ 2 * (Q * D * U ^ 2 / J) =
          4 * A * R ^ 2 * P * D * U / n +
            (2 * A * R ^ 2 * Q * D * U / n) * (U / ((n : ℝ) * J)) := by
        rw [hWeight]
        field_simp [hn₀.ne', hJ.ne']
        <;> ring
      calc
        _ ≤ radialDeficitSeries d s := radialDeficitSeries_mono_of_linear_bound
          (fun j ↦ (ho j).1) (fun j ↦ (hd j).1) (fun j ↦ (hd j).2) (fun j ↦ (ho j).2) hs.le hs1
        _ ≤ _ := h.trans (add_le_add (mul_le_mul_of_nonneg_left
          (hEven hnEven) (by positivity)) (le_refl _))
        _ = _ := hEq
        _ ≤ 4 * A * R ^ 2 * P * D * U / n + (2 * A * R ^ 2 * Q * D * U / n) * 1 :=
          add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hRatio (by positivity))
        _ = _ := by ring
    · have h := radialDeficitSeries_exp_absorb (fun j ↦ (ho j).1) hod n hR₁ hx
        (by positivity) hPropOdd (by simpa only [hEx] using hTail)
      calc
        _ ≤ 2 * (2 * A) * (R * x) ^ 2 * (P * (n : ℝ) * D * U) :=
          h.trans (mul_le_mul_of_nonneg_left (hOdd hnOdd) (by positivity))
        _ = 4 * A * R ^ 2 * P * D * U / n := by rw [hWeight]; field_simp [hn₀.ne']; ring
        _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ hn₀.le
          have hf : 0 ≤ 2 * A * R ^ 2 * Q * D * U := by positivity
          nlinarith only [hf]
  have hMass := radialDeficitSeries_mass_le (fun j ↦ (ho j).1) hod (show 0 < n by omega)
  change _ ≤ Real.exp 6 * (n : ℝ) ^ 2 * radialDeficitSeries o s at hMass
  calc
    _ ≤ Real.exp 6 * (n : ℝ) ^ 2 * ((4 * A * R ^ 2 * P + 2 * A * R ^ 2 * Q) * D * U / n) :=
      hMass.trans (mul_le_mul_of_nonneg_left hRadial (by positivity))
    _ ≤ C * (n : ℝ) * D * U := by
      have hCalc : Real.exp 6 * (n : ℝ) ^ 2 *
          ((4 * A * R ^ 2 * P + 2 * A * R ^ 2 * Q) * D * U / n) =
          Real.exp 6 * (4 * A * R ^ 2 * P + 2 * A * R ^ 2 * Q) * (n : ℝ) * D * U := by
        field_simp [hn₀.ne']
        <;> ring
      rw [hCalc]
      dsimp only [C]
      nlinarith only [show 0 ≤ Real.exp 6 * (n : ℝ) * D * U by positivity]

end Zalcman
