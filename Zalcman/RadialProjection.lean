/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Basic
public import Zalcman.RadialTransfer
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact projections of radial coefficient deficits

Index `j` is the manuscript's coefficient of order `j + 1`.
-/

@[expose] public section

noncomputable section

namespace Zalcman

open scoped ComplexConjugate

/-- Keep coefficients of even order. -/
def evenCoefficientDeficits (d : ℕ → ℝ) (j : ℕ) : ℝ :=
  if Even j then 0 else d j

/-- Keep coefficients of odd order. -/
def oddCoefficientDeficits (d : ℕ → ℝ) (j : ℕ) : ℝ :=
  if Even j then d j else 0

/-- A nonnegative sequence with the coefficient deficit growth bound gives an
absolutely convergent radial series at every signed radius in the disk. -/
theorem summable_radialDeficit_of_le {d : ℕ → ℝ} (hd : ∀ j, 0 ≤ d j)
    (hb : ∀ j : ℕ, d j ≤ 2 * ((j : ℝ) + 1)) {r : ℝ} (hr : |r| < 1) :
    Summable (fun j ↦ ‖d j * r ^ j‖) := by
  have habs : ‖|r|‖ < 1 := (Real.norm_of_nonneg (abs_nonneg _)).trans_lt hr
  have hgeom := (hasSum_choose_mul_geometric_of_norm_lt_one 1 habs).summable.mul_left 2
  apply Summable.of_nonneg_of_le (fun j ↦ norm_nonneg _) _ hgeom
  intro j
  change ‖d j * r ^ j‖ ≤ 2 * (((j + 1).choose 1 : ℕ) * |r| ^ j)
  rw [norm_mul, Real.norm_of_nonneg (hd j), norm_pow, Real.norm_eq_abs,
    Nat.choose_one_right, Nat.cast_add, Nat.cast_one, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hb j) (pow_nonneg (abs_nonneg _) _)

/-- Positive and negative radii recover the even and odd parts, respectively by
subtraction and addition after restoring the radial weights. -/
theorem radialDeficitSeries_projections (d : ℕ → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hplus : Summable fun j ↦ d j * r ^ j)
    (hminus : Summable fun j ↦ d j * (-r) ^ j) :
    radialDeficitSeries d r =
        2 * radialDeficitSeries (evenCoefficientDeficits d) r +
          ((1 - r) / (1 + r)) ^ 2 * radialDeficitSeries d (-r) ∧
      2 * radialDeficitSeries (oddCoefficientDeficits d) r =
        radialDeficitSeries d r + ((1 - r) / (1 + r)) ^ 2 * radialDeficitSeries d (-r) := by
  have heven (j : ℕ) : evenCoefficientDeficits d j * r ^ j =
      (d j * r ^ j - d j * (-r) ^ j) / 2 := by
    by_cases hj : Even j
    · simp [evenCoefficientDeficits, hj, hj.neg_pow]
    · rw [evenCoefficientDeficits, ite_eq_right hj, (Nat.not_even_iff_odd.mp hj).neg_pow]
      ring
  have hodd (j : ℕ) : oddCoefficientDeficits d j * r ^ j =
      (d j * r ^ j + d j * (-r) ^ j) / 2 := by
    by_cases hj : Even j
    · rw [oddCoefficientDeficits, ite_eq_left hj, hj.neg_pow]
      ring
    · simp [oddCoefficientDeficits, hj, (Nat.not_even_iff_odd.mp hj).neg_pow]
  have hve : (∑' j, evenCoefficientDeficits d j * r ^ j) =
      ((∑' j, d j * r ^ j) - ∑' j, d j * (-r) ^ j) / 2 := by
    rw [tsum_congr heven, tsum_div_const, hplus.tsum_sub hminus]
  have hvo : (∑' j, oddCoefficientDeficits d j * r ^ j) =
      ((∑' j, d j * r ^ j) + ∑' j, d j * (-r) ^ j) / 2 := by
    rw [tsum_congr hodd, tsum_div_const, hplus.tsum_add hminus]
  have hscale : ((1 - r) / (1 + r)) ^ 2 * (1 - -r) ^ 2 = (1 - r) ^ 2 := by
    rw [sub_neg_eq_add, div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 (by positivity))]
  constructor <;> simp only [radialDeficitSeries, hve, hvo, ← mul_assoc, hscale] <;> ring

/-- The coefficient deficit used in the radial series. -/
def radialCoefficientDeficit (f : ℂ → ℂ) (γ : ℂ) (j : ℕ) : ℝ :=
  (j : ℝ) + 1 - (conj γ * coeff f (j + 1)).re

/-- The radial coefficient deficit is nonnegative and grows at most linearly
under the Bieberbach coefficient bound. -/
theorem radialCoefficientDeficit_bounds {f : ℂ → ℂ} {γ : ℂ} (hγ : ‖γ‖ = 1)
    (hcoeff : ∀ n : ℕ, ‖coeff f n‖ ≤ n) (j : ℕ) :
    0 ≤ radialCoefficientDeficit f γ j ∧ radialCoefficientDeficit f γ j ≤ 2 * ((j : ℝ) + 1) := by
  have hbound : ‖conj γ * coeff f (j + 1)‖ ≤ (j : ℝ) + 1 := by
    rw [norm_mul, Complex.norm_conj, hγ, one_mul]
    simpa only [Nat.cast_add, Nat.cast_one] using hcoeff (j + 1)
  have hre := abs_le.mp ((Complex.abs_re_le_norm (conj γ * coeff f (j + 1))).trans hbound)
  unfold radialCoefficientDeficit
  exact ⟨by linarith only [hre.2], by linarith only [hre.1]⟩

/-- The phase-corrected deficit relative to Koebe at a signed real radius. -/
def radialPhaseDeficit (f : ℂ → ℂ) (γ : ℂ) (r : ℝ) : ℝ :=
  1 - (conj γ * (f (r : ℂ) / koebe (r : ℂ))).re

/-- The phase-corrected deficit of the odd part at a positive real radius. -/
def oddRadialPhaseDeficit (f : ℂ → ℂ) (γ : ℂ) (r : ℝ) : ℝ :=
  1 - (conj γ * ((f (r : ℂ) - f (-(r : ℂ))) / (koebe (r : ℂ) - koebe (-(r : ℂ))))).re

/-- The real Koebe function on the real diameter. -/
def realKoebe (r : ℝ) : ℝ := r / (1 - r) ^ 2

private lemma coe_realKoebe (r : ℝ) : (realKoebe r : ℂ) = koebe (r : ℂ) := by
  simp only [realKoebe, koebe, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_one]

private lemma hasSum_coeff_succ {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {z : ℂ} (hz : z ∈ unitDisk) (hz0 : z ≠ 0) :
    HasSum (fun j : ℕ ↦ coeff f (j + 1) * z ^ j) (f z / z) := by
  have htaylor : HasSum (fun j : ℕ ↦ coeff f j * z ^ j) (f z) := by
    convert Complex.hasSum_taylorSeries_on_ball hf.holomorphic hz using 1
    funext j
    simp only [coeff, sub_zero, smul_eq_mul]
    ring
  have htail : HasSum (fun j : ℕ ↦ coeff f (j + 1) * z ^ (j + 1)) (f z) := by
    simpa [hf.map_zero] using (hasSum_nat_add_iff' 1).mpr htaylor
  convert htail.div_const z using 1
  funext j
  rw [pow_succ, ← mul_assoc, mul_div_cancel_right₀ _ hz0]

private lemma hasSum_radialCoefficientDeficit {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    (γ : ℂ) {r : ℝ} (hr : |r| < 1) (hr0 : r ≠ 0) :
    HasSum (fun j ↦ radialCoefficientDeficit f γ j * r ^ j)
      (1 / (1 - (r : ℂ)) ^ 2 - conj γ * (f (r : ℂ) / (r : ℂ))).re := by
  have hr_complex : ‖(r : ℂ)‖ < 1 := by simpa [Complex.norm_real, Real.norm_eq_abs] using hr
  have hcoef := hasSum_coeff_succ hf (mem_unitDisk.mpr hr_complex)
    (Complex.ofReal_ne_zero.mpr hr0)
  have hgeom := hasSum_choose_mul_geometric_of_norm_lt_one 1 hr_complex
  have h := Complex.reCLM.hasSum (hgeom.sub (hcoef.mul_left (conj γ)))
  convert h using 1
  · funext j
    simp only [radialCoefficientDeficit, Complex.reCLM_apply, Complex.sub_re,
      Nat.choose_one_right, Nat.cast_add, Nat.cast_one, ← Complex.ofReal_pow, Complex.add_re,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
      Complex.one_re, mul_zero, zero_add, sub_zero]
    ring
  · simp only [Complex.reCLM_apply]

/-- The full deficit series equals the phase-corrected deficit on both halves of the diameter. -/
theorem radialDeficitSeries_eq_radialPhaseDeficit {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    (γ : ℂ) {r : ℝ} (hr : |r| < 1) (hr0 : r ≠ 0) :
    radialDeficitSeries (radialCoefficientDeficit f γ) r = radialPhaseDeficit f γ r := by
  have hden_real : 1 - r ≠ 0 := sub_ne_zero.mpr ((lt_of_le_of_lt (le_abs_self _) hr).ne')
  have hden : 1 - (r : ℂ) ≠ 0 := by exact_mod_cast hden_real
  have hr0_complex : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0
  have hscale :
      Complex.ofReal ((1 - r) ^ 2) * (1 / (1 - (r : ℂ)) ^ 2 - conj γ * (f (r : ℂ) / (r : ℂ))) =
        1 - conj γ * (f (r : ℂ) / koebe (r : ℂ)) := by
    unfold koebe
    rw [Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one]
    field_simp [hden, hr0_complex]
    <;> ring
  unfold radialDeficitSeries radialPhaseDeficit
  rw [(hasSum_radialCoefficientDeficit hf γ hr hr0).tsum_eq]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.sub_re, Complex.one_re] using congrArg Complex.re hscale

/-- On the positive diameter, the analytic real-part deficit is nonnegative
under the Bieberbach coefficient bound. -/
theorem radialPhaseDeficit_nonneg {f : ℂ → ℂ} (hf : NormalizedUnivalent f) {γ : ℂ}
    (hγ : ‖γ‖ = 1) (hcoeff : ∀ n : ℕ, ‖coeff f n‖ ≤ n)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 ≤ radialPhaseDeficit f γ r := by
  have hrabs : |r| < 1 := by rwa [abs_of_pos hr]
  rw [← radialDeficitSeries_eq_radialPhaseDeficit hf γ hrabs hr.ne']
  exact radialDeficitSeries_nonneg (fun j ↦ (radialCoefficientDeficit_bounds hγ hcoeff j).1) hr.le

private lemma mul_deficit {k : ℝ} (hk : k ≠ 0) (γ z : ℂ) :
    k * (1 - (conj γ * (z / (k : ℂ))).re) = k - (conj γ * z).re := by
  have hmul : (k : ℂ) * (conj γ * (z / (k : ℂ))) = conj γ * z := by
    field_simp [Complex.ofReal_ne_zero.mpr hk]
  rw [mul_sub, mul_one]
  have hre : k * (conj γ * (z / (k : ℂ))).re = (conj γ * z).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      congrArg Complex.re hmul
  rw [hre]

private lemma realKoebe_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 < realKoebe r :=
  div_pos hr (sq_pos_of_pos (sub_pos.mpr hr1))

private lemma realKoebe_neg {r : ℝ} (hr : 0 < r) : realKoebe (-r) < 0 :=
  div_neg_of_neg_of_pos (neg_neg_of_pos hr) (sq_pos_of_pos (by linarith))

private lemma realKoebe_mul_radial_weight {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    realKoebe r * ((1 - r) / (1 + r)) ^ 2 = -realKoebe (-r) := by
  have hden₁ : 1 - r ≠ 0 := (sub_pos.mpr hr1).ne'
  have hden₂ : 1 + r ≠ 0 := by positivity
  unfold realKoebe
  rw [sub_neg_eq_add]
  field_simp [hden₁, hden₂]

/-- The odd deficit series is the odd analytic deficit with its exact prefactor. -/
theorem oddRadialPhaseDeficit_eq_series {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    (γ : ℂ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    oddRadialPhaseDeficit f γ r =
      (2 * realKoebe r / (realKoebe r - realKoebe (-r))) *
        radialDeficitSeries (oddCoefficientDeficits (radialCoefficientDeficit f γ)) r := by
  have hrabs : |r| < 1 := by rwa [abs_of_pos hr]
  have habsneg : |-r| < 1 := (abs_neg r).trans_lt hrabs
  have hrneg : -r ≠ 0 := neg_ne_zero.mpr hr.ne'
  have hk := realKoebe_pos hr hr1
  have hkn := realKoebe_neg hr
  have hden : realKoebe r - realKoebe (-r) ≠ 0 := (sub_pos.mpr (hkn.trans hk)).ne'
  have hproj := (radialDeficitSeries_projections (radialCoefficientDeficit f γ) hr.le
    (hasSum_radialCoefficientDeficit hf γ hrabs hr.ne').summable
    (hasSum_radialCoefficientDeficit hf γ habsneg hrneg).summable).2
  rw [radialDeficitSeries_eq_radialPhaseDeficit hf γ hrabs hr.ne',
    radialDeficitSeries_eq_radialPhaseDeficit hf γ habsneg hrneg] at hproj
  have hodd :
      (realKoebe r - realKoebe (-r)) * oddRadialPhaseDeficit f γ r =
        realKoebe r * radialPhaseDeficit f γ r - realKoebe (-r) * radialPhaseDeficit f γ (-r) := by
    unfold oddRadialPhaseDeficit radialPhaseDeficit
    simp only [← coe_realKoebe, ← Complex.ofReal_neg, ← Complex.ofReal_sub]
    rw [mul_deficit hden, mul_deficit hk.ne', mul_deficit hkn.ne]
    simp only [mul_sub, Complex.sub_re]
    ring
  have hweight := realKoebe_mul_radial_weight hr hr1
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hden).mpr
  calc
    _ = (realKoebe r - realKoebe (-r)) * oddRadialPhaseDeficit f γ r := mul_comm _ _
    _ = realKoebe r * radialPhaseDeficit f γ r -
        realKoebe (-r) * radialPhaseDeficit f γ (-r) := hodd
    _ = realKoebe r *
        (radialPhaseDeficit f γ r + ((1 - r) / (1 + r)) ^ 2 * radialPhaseDeficit f γ (-r)) := by
      rw [mul_add, ← mul_assoc (realKoebe r), hweight]
      ring
    _ = _ := by rw [← hproj]; ring

/-- The odd projection prefactor is between one and two. -/
theorem oddRadialPhaseDeficit_prefactor_bounds {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    1 ≤ 2 * realKoebe r / (realKoebe r - realKoebe (-r)) ∧
      2 * realKoebe r / (realKoebe r - realKoebe (-r)) ≤ 2 := by
  have hk := realKoebe_pos hr hr1
  have hkn := realKoebe_neg hr
  have hden : 0 < realKoebe r - realKoebe (-r) := sub_pos.mpr (hkn.trans hk)
  have hweight : ((1 - r) / (1 + r)) ^ 2 ≤ 1 := by
    have hratio : (1 - r) / (1 + r) ≤ 1 := by
      apply (div_le_one₀ (by positivity : 0 < 1 + r)).mpr
      linarith
    simpa using pow_le_pow_left₀ (by positivity : 0 ≤ (1 - r) / (1 + r)) hratio 2
  have hneg_le : -realKoebe (-r) ≤ realKoebe r := by
    rw [← realKoebe_mul_radial_weight hr hr1]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hweight hk.le
  constructor
  · rw [le_div_iff₀ hden]
    linarith only [hneg_le]
  · rw [div_le_iff₀ hden]
    linarith only [hkn]

end Zalcman
