/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.LogarithmicCoefficients
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Logarithmic estimates at the negative radius

Index `k` represents the manuscript's coefficient of order `k + 1`.
-/

@[expose] public section

noncomputable section

namespace Zalcman

open scoped ComplexConjugate

/-- The terms of the normalized logarithmic deviation from Koebe. -/
def logarithmicDeviationTerm (t : ℕ → ℂ) (z : ℂ) (k : ℕ) : ℂ :=
  (t k - 1) * z ^ (k + 1) / ((k + 1 : ℕ) : ℂ)

/-- The normalized logarithmic deviation from Koebe. -/
def logarithmicDeviationSeries (t : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, logarithmicDeviationTerm t z k

/-- The terms of the weighted squared deviation from the Koebe coefficients. -/
def logarithmicDeviationEnergyTerm (t : ℕ → ℂ) (s : ℝ) (k : ℕ) : ℝ :=
  ‖t k - 1‖ ^ 2 * s ^ (k + 1) / ((k + 1 : ℕ) : ℝ)

/-- The weighted squared deviation from the Koebe coefficients. -/
def logarithmicDeviationEnergy (t : ℕ → ℂ) (s : ℝ) : ℝ :=
  ∑' k : ℕ, logarithmicDeviationEnergyTerm t s k

/-- The signed quadratic logarithmic coefficient deficit at positive radius. -/
def logarithmicQuadraticDeficitTerm (t : ℕ → ℂ) (s : ℝ) (k : ℕ) : ℝ :=
  (1 - ‖t k‖ ^ 2) * s ^ (k + 1) / ((k + 1 : ℕ) : ℝ)

private lemma logarithmicDeviationEnergyTerm_add_deficit (t : ℕ → ℂ) (s : ℝ)
    (k : ℕ) : logarithmicDeviationEnergyTerm t s k + logarithmicQuadraticDeficitTerm t s k =
      -2 * (logarithmicDeviationTerm t (s : ℂ) k).re := by
  have hsquare : ‖t k - 1‖ ^ 2 + (1 - ‖t k‖ ^ 2) = -2 * ((t k).re - 1) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    ring
  unfold logarithmicDeviationEnergyTerm logarithmicQuadraticDeficitTerm
    logarithmicDeviationTerm
  rw [mul_div_assoc (t k - 1) ((s : ℂ) ^ (k + 1)) ((k + 1 : ℕ) : ℂ),
    ← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_div]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.sub_re, Complex.one_re]
  calc
    _ = (‖t k - 1‖ ^ 2 + (1 - ‖t k‖ ^ 2)) *
        (s ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by ring
    _ = _ := by rw [hsquare]; ring

/-- The radial energy is bounded by the real part of the logarithmic deviation
when the signed quadratic logarithmic coefficient deficit is nonnegative. -/
theorem logarithmicDeviationEnergy_le_of_nonneg_deficit {t : ℕ → ℂ} {s : ℝ}
    (hlog : Summable (logarithmicDeviationTerm t (s : ℂ)))
    (hdef : Summable (logarithmicQuadraticDeficitTerm t s))
    (hdef_nonneg : 0 ≤ ∑' k : ℕ, logarithmicQuadraticDeficitTerm t s k) :
    Summable (logarithmicDeviationEnergyTerm t s) ∧
      logarithmicDeviationEnergy t s ≤ -2 * (logarithmicDeviationSeries t (s : ℂ)).re := by
  have hre : Summable (fun k ↦ (logarithmicDeviationTerm t (s : ℂ) k).re) :=
    Complex.reCLM.summable hlog
  have henergy_fun : logarithmicDeviationEnergyTerm t s =
      fun k ↦ -2 * (logarithmicDeviationTerm t (s : ℂ) k).re -
        logarithmicQuadraticDeficitTerm t s k := by
    ext k
    linarith only [logarithmicDeviationEnergyTerm_add_deficit t s k]
  have hsum_re : (∑' k : ℕ, (logarithmicDeviationTerm t (s : ℂ) k).re) =
      (logarithmicDeviationSeries t (s : ℂ)).re :=
    (Complex.reCLM.map_tsum hlog).symm
  have henergy_sum : Summable (logarithmicDeviationEnergyTerm t s) := by
    rw [henergy_fun]
    exact (hre.mul_left (-2)).sub hdef
  refine ⟨henergy_sum, ?_⟩
  unfold logarithmicDeviationEnergy
  rw [henergy_fun, (hre.mul_left (-2)).tsum_sub hdef, tsum_mul_left, hsum_re]
  exact sub_le_self _ hdef_nonneg

/-- Cauchy–Schwarz for the logarithmic deviation at the negative radius. -/
theorem logarithmicDeviationSeries_neg_sq_le {t : ℕ → ℂ} {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 < s) (hrs : r ^ 2 < s)
    (hsum : Summable (logarithmicDeviationEnergyTerm t s)) :
    Summable (logarithmicDeviationTerm t (-(r : ℂ))) ∧
      ‖logarithmicDeviationSeries t (-(r : ℂ))‖ ^ 2 ≤
        logarithmicDeviationEnergy t s * (-Real.log (1 - r ^ 2 / s)) := by
  let q := r ^ 2 / s
  have hq : 0 ≤ q := div_nonneg (sq_nonneg _) hs.le
  have hq_lt : q < 1 := (div_lt_one₀ hs).mpr hrs
  let a (k : ℕ) := ‖t k - 1‖ * Real.sqrt (s ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
  let b (k : ℕ) := Real.sqrt (q ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
  have ha_nonneg (k : ℕ) : 0 ≤ a k :=
    mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hb_nonneg (k : ℕ) : 0 ≤ b k := Real.sqrt_nonneg _
  have ha_sq (k : ℕ) : a k ^ (2 : ℝ) = logarithmicDeviationEnergyTerm t s k := by
    dsimp only [a]
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (by positivity)]
    unfold logarithmicDeviationEnergyTerm
    ring
  have hb_sq (k : ℕ) : b k ^ (2 : ℝ) = q ^ (k + 1) / ((k : ℝ) + 1) := by
    dsimp only [b]
    rw [Real.rpow_two, Real.sq_sqrt (by positivity), Nat.cast_add, Nat.cast_one]
  have hb_sum := Real.hasSum_pow_div_log_of_abs_lt_one ((abs_of_nonneg hq).trans_lt hq_lt)
  have ha_summable : Summable (fun k ↦ a k ^ (2 : ℝ)) := by
    simpa only [ha_sq] using hsum
  have hb_summable : Summable (fun k ↦ b k ^ (2 : ℝ)) := by
    simpa only [hb_sq] using hb_sum.summable
  have hholder := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two ha_nonneg hb_nonneg ha_summable hb_summable
  have hnorm (k : ℕ) : ‖logarithmicDeviationTerm t (-(r : ℂ)) k‖ = a k * b k := by
    have hden : 0 ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hq_mul : s * q = r ^ 2 := by
      dsimp [q]
      field_simp [hs.ne']
      <;> ring
    have hradial :
        (s ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) * (q ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) =
          (r ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [div_mul_div_comm, ← mul_pow, hq_mul, div_pow,
        ← pow_two ((k + 1 : ℕ) : ℝ), ← pow_mul, ← pow_mul, Nat.mul_comm 2 (k + 1)]
    unfold logarithmicDeviationTerm
    dsimp only [a, b]
    rw [norm_div, norm_mul, norm_pow, norm_neg, Complex.norm_of_nonneg hr,
      Complex.norm_natCast, mul_assoc ‖t k - 1‖ (Real.sqrt _) (Real.sqrt _),
      ← Real.sqrt_mul (div_nonneg (pow_nonneg hs.le _) hden),
      hradial, Real.sqrt_sq (div_nonneg (pow_nonneg hr _) hden)]
    ring
  have hnorm_sum : Summable (fun k ↦ ‖logarithmicDeviationTerm t (-(r : ℂ)) k‖) := by
    simpa only [hnorm] using hholder.1
  have hbound : ‖logarithmicDeviationSeries t (-(r : ℂ))‖ ≤
      Real.sqrt (logarithmicDeviationEnergy t s) * Real.sqrt (-Real.log (1 - q)) := by
    calc
      _ ≤ ∑' k, ‖logarithmicDeviationTerm t (-(r : ℂ)) k‖ :=
        norm_tsum_le_tsum_norm hnorm_sum
      _ = ∑' k, a k * b k := tsum_congr hnorm
      _ ≤ _ := by
        simpa only [ha_sq, hb_sq, ← Real.sqrt_eq_rpow, hb_sum.tsum_eq,
          logarithmicDeviationEnergy] using hholder.2
  refine ⟨hnorm_sum.of_norm, ?_⟩
  have henergy : 0 ≤ logarithmicDeviationEnergy t s := tsum_nonneg fun k ↦ by
    unfold logarithmicDeviationEnergyTerm
    exact div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hs.le _)) (Nat.cast_nonneg _)
  have hkernel : 0 ≤ -Real.log (1 - q) := by
    rw [← hb_sum.tsum_eq]
    exact tsum_nonneg fun k ↦ div_nonneg (pow_nonneg hq _) (by positivity)
  calc
    _ ≤ (Real.sqrt (logarithmicDeviationEnergy t s) * Real.sqrt (-Real.log (1 - q))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt henergy, Real.sq_sqrt hkernel]

/-- The negative radial deficit can be bounded by the phase error and
the squared logarithmic deviation, using the sharp lower growth bound. -/
theorem real_deficit_conj_mul_exp_le {γ G : ℂ} (hγ : ‖γ‖ = 1) (hG : ‖G‖ ≤ 1 / 2)
    (hw : 1 ≤ ‖conj γ * Complex.exp (2 * G)‖) :
    1 - (conj γ * Complex.exp (2 * G)).re ≤ ‖1 - γ‖ ^ 2 + 16 * ‖G‖ ^ 2 := by
  let w := conj γ * Complex.exp (2 * G)
  have hw_sq : 1 ≤ ‖w‖ ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hw 2
  have hdef : 2 * (1 - w.re) ≤ ‖1 - w‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply] at hw_sq
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    nlinarith only [hw_sq]
  have hG' : ‖(2 : ℂ) * G‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_ofNat]
    linarith only [hG]
  have hexp : ‖1 - Complex.exp (2 * G)‖ ≤ 4 * ‖G‖ := by
    have h := Complex.norm_exp_sub_one_le hG'
    rw [norm_mul, Complex.norm_ofNat] at h
    rw [norm_sub_rev]
    linarith only [h]
  have htriangle : ‖1 - w‖ ≤ ‖1 - γ‖ + 4 * ‖G‖ := by
    have hid : 1 - w = (1 - conj γ) + conj γ * (1 - Complex.exp (2 * G)) := by
      unfold w
      ring
    have hconj : ‖(1 : ℂ) - conj γ‖ = ‖1 - γ‖ := by
      rw [← Complex.norm_conj (1 - γ), map_sub, map_one]
    rw [hid]
    calc
      _ ≤ ‖1 - conj γ‖ + ‖conj γ * (1 - Complex.exp (2 * G))‖ := norm_add_le _ _
      _ ≤ _ := by simpa only [hconj, norm_mul, Complex.norm_conj, hγ, one_mul] using
        add_le_add_right hexp ‖1 - γ‖
  have htriangle_sq := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  change 1 - w.re ≤ _
  nlinarith only [hdef, htriangle_sq, sq_nonneg (‖1 - γ‖ - 4 * ‖G‖)]

/-- At a near-extremal positive radius, the real part of the logarithm is
controlled by the phase-corrected radial deficit. -/
theorem neg_two_re_le_exp_radial_deficit {γ G : ℂ} (hγ : ‖γ‖ = 1)
    (h0 : 0 ≤ 1 - (conj γ * Complex.exp (2 * G)).re)
    (h1 : 1 - (conj γ * Complex.exp (2 * G)).re ≤ 1 / 2) :
    -2 * G.re ≤ 2 * (1 - (conj γ * Complex.exp (2 * G)).re) := by
  let h := 1 - (conj γ * Complex.exp (2 * G)).re
  change 0 ≤ h at h0
  change h ≤ 1 / 2 at h1
  change -2 * G.re ≤ 2 * h
  have hh : 0 < 1 - h := by linarith only [h1]
  have hnorm : 1 - h ≤ Real.exp (2 * G.re) := by
    have hre := Complex.re_le_norm (conj γ * Complex.exp (2 * G))
    have h2 : ((2 : ℂ) * G).re = 2 * G.re := by simp [Complex.mul_re]
    rw [norm_mul, Complex.norm_conj, hγ, one_mul, Complex.norm_exp, h2] at hre
    dsimp only [h]
    linarith only [hre]
  have hlog := Real.log_le_log hh hnorm
  rw [Real.log_exp] at hlog
  have hupper := Real.log_le_sub_one_of_pos (inv_pos.mpr hh)
  rw [Real.log_inv] at hupper
  have hfrac : (1 - h)⁻¹ - 1 ≤ 2 * h := by
    rw [inv_eq_one_div, sub_le_iff_le_add, div_le_iff₀ hh]
    have hh0 : 0 ≤ h := h0
    have hh1 : 0 ≤ 1 - 2 * h := by linarith only [h1]
    nlinarith only [mul_nonneg hh0 hh1]
  linarith only [hlog, hupper, hfrac]

/-- The normalized logarithm of the ratio of the root function to the Koebe root. -/
def normalizedKoebeLogDeviation {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (z : ℂ) : ℂ :=
  normalizedLogarithm hf z / 2 + Complex.log (1 - z)

/-- The deviation series of the logarithmic Taylor coefficients gives the
normalized logarithmic deviation on the open unit disk. -/
theorem hasSum_logarithmicDeviationTerm_logCoeff {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {z : ℂ} (hz : z ∈ unitDisk) :
    HasSum (logarithmicDeviationTerm (fun k ↦ logCoeff hf (k + 1)) z)
      (normalizedKoebeLogDeviation hf z) := by
  let g : ℂ → ℂ := fun w ↦ normalizedLogarithm hf w / 2
  have hg : DifferentiableOn ℂ g unitDisk :=
    (normalizedLogarithm_holomorphic hf).div_const 2
  have hfull : HasSum (fun k : ℕ ↦ coeff g k * z ^ k) (g z) := by
    convert Complex.hasSum_taylorSeries_on_ball hg hz using 1
    funext k
    simp only [coeff, sub_zero, smul_eq_mul]
    ring
  have htail : HasSum (fun k : ℕ ↦ coeff g (k + 1) * z ^ (k + 1)) (g z) := by
    simpa [g] using (hasSum_nat_add_iff' 1).mpr hfull
  have hlog := Complex.hasSum_taylorSeries_neg_log' (mem_unitDisk.mp hz)
  convert htail.sub hlog using 1
  · funext k
    have hk : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    simp only [logarithmicDeviationTerm, logCoeff, Nat.cast_add, Nat.cast_one] at hk ⊢
    change (((k : ℂ) + 1) * coeff g (k + 1) - 1) * z ^ (k + 1) / ((k : ℂ) + 1) =
      coeff g (k + 1) * z ^ (k + 1) - z ^ (k + 1) / ((k : ℂ) + 1)
    field_simp [hk]
    <;> ring
  · simp only [normalizedKoebeLogDeviation, g, sub_neg_eq_add]

private lemma one_sub_ne_zero_in_unitDisk {z : ℂ} (hz : z ∈ unitDisk) : 1 - z ≠ 0 := by
  intro heq
  have hz' := mem_unitDisk.mp hz
  rw [← eq_of_sub_eq_zero heq, norm_one] at hz'
  exact lt_irrefl _ hz'

/-- At nonzero points of the disk, the ratio to Koebe is the exponential of
twice the normalized logarithmic deviation. -/
theorem exp_two_normalizedKoebeLogDeviation {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {z : ℂ} (hz : z ∈ unitDisk) (hz0 : z ≠ 0) :
    Complex.exp (2 * normalizedKoebeLogDeviation hf z) = f z / koebe z := by
  have h₁ : 1 - z ≠ 0 := one_sub_ne_zero_in_unitDisk hz
  rw [normalizedKoebeLogDeviation,
    show 2 * (normalizedLogarithm hf z / 2 + Complex.log (1 - z)) =
      normalizedLogarithm hf z + (Complex.log (1 - z) + Complex.log (1 - z)) by ring,
    Complex.exp_add, Complex.exp_add, exp_normalizedLogarithm hf hz, Complex.exp_log h₁]
  unfold koebe
  rw [← hf.mul_dslope z]
  field_simp [hz0, h₁]

/-- The logarithmic Cauchy–Schwarz kernel at the two manuscript radii. -/
theorem negativeRadius_log_kernel_le {n : ℕ} (hn : 2 ≤ n) {R : ℝ} (hR : 1 ≤ R) :
    -Real.log (1 - (Real.exp (-(R / (n : ℝ)))) ^ 2 / Real.exp (-(1 / (n : ℝ)))) ≤
      2 * Real.log n := by
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  let x : ℝ := 1 / (n : ℝ)
  have hx : 0 < x := one_div_pos.mpr hnpos
  have hq :
      (Real.exp (-(R / (n : ℝ)))) ^ 2 / Real.exp (-(1 / (n : ℝ))) =
        Real.exp (-((2 * R - 1) * x)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    dsimp [x]
    push_cast
    ring
  have hexp : Real.exp (-x) ≤ (n : ℝ) / ((n : ℝ) + 1) := by
    have h := one_div_le_one_div_of_le (show 0 < 1 + x by linarith only [hx])
      (show 1 + x ≤ Real.exp x by simpa only [add_comm] using Real.add_one_le_exp x)
    have hfrac : 1 / (1 + x) = (n : ℝ) / ((n : ℝ) + 1) := by
      dsimp [x]
      field_simp [hnpos.ne', show (n : ℝ) + 1 ≠ 0 by positivity]
      <;> ring
    simpa only [hfrac, one_div (Real.exp x), ← Real.exp_neg] using h
  have hq_le : Real.exp (-((2 * R - 1) * x)) ≤ Real.exp (-x) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hx.le (show 0 ≤ R - 1 by linarith only [hR])]
  have hbase : 1 / ((n : ℝ) + 1) ≤ 1 - Real.exp (-((2 * R - 1) * x)) := by
    have heq : 1 - (n : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) := by
      field_simp [show (n : ℝ) + 1 ≠ 0 by positivity]
      <;> ring
    rw [← heq]
    exact sub_le_sub_left (hq_le.trans hexp) _
  have hlog := Real.log_le_log (by positivity : 0 < 1 / ((n : ℝ) + 1)) hbase
  rw [one_div, Real.log_inv] at hlog
  have hsq : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by
    have hprod := mul_nonneg
      (show 0 ≤ (n : ℝ) - 2 by linarith only [hn₂]) (show 0 ≤ (n : ℝ) + 1 by positivity)
    nlinarith only [hprod]
  have hlogn := Real.log_le_log (by positivity : 0 < (n : ℝ) + 1) hsq
  rw [Real.log_pow] at hlogn
  rw [hq]
  push_cast at hlogn
  linarith only [hlog, hlogn]

end Zalcman
