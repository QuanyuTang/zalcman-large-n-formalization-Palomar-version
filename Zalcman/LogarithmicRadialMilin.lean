/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CoefficientBound
public import Zalcman.NegativeRadius
public import Zalcman.RadialProjection
public import Zalcman.SharpLowerGrowth
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The signed logarithmic deficit as a radial average of Milin sums
-/

public section

open scoped ComplexConjugate

namespace Zalcman.MilinCoefficients

open Finset

private lemma milinSum_as_weighted_logarithmic_deficit (d : MilinCoefficients) (n : ℕ) :
    d.milinSum (n + 2) = ∑ k ∈ range (n + 1),
      ((n - k + 1 : ℕ) : ℝ) * (1 - ‖d.t (k + 1)‖ ^ 2) / ((k + 1 : ℕ) : ℝ) := by
  unfold milinSum
  rw [Finset.sum_range_succ]
  have hlast : (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) + 1) - 1) *
      (1 - ‖d.t ((n + 1) + 1)‖ ^ 2) = 0 := by
    push_cast
    field_simp [show (n : ℝ) + 1 + 1 ≠ 0 by positivity]
    <;> ring
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [Nat.cast_add, Nat.cast_sub hkn, Nat.cast_one, Nat.cast_ofNat]
  field_simp [show (k : ℝ) + 1 ≠ 0 by positivity]
  <;> ring

/-- The quadratic logarithmic coefficient deficit is the normalized weighted
average of the finite Milin sums, by the absolutely convergent Cauchy product. -/
theorem tsum_logarithmicQuadraticDeficit_eq_radial_milinSum (d : MilinCoefficients)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1)
    (habs : Summable (fun k ↦ ‖logarithmicQuadraticDeficitTerm (fun j ↦ d.t (j + 1)) s k‖)) :
    (∑' k, logarithmicQuadraticDeficitTerm (fun j ↦ d.t (j + 1)) s k) * (1 / (1 - s) ^ 2) =
       ∑' n : ℕ, s ^ (n + 1) * d.milinSum (n + 2) := by
  let br (j : ℕ) : ℝ := ((j + 1 : ℕ) : ℝ) * s ^ j
  have hs_abs : ‖s‖ < 1 := (Real.norm_of_nonneg hs).trans_lt hs1
  have hbr : HasSum br (1 / (1 - s) ^ 2) := by
    simpa only [br, Nat.choose_one_right] using hasSum_choose_mul_geometric_of_norm_lt_one 1 hs_abs
  have hbr_abs : Summable (fun j ↦ ‖br j‖) := by
    refine hbr.summable.congr fun j ↦ ?_
    exact (Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs _))).symm
  rw [← hbr.tsum_eq, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm habs hbr_abs]
  apply tsum_congr
  intro n
  rw [d.milinSum_as_weighted_logarithmic_deficit, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hpow : s ^ (k + 1) * s ^ (n - k) = s ^ (n + 1) := by
    rw [← pow_add, show k + 1 + (n - k) = n + 1 by omega]
  unfold logarithmicQuadraticDeficitTerm br
  calc
    _ = (s ^ (k + 1) * s ^ (n - k)) *
        (((n - k + 1 : ℕ) : ℝ) * (1 - ‖d.t (k + 1)‖ ^ 2) / ((k + 1 : ℕ) : ℝ)) := by ring
    _ = _ := by rw [hpow]

/-- Finite Milin positivity implies nonnegativity of the weighted infinite deficit. -/
theorem tsum_logarithmicQuadraticDeficit_nonneg (d : MilinCoefficients)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1)
    (habs : Summable (fun k ↦ ‖logarithmicQuadraticDeficitTerm (fun j ↦ d.t (j + 1)) s k‖))
    (hm : ∀ n, 0 ≤ d.milinSum (n + 2)) :
    0 ≤ ∑' k, logarithmicQuadraticDeficitTerm (fun j ↦ d.t (j + 1)) s k := by
  apply nonneg_of_mul_nonneg_left _ (one_div_pos.mpr (sq_pos_of_pos (sub_pos.mpr hs1)))
  rw [d.tsum_logarithmicQuadraticDeficit_eq_radial_milinSum hs hs1 habs]
  exact tsum_nonneg fun n ↦ mul_nonneg (pow_nonneg hs _) (hm n)

end Zalcman.MilinCoefficients

namespace Zalcman

/-- The quadratic logarithmic coefficient deficit converges absolutely at every
nonnegative radius below one. -/
theorem summable_norm_logarithmicQuadraticDeficit {f : ℂ → ℂ}
    (hf : NormalizedUnivalent f) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    Summable (fun k ↦ ‖logarithmicQuadraticDeficitTerm (fun j ↦ logCoeff hf (j + 1)) s k‖) := by
  have hsqrt : Real.sqrt s < 1 := (Real.sqrt_lt' one_pos).mpr (by simpa using hs1)
  obtain ⟨ρ, hρ, hρ1⟩ := exists_between hsqrt
  have hρ0 : 0 < ρ := (Real.sqrt_nonneg s).trans_lt hρ
  have hsρ : s < ρ ^ 2 := (Real.sqrt_lt' hρ0).mp hρ
  have hρ_disk : (ρ : ℂ) ∈ unitDisk := mem_unitDisk.mpr
    ((Complex.norm_of_nonneg hρ0.le).trans_lt hρ1)
  let g : ℂ → ℂ := fun z ↦ normalizedLogarithm hf z / 2
  have hg : DifferentiableOn ℂ g unitDisk := (normalizedLogarithm_holomorphic hf).div_const 2
  have htaylor : HasSum (fun m : ℕ ↦ coeff g m * (ρ : ℂ) ^ m) (g (ρ : ℂ)) := by
    convert Complex.hasSum_taylorSeries_on_ball hg hρ_disk using 1
    funext m
    simp only [coeff, sub_zero, smul_eq_mul]
    ring
  obtain ⟨M, hM⟩ := htaylor.summable.tendsto_atTop_zero.norm.bddAbove_range
  let K := max 0 M
  have hcoeff (m : ℕ) : ‖coeff g m‖ * ρ ^ m ≤ K := by
    have hm := hM (Set.mem_range_self m)
    rw [norm_mul, norm_pow, Complex.norm_of_nonneg hρ0.le] at hm
    exact hm.trans (le_max_right _ _)
  let q := s / ρ ^ 2
  have hq0 : 0 ≤ q := div_nonneg hs (sq_nonneg _)
  have hq1 : q < 1 := (div_lt_one₀ (sq_pos_of_pos hρ0)).mpr hsρ
  have hg₁ := (hasSum_geometric_of_norm_lt_one ((Real.norm_of_nonneg hs).trans_lt hs1)).summable
  have hg₂ := (hasSum_coe_mul_geometric_of_norm_lt_one
    ((Real.norm_of_nonneg hq0).trans_lt hq1)).summable
  have hmajor : Summable (fun k : ℕ ↦
      s ^ (k + 1) + K ^ 2 * ((k + 1 : ℕ) : ℝ) * q ^ (k + 1)) := by
    convert (summable_nat_add_iff 1).mpr (hg₁.add (hg₂.mul_left (K ^ 2))) using 1
    funext k
    ring
  refine Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) (fun k ↦ ?_) hmajor
  let m := k + 1
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have hm0 : 0 < (m : ℝ) := by linarith only [hm]
  have hpow : (ρ ^ m) ^ 2 * q ^ m = s ^ m := by
    have hprod : ρ ^ 2 * q = s := by
      dsimp [q]
      field_simp [hρ0.ne']
    rw [← pow_mul, Nat.mul_comm m 2, pow_mul, ← mul_pow, hprod]
  have hnormeq : ‖logCoeff hf m‖ ^ 2 * s ^ m / (m : ℝ) =
      (m : ℝ) * (‖coeff g m‖ * ρ ^ m) ^ 2 * q ^ m := by
    change ‖(m : ℂ) * coeff g m‖ ^ 2 * s ^ m / (m : ℝ) = _
    rw [norm_mul, Complex.norm_natCast, mul_pow, mul_pow, ← hpow]
    field_simp [hm0.ne']
  have hnormle : ‖logCoeff hf m‖ ^ 2 * s ^ m / (m : ℝ) ≤ K ^ 2 * (m : ℝ) * q ^ m := by
    rw [hnormeq, mul_comm (K ^ 2) (m : ℝ)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (pow_nonneg hρ0.le _)) (hcoeff m) 2)
        hm0.le) (pow_nonneg hq0 _)
  have hbase : s ^ m / (m : ℝ) ≤ s ^ m := by
    rw [div_le_iff₀ hm0]
    exact le_mul_of_one_le_right (pow_nonneg hs _) hm
  change ‖(1 - ‖logCoeff hf m‖ ^ 2) * s ^ m / (m : ℝ)‖ ≤
    s ^ m + K ^ 2 * (m : ℝ) * q ^ m
  rw [norm_div, norm_mul, Real.norm_of_nonneg (pow_nonneg hs _),
    Real.norm_of_nonneg hm0.le]
  calc
    _ ≤ (1 + ‖logCoeff hf m‖ ^ 2) * s ^ m / (m : ℝ) := by
      have h := norm_sub_le (1 : ℝ) (‖logCoeff hf m‖ ^ 2)
      rw [norm_one, Real.norm_of_nonneg (sq_nonneg _)] at h
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h (pow_nonneg hs _)) hm0.le
    _ = s ^ m / (m : ℝ) + ‖logCoeff hf m‖ ^ 2 * s ^ m / (m : ℝ) := by ring
    _ ≤ _ := add_le_add hbase hnormle

/-- Analytic logarithmic coefficients satisfy the signed radial positivity whenever
the finite Milin sums are nonnegative. -/
theorem tsum_logarithmicQuadraticDeficit_nonneg_of_milin {f : ℂ → ℂ}
    (hf : NormalizedUnivalent f) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1)
    (hm : ∀ n, 0 ≤ (milinCoefficients hf).milinSum n) :
    0 ≤ ∑' k, logarithmicQuadraticDeficitTerm (fun j ↦ logCoeff hf (j + 1)) s k :=
  (milinCoefficients hf).tsum_logarithmicQuadraticDeficit_nonneg hs hs1
    (summable_norm_logarithmicQuadraticDeficit hf hs hs1) (fun n ↦ hm (n + 2))

/-- The negative-radius deficit is controlled by the phase error and the
positive-radius deficit times the logarithmic kernel. -/
theorem negative_radialPhaseDeficit_le {f : ℂ → ℂ}
    (hf : NormalizedUnivalent f) {γ : ℂ} (hγ : ‖γ‖ = 1)
    (hm : ∀ n, 0 ≤ (milinCoefficients hf).milinSum n)
    {r s : ℝ} (hr : 0 < r) (hr1 : r < 1) (hs : 0 < s) (hs1 : s < 1) (hrs : r ^ 2 < s)
    (hsmall : radialPhaseDeficit f γ s ≤ 1 / 2)
    (hkernel_small : 2 * radialPhaseDeficit f γ s * (-Real.log (1 - r ^ 2 / s)) ≤ 1 / 4) :
    radialPhaseDeficit f γ (-r) ≤
      ‖1 - γ‖ ^ 2 + 32 * radialPhaseDeficit f γ s * (-Real.log (1 - r ^ 2 / s)) := by
  have hs_mem : (s : ℂ) ∈ unitDisk := mem_unitDisk.mpr
    ((Complex.norm_of_nonneg hs.le).trans_lt hs1)
  have hr_norm : ‖-(r : ℂ)‖ = r := by rw [norm_neg, Complex.norm_of_nonneg hr.le]
  have hr_mem : -(r : ℂ) ∈ unitDisk := mem_unitDisk.mpr (hr_norm.trans_lt hr1)
  have hr0 : -(r : ℂ) ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hr.ne')
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  let t (k : ℕ) := logCoeff hf (k + 1)
  let G := normalizedKoebeLogDeviation hf
  have hkernel : 0 ≤ -Real.log (1 - r ^ 2 / s) := by
    apply neg_nonneg.mpr
    exact Real.log_nonpos (sub_pos.mpr ((div_lt_one₀ hs).mpr hrs)).le
      (sub_le_self _ (div_nonneg (sq_nonneg _) hs.le))
  have hexp_s : Complex.exp (2 * G (s : ℂ)) = f (s : ℂ) / koebe (s : ℂ) :=
    exp_two_normalizedKoebeLogDeviation hf hs_mem hs0
  have hcoeff (n : ℕ) : ‖coeff f n‖ ≤ n := norm_coeff_le_of_milinSum_nonneg hf (hm n)
  have hsdef0 := radialPhaseDeficit_nonneg hf hγ hcoeff hs hs1
  have hs_re : -2 * (G (s : ℂ)).re ≤ 2 * radialPhaseDeficit f γ s := by
    simpa only [hexp_s, radialPhaseDeficit] using neg_two_re_le_exp_radial_deficit (G := G (s : ℂ)) hγ
      (by simpa only [hexp_s, radialPhaseDeficit] using hsdef0)
      (by simpa only [hexp_s, radialPhaseDeficit] using hsmall)
  have hslog := hasSum_logarithmicDeviationTerm_logCoeff hf hs_mem
  have hrlog := hasSum_logarithmicDeviationTerm_logCoeff hf hr_mem
  have henergy := logarithmicDeviationEnergy_le_of_nonneg_deficit
    hslog.summable (summable_norm_logarithmicQuadraticDeficit hf hs.le hs1).of_norm
    (tsum_logarithmicQuadraticDeficit_nonneg_of_milin hf hs.le hs1 hm)
  have henergy_le : logarithmicDeviationEnergy t s ≤ 2 * radialPhaseDeficit f γ s := by
    have h := henergy.2
    rw [logarithmicDeviationSeries, hslog.tsum_eq] at h
    exact h.trans hs_re
  have hm_le : ‖G (-(r : ℂ))‖ ^ 2 ≤
      2 * radialPhaseDeficit f γ s * (-Real.log (1 - r ^ 2 / s)) := by
    have h := (logarithmicDeviationSeries_neg_sq_le hr.le hs hrs henergy.1).2
    rw [logarithmicDeviationSeries, hrlog.tsum_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_right henergy_le hkernel)
  have hG_small : ‖G (-(r : ℂ))‖ ≤ 1 / 2 :=
    le_of_sq_le_sq (hm_le.trans (by convert hkernel_small using 1 <;> norm_num))
      (by norm_num)
  have hexp_r : Complex.exp (2 * G (-(r : ℂ))) = f (-(r : ℂ)) / koebe (-(r : ℂ)) :=
    exp_two_normalizedKoebeLogDeviation hf hr_mem hr0
  have hkoebe : ‖koebe (-(r : ℂ))‖ = r / (1 + r) ^ 2 := by
    have heq : (1 : ℂ) - (-(r : ℂ)) = Complex.ofReal (1 + r) := by
      rw [sub_neg_eq_add, Complex.ofReal_add, Complex.ofReal_one]
    rw [koebe, norm_div, norm_pow, hr_norm, heq, Complex.norm_of_nonneg (by positivity)]
  have hnorm_r : 1 ≤ ‖conj γ * Complex.exp (2 * G (-(r : ℂ)))‖ := by
    rw [norm_mul, Complex.norm_conj, hγ, one_mul, hexp_r, norm_div, hkoebe,
      le_div_iff₀ (by positivity), one_mul]
    simpa only [hr_norm] using sharp_lower_growth hf hr_mem
  have hbound := real_deficit_conj_mul_exp_le hγ hG_small hnorm_r
  rw [hexp_r] at hbound
  calc
    _ ≤ ‖1 - γ‖ ^ 2 + 16 * ‖G (-(r : ℂ))‖ ^ 2 := by
      simpa only [radialPhaseDeficit, Complex.ofReal_neg] using hbound
    _ ≤ _ := by
      have hmul := mul_le_mul_of_nonneg_left hm_le (show 0 ≤ (16 : ℝ) by norm_num)
      nlinarith only [hmul]

/-- At the exponentially spaced radii, the negative deficit is at most the
phase error plus a logarithmic multiple of the positive deficit. -/
theorem negative_radialPhaseDeficit_at_exp_le {f : ℂ → ℂ}
    (hf : NormalizedUnivalent f) {γ : ℂ} (hγ : ‖γ‖ = 1)
    (hm : ∀ n, 0 ≤ (milinCoefficients hf).milinSum n)
    {n : ℕ} (hn : 2 ≤ n) {R : ℝ} (hR : 1 ≤ R) :
    let r := Real.exp (-(R / (n : ℝ)))
    let s := Real.exp (-(1 / (n : ℝ)))
    radialPhaseDeficit f γ s ≤ 1 / 2 →
    4 * radialPhaseDeficit f γ s * Real.log (n : ℝ) ≤ 1 / 4 →
      radialPhaseDeficit f γ (-r) ≤ ‖1 - γ‖ ^ 2 + 64 * radialPhaseDeficit f γ s * Real.log (n : ℝ) := by
  let r := Real.exp (-(R / (n : ℝ)))
  let s := Real.exp (-(1 / (n : ℝ)))
  change radialPhaseDeficit f γ s ≤ 1 / 2 →
    4 * radialPhaseDeficit f γ s * Real.log (n : ℝ) ≤ 1 / 4 →
      radialPhaseDeficit f γ (-r) ≤ ‖1 - γ‖ ^ 2 + 64 * radialPhaseDeficit f γ s * Real.log (n : ℝ)
  intro hsmall hkernel_small
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith only [hn']
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hr : 0 < r := Real.exp_pos _
  have hs : 0 < s := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (div_pos hR0 hn0))
  have hs1 : s < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (one_div_pos.mpr hn0))
  have hrs : r ^ 2 < s := by
    dsimp only [r, s]
    rw [← Real.exp_nat_mul, Real.exp_lt_exp, Nat.cast_ofNat, mul_neg, neg_lt_neg_iff,
      ← mul_div_assoc, div_lt_div_iff_of_pos_right hn0]
    linarith only [hR]
  have hs_0 : 0 ≤ radialPhaseDeficit f γ s :=
    radialPhaseDeficit_nonneg hf hγ (fun j ↦ norm_coeff_le_of_milinSum_nonneg hf (hm j)) hs hs1
  have hkernel : -Real.log (1 - r ^ 2 / s) ≤ 2 * Real.log (n : ℝ) :=
    negativeRadius_log_kernel_le hn hR
  have hkernel_small' : 2 * radialPhaseDeficit f γ s * (-Real.log (1 - r ^ 2 / s)) ≤ 1 / 4 := by
    calc
      _ ≤ 2 * radialPhaseDeficit f γ s * (2 * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hkernel (mul_nonneg (by norm_num) hs_0)
      _ = 4 * radialPhaseDeficit f γ s * Real.log (n : ℝ) := by ring
      _ ≤ _ := hkernel_small
  calc
    _ ≤ ‖1 - γ‖ ^ 2 + 32 * radialPhaseDeficit f γ s * (-Real.log (1 - r ^ 2 / s)) :=
      negative_radialPhaseDeficit_le hf hγ hm hr hr1 hs hs1 hrs hsmall hkernel_small'
    _ ≤ ‖1 - γ‖ ^ 2 + 32 * radialPhaseDeficit f γ s * (2 * Real.log (n : ℝ)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hkernel (mul_nonneg (by norm_num) hs_0)) _
    _ = _ := by ring

end Zalcman
