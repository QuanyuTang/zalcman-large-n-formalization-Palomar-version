/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Comparison of nonnegative radial deficit series

The sequence entry `d j` corresponds to the coefficient of order `j + 1`.
Selective sums, including the odd-coefficient projection, use a sequence with
the excluded entries set to zero. Tail domination uses only the nonnegativity
and linear growth bound of this sequence.
-/

@[expose] public section

noncomputable section

namespace Zalcman

open Filter Finset
open scoped Topology

/-- The normalized radial generating series of coefficient deficits. -/
def radialDeficitSeries (d : ℕ → ℝ) (r : ℝ) : ℝ :=
  (1 - r) ^ 2 * ∑' j : ℕ, d j * r ^ j

theorem radialDeficitSeries_nonneg {d : ℕ → ℝ} (hd : ∀ j, 0 ≤ d j) {r : ℝ}
    (hr : 0 ≤ r) : 0 ≤ radialDeficitSeries d r := by
  exact mul_nonneg (sq_nonneg _) (tsum_nonneg fun j ↦ mul_nonneg (hd j) (pow_nonneg hr j))

private lemma radialDeficitSeries_at_exp (d : ℕ → ℝ) (x : ℝ) :
    radialDeficitSeries d (Real.exp (-x)) =
      (1 - Real.exp (-x)) ^ 2 * ∑' j : ℕ, d j * Real.exp (-x * j) := by
  unfold radialDeficitSeries
  congr 1
  apply tsum_congr
  intro j
  rw [← Real.exp_nat_mul, mul_comm (j : ℝ) (-x)]

private lemma summable_radialDeficit_at_exp {d : ℕ → ℝ} (hd : ∀ j, 0 ≤ d j)
    (hb : ∀ j : ℕ, d j ≤ 2 * ((j : ℝ) + 1)) {x : ℝ} (hx : 0 < x) :
    Summable (fun j : ℕ ↦ d j * Real.exp (-x * j)) := by
  have hm : Summable (fun j : ℕ ↦ (2 * ((j : ℝ) + 1)) * Real.exp (-x * j)) := by
    convert ((Real.summable_pow_mul_exp_neg_nat_mul 1 hx).add
      (Real.summable_pow_mul_exp_neg_nat_mul 0 hx)).mul_left 2 using 1
    ext j
    simp only [pow_one, pow_zero, one_mul]
    ring
  exact Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (hd j) (Real.exp_nonneg _))
    (fun j ↦ mul_le_mul_of_nonneg_right (hb j) (Real.exp_nonneg _)) hm

private lemma one_sub_exp_neg_mul_eq_integral {c : ℝ} (hc : 0 < c) (x : ℝ) :
    1 - Real.exp (-c * x) = c * ∫ u in (0 : ℝ)..x, Real.exp (-c * u) := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hc.ne'),
    integral_exp, mul_zero, Real.exp_zero, smul_eq_mul]
  field_simp [hc.ne']
  ring

private lemma one_sub_exp_neg_ratio {R x : ℝ} (hR : 1 ≤ R) (hx : 0 ≤ x) :
    1 - Real.exp (-(R * x)) ≤ R * (1 - Real.exp (-x)) := by
  have hR' : 0 < R := zero_lt_one.trans_le hR
  have hI : (∫ u in (0 : ℝ)..x, Real.exp (-R * u)) ≤
      ∫ u in (0 : ℝ)..x, Real.exp ((-1 : ℝ) * u) := by
    apply intervalIntegral.integral_mono_on hx
    · exact (show Continuous (fun u : ℝ ↦ Real.exp (-R * u)) by fun_prop).intervalIntegrable _ _
    · exact (show Continuous (fun u : ℝ ↦ Real.exp ((-1 : ℝ) * u)) by fun_prop).intervalIntegrable _ _
    · intro u hu
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hR) hu.1)
  rw [neg_mul_eq_neg_mul, one_sub_exp_neg_mul_eq_integral hR',
    show -x = (-1 : ℝ) * x by ring, one_sub_exp_neg_mul_eq_integral one_pos, one_mul]
  exact mul_le_mul_of_nonneg_left hI hR'.le

/-- The ratio of the radial gaps at exponential spacing at most `R`. -/
theorem exp_radial_gap_ratio_le {R x : ℝ} (hR : 1 ≤ R) (hx : 0 < x) :
    (1 - Real.exp (-(R * x))) / (1 - Real.exp (-x)) ≤ R :=
  (div_le_iff₀ (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)))).mpr
    (one_sub_exp_neg_ratio hR hx.le)

/-- Tail comparison at the radii `exp (-R*x)` and `exp (-x)`. The cutoff `n` is
the number of retained coefficients. -/
theorem radialDeficitSeries_exp_tail_compare {d : ℕ → ℝ} (hd : ∀ j, 0 ≤ d j)
    (hb : ∀ j : ℕ, d j ≤ 2 * ((j : ℝ) + 1)) (n : ℕ) {R x : ℝ}
    (hR : 1 ≤ R) (hx : 0 < x) :
    radialDeficitSeries d (Real.exp (-(R * x))) ≤
      (R * x) ^ 2 * (∑ j ∈ range n, d j) +
        R ^ 2 * Real.exp (-((R - 1) * x) * n) * radialDeficitSeries d (Real.exp (-x)) := by
  let E := Real.exp (-((R - 1) * x) * n)
  have hR' : 0 < R := zero_lt_one.trans_le hR
  have hRx : 0 < R * x := mul_pos hR' hx
  have hA₀ : 0 ≤ 1 - Real.exp (-(R * x)) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hRx.le))
  have hA : (1 - Real.exp (-(R * x))) ^ 2 ≤ (R * x) ^ 2 :=
    pow_le_pow_left₀ hA₀ (by linarith only [Real.one_sub_le_exp_neg (R * x)]) 2
  have hnorm : (1 - Real.exp (-(R * x))) ^ 2 ≤ R ^ 2 * (1 - Real.exp (-x)) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hA₀ (one_sub_exp_neg_ratio hR hx.le) 2
  have hs := summable_radialDeficit_at_exp hd hb hx
  have hr := summable_radialDeficit_at_exp hd hb hRx
  have hpre : (∑ j ∈ range n, d j * Real.exp (-(R * x) * j)) ≤ ∑ j ∈ range n, d j := by
    refine Finset.sum_le_sum fun j _ ↦ ?_
    have hExp : Real.exp (-(R * x) * j) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hRx.le) (Nat.cast_nonneg j))
    calc
      _ ≤ d j * 1 := mul_le_mul_of_nonneg_left hExp (hd j)
      _ = _ := mul_one _
  have hpreR₀ : 0 ≤ ∑ j ∈ range n, d j * Real.exp (-(R * x) * j) :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (hd j) (Real.exp_nonneg _)
  have hpreS₀ : 0 ≤ ∑ j ∈ range n, d j * Real.exp (-x * j) :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (hd j) (Real.exp_nonneg _)
  have hterm (j : ℕ) : d (j + n) * Real.exp (-(R * x) * (j + n : ℕ)) ≤
      E * (d (j + n) * Real.exp (-x * (j + n : ℕ))) := by
    have hcast : (n : ℝ) ≤ (j + n : ℕ) := by exact_mod_cast Nat.le_add_left n j
    have hneg : -((R - 1) * x) ≤ 0 := by
      exact neg_nonpos.mpr (mul_nonneg (sub_nonneg.mpr hR) hx.le)
    have hexp : Real.exp (-((R - 1) * x) * (j + n : ℕ)) ≤ E :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hcast hneg)
    have hdecomp : Real.exp (-(R * x) * (j + n : ℕ)) =
        Real.exp (-((R - 1) * x) * (j + n : ℕ)) * Real.exp (-x * (j + n : ℕ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hdecomp, show d (j + n) * (Real.exp (-((R - 1) * x) * (j + n : ℕ)) *
      Real.exp (-x * (j + n : ℕ))) = Real.exp (-((R - 1) * x) * (j + n : ℕ)) *
      (d (j + n) * Real.exp (-x * (j + n : ℕ))) by ring]
    exact mul_le_mul_of_nonneg_right hexp (mul_nonneg (hd _) (Real.exp_nonneg _))
  have hrTail : Summable (fun j : ℕ ↦ d (j + n) * Real.exp (-(R * x) * (j + n : ℕ))) :=
    (summable_nat_add_iff n).mpr hr
  have hsTail : Summable (fun j : ℕ ↦ d (j + n) * Real.exp (-x * (j + n : ℕ))) :=
    (summable_nat_add_iff n).mpr hs
  have htsum : (∑' j : ℕ, d (j + n) * Real.exp (-(R * x) * (j + n : ℕ))) ≤
      E * ∑' j : ℕ, d j * Real.exp (-x * j) := by
    calc
      _ ≤ ∑' j : ℕ, E * (d (j + n) * Real.exp (-x * (j + n : ℕ))) :=
        hrTail.tsum_le_tsum hterm (hsTail.mul_left E)
      _ = E * ∑' j : ℕ, d (j + n) * Real.exp (-x * (j + n : ℕ)) := tsum_mul_left
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        rw [← hs.sum_add_tsum_nat_add n]
        exact le_add_of_nonneg_left hpreS₀
  have htail₀ : 0 ≤ ∑' j : ℕ, d (j + n) * Real.exp (-(R * x) * (j + n : ℕ)) :=
    tsum_nonneg fun j ↦ mul_nonneg (hd _) (Real.exp_nonneg _)
  rw [radialDeficitSeries_at_exp d (R * x), radialDeficitSeries_at_exp d x,
    ← hr.sum_add_tsum_nat_add n, mul_add]
  calc
    _ ≤ (R * x) ^ 2 * (∑ j ∈ range n, d j) +
        (R ^ 2 * (1 - Real.exp (-x)) ^ 2) * (E * ∑' j : ℕ, d j * Real.exp (-x * j)) := by
      exact add_le_add (mul_le_mul hA hpre hpreR₀ (sq_nonneg _))
        (mul_le_mul hnorm htsum htail₀ (by positivity))
    _ = _ := by dsimp only [E]; ring

/-- If the radial estimate amplifies the smaller-radius deficit by at most `A`,
the exponentially small tail is absorbed and only the initial block remains. -/
theorem radialDeficitSeries_exp_absorb {d : ℕ → ℝ} (hd : ∀ j, 0 ≤ d j)
    (hb : ∀ j : ℕ, d j ≤ 2 * ((j : ℝ) + 1)) (n : ℕ) {R x A : ℝ}
    (hR : 1 ≤ R) (hx : 0 < x) (hA : 0 ≤ A)
    (hprop : radialDeficitSeries d (Real.exp (-x)) ≤ A * radialDeficitSeries d (Real.exp (-(R * x))))
    (hsmall : A * R ^ 2 * Real.exp (-((R - 1) * x) * n) ≤ 1 / 4) :
    radialDeficitSeries d (Real.exp (-x)) ≤ 2 * A * (R * x) ^ 2 * (∑ j ∈ range n, d j) := by
  have ht := radialDeficitSeries_exp_tail_compare hd hb n hR hx
  have hw : 0 ≤ radialDeficitSeries d (Real.exp (-x)) :=
    radialDeficitSeries_nonneg hd (Real.exp_nonneg _)
  have hl := hprop.trans (mul_le_mul_of_nonneg_left ht hA)
  have htail := mul_le_mul_of_nonneg_right hsmall hw
  nlinarith only [hl, htail, hw]

/-- The absorption estimate at the radii `exp (-R/n)` and `exp (-1/n)`. -/
theorem radialDeficitSeries_absorb_at_one_over {d : ℕ → ℝ} (hd : ∀ j, 0 ≤ d j)
    (hb : ∀ j : ℕ, d j ≤ 2 * ((j : ℝ) + 1)) {n : ℕ} (hn : 0 < n) {R A : ℝ}
    (hR : 1 ≤ R) (hA : 0 ≤ A)
    (hprop : radialDeficitSeries d (Real.exp (-(1 / (n : ℝ)))) ≤
      A * radialDeficitSeries d (Real.exp (-(R / (n : ℝ)))))
    (hsmall : A * R ^ 2 * Real.exp (-(R - 1)) ≤ 1 / 4) :
    radialDeficitSeries d (Real.exp (-(1 / (n : ℝ)))) ≤
      2 * A * (R / (n : ℝ)) ^ 2 * ∑ j ∈ range n, d j := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hx : 0 < 1 / (n : ℝ) := one_div_pos.mpr hn'
  have he : -((R - 1) * (1 / (n : ℝ))) * (n : ℝ) = -(R - 1) := by
    field_simp [hn'.ne']
  have hp' : radialDeficitSeries d (Real.exp (-(1 / (n : ℝ)))) ≤
      A * radialDeficitSeries d (Real.exp (-(R * (1 / (n : ℝ))))) := by
    simpa only [mul_one_div] using hprop
  have hs' : A * R ^ 2 * Real.exp (-((R - 1) * (1 / (n : ℝ))) * (n : ℝ)) ≤ 1 / 4 := by
    simpa only [he] using hsmall
  simpa only [mul_one_div] using radialDeficitSeries_exp_absorb hd hb n hR hx hA hp' hs'

private lemma lower_bound_one_sub_exp_neg {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    Real.exp (-1) * x ≤ 1 - Real.exp (-x) := by
  rw [show -x = (-1 : ℝ) * x by ring, one_sub_exp_neg_mul_eq_integral one_pos, one_mul]
  have hi : (∫ _ in (0 : ℝ)..x, Real.exp (-1)) ≤ ∫ u in (0 : ℝ)..x, Real.exp ((-1 : ℝ) * u) := by
    apply intervalIntegral.integral_mono_on hx
    · exact intervalIntegrable_const
    · exact (show Continuous (fun u : ℝ ↦ Real.exp ((-1 : ℝ) * u)) by fun_prop).intervalIntegrable _ _
    · intro u hu
      apply Real.exp_le_exp.mpr
      linarith only [hu.2, hx']
  simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hi

/-- A radial estimate at `exp (-1/n)` controls the unweighted mass of the first
`4*n` deficits with an explicit absolute constant. -/
theorem radialDeficitSeries_mass_le {d : ℕ → ℝ} (hd : ∀ j, 0 ≤ d j)
    (hb : ∀ j : ℕ, d j ≤ 2 * ((j : ℝ) + 1)) {n : ℕ} (hn : 0 < n) :
    (∑ j ∈ range (4 * n), d j) ≤ Real.exp 6 * (n : ℝ) ^ 2 *
      radialDeficitSeries d (Real.exp (-(1 / (n : ℝ)))) := by
  let x : ℝ := 1 / (n : ℝ)
  let W := radialDeficitSeries d (Real.exp (-x))
  let M := ∑ j ∈ range (4 * n), d j
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hx : 0 < x := by dsimp only [x]; positivity
  have hx1 : x ≤ 1 := (div_le_one hn').mpr hn1
  have hM₀ : 0 ≤ M := Finset.sum_nonneg fun j _ ↦ hd j
  have hs := summable_radialDeficit_at_exp hd hb hx
  have hA : (Real.exp (-1) * x) ^ 2 ≤ (1 - Real.exp (-x)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (lower_bound_one_sub_exp_neg hx.le hx1) 2
  have hpre : Real.exp (-4) * M ≤ ∑ j ∈ range (4 * n), d j * Real.exp (-x * j) := by
    dsimp only [M]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj ↦ ?_
    have hcut : (j : ℝ) ≤ 4 * (n : ℝ) := by
      exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
    have hmul : x * (j : ℝ) ≤ 4 := calc
      _ ≤ x * (4 * (n : ℝ)) := mul_le_mul_of_nonneg_left hcut hx.le
      _ = _ := by dsimp only [x]; field_simp [hn'.ne']
    have hExp : Real.exp (-4) ≤ Real.exp (-x * j) := Real.exp_le_exp.mpr (by linarith)
    rw [mul_comm (Real.exp (-4))]
    exact mul_le_mul_of_nonneg_left hExp (hd j)
  have hconst : (Real.exp (-1) * x) ^ 2 * Real.exp (-4) = Real.exp (-6) * x ^ 2 := by
    rw [mul_pow]
    calc
      _ = (Real.exp (-1) ^ 2 * Real.exp (-4)) * x ^ 2 := by ring
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have hW : (Real.exp (-6) * x ^ 2) * M ≤ W := by
    dsimp only [W]
    rw [radialDeficitSeries_at_exp, ← hconst, mul_assoc]
    refine mul_le_mul hA (hpre.trans (hs.sum_le_tsum _ fun j _ ↦ ?_))
      (mul_nonneg (Real.exp_nonneg _) hM₀) (sq_nonneg _)
    exact mul_nonneg (hd j) (Real.exp_nonneg _)
  change M ≤ Real.exp 6 * (n : ℝ) ^ 2 * W
  calc
    _ ≤ W / (Real.exp (-6) * x ^ 2) := (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hW)
    _ = _ := by
      dsimp only [x]
      rw [Real.exp_neg]
      field_simp [hn'.ne', Real.exp_ne_zero 6]

/-- The radial transfer factor can be made small by taking the radius separation large. -/
theorem exists_radialDeficitSeries_tail_ratio (K B : ℝ) :
    ∃ R : ℝ, 2 < R ∧ 2 * K * R ^ (B + 2) * Real.exp (-(R - 1)) < 1 / 4 := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (B + 2) 1 one_pos).const_mul
    (2 * K * Real.exp 1)
  have hlim : Tendsto (fun R : ℝ ↦ 2 * K * R ^ (B + 2) * Real.exp (-(R - 1))) atTop (𝓝 0) := by
    rw [mul_zero] at h
    refine h.congr' (Filter.Eventually.of_forall fun R ↦ ?_)
    change 2 * K * Real.exp 1 * (R ^ (B + 2) * Real.exp (-1 * R)) =
      2 * K * R ^ (B + 2) * Real.exp (-(R - 1))
    rw [show -(R - 1) = 1 + -1 * R by ring, Real.exp_add]
    ring
  obtain ⟨L, hL⟩ := eventually_atTop.mp (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4))
  exact ⟨max L 3, (by norm_num : (2 : ℝ) < 3).trans_le (le_max_right _ _),
    hL _ (le_max_left _ _)⟩

/-- The smaller family of radii is eventually above any fixed modulus below one. -/
theorem exists_radialDeficitSeries_radius_threshold {R r₀ : ℝ} (hr₀ : r₀ < 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → r₀ ≤ Real.exp (-(R / (n : ℝ))) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (R / (1 - r₀))
  refine ⟨max 1 M, le_max_left _ _, fun n hn ↦ ?_⟩
  have hMle : M ≤ n := (le_max_right _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hbound : R / (1 - r₀) ≤ n := hM.trans (by exact_mod_cast hMle)
  have hprod : R ≤ (1 - r₀) * (n : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ (sub_pos.mpr hr₀)).mp hbound
  have hdiv : R / (n : ℝ) ≤ 1 - r₀ := (div_le_iff₀ hnpos).mpr hprod
  exact (show r₀ ≤ 1 - R / (n : ℝ) by linarith only [hdiv]).trans
    (Real.one_sub_le_exp_neg _)

end Zalcman
