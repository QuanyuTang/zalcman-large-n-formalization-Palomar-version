/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Tactic.LinearCombination

/-!
# Normalized univalent functions and the Koebe function

We define the Taylor coefficients at the origin and prove the normalization,
injectivity, and coefficient formula for the Koebe rotations.
-/

@[expose] public section

namespace Zalcman

open scoped ComplexConjugate

/-- The open unit disk in the complex plane. -/
def unitDisk : Set ℂ := Metric.ball 0 1

lemma mem_unitDisk {z : ℂ} : z ∈ unitDisk ↔ ‖z‖ < 1 := by
  simp [unitDisk, Metric.mem_ball, dist_zero_right]

lemma zero_mem_unitDisk : (0 : ℂ) ∈ unitDisk := mem_unitDisk.mpr (by simp)

/-- The classical class `S` of normalized univalent functions on the unit disk.
Values of the ambient function outside `unitDisk` do not enter this predicate. -/
structure NormalizedUnivalent (f : ℂ → ℂ) : Prop where
  holomorphic : DifferentiableOn ℂ f unitDisk
  injective : Set.InjOn f unitDisk
  map_zero : f 0 = 0
  deriv_zero : deriv f 0 = 1

/-- The coefficient of `z ^ n` in the Taylor expansion of `f` at zero. -/
noncomputable def coeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

@[simp] lemma coeff_zero (f : ℂ → ℂ) : coeff f 0 = f 0 := by simp [coeff]

@[simp] lemma coeff_one (f : ℂ → ℂ) : coeff f 1 = deriv f 0 := by simp [coeff]

lemma taylor_eq_on_unitDisk {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisk)
    {z : ℂ} (hz : z ∈ unitDisk) : ∑' n : ℕ, coeff f n * z ^ n = f z := by
  simpa only [coeff, sub_zero] using Complex.taylorSeries_eq_on_ball' hz hf

/-- The Koebe function. -/
noncomputable def koebe (z : ℂ) : ℂ := z / (1 - z) ^ 2

/-- Rotation of the argument and value by opposite angles. -/
noncomputable def rotate (lam : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ := conj lam * f (lam * z)

/-- Agreement on the unit disk with a unit-circle rotation of the Koebe function. -/
def IsKoebeRotation (f : ℂ → ℂ) : Prop :=
  ∃ lam : ℂ, ‖lam‖ = 1 ∧ Set.EqOn f (rotate lam koebe) unitDisk

private lemma conj_mul_self_of_norm_one {lam : ℂ} (hlam : ‖lam‖ = 1) : conj lam * lam = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hlam]
  norm_num

private lemma one_sub_ne_zero_of_mem_unitDisk {z : ℂ} (hz : z ∈ unitDisk) : 1 - z ≠ 0 := by
  intro h
  have hz' := mem_unitDisk.mp hz
  rw [← eq_of_sub_eq_zero h] at hz'
  simp at hz'

theorem koebe_normalizedUnivalent : NormalizedUnivalent koebe := by
  refine ⟨?_, ?_, by simp [koebe], ?_⟩
  · have hden : DifferentiableOn ℂ (fun z : ℂ ↦ (1 - z) ^ 2) unitDisk := by
      fun_prop
    exact differentiableOn_id.div hden (fun _ hz ↦ pow_ne_zero _ (one_sub_ne_zero_of_mem_unitDisk hz))
  · intro z hz w hw heq
    have hzw : 1 - z * w ≠ 0 := by
      apply one_sub_ne_zero_of_mem_unitDisk
      rw [mem_unitDisk, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (mem_unitDisk.mp hz).le).trans_lt
        (mem_unitDisk.mp hw)
    have hcross := (div_eq_div_iff (pow_ne_zero 2 (one_sub_ne_zero_of_mem_unitDisk hz))
      (pow_ne_zero 2 (one_sub_ne_zero_of_mem_unitDisk hw))).mp heq
    have hfact : (z - w) * (1 - z * w) = 0 := by linear_combination hcross
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfact).resolve_right hzw)
  · have hden : HasDerivAt (fun z : ℂ ↦ (1 - z) ^ 2) (-2) 0 := by
      convert (((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hasDerivAt_id (0 : ℂ))).pow 2) using 1 <;>
        norm_num [Pi.pow_def, Pi.sub_def, id]
    have h := (hasDerivAt_id (0 : ℂ)).div hden (by norm_num)
    change deriv (fun z : ℂ ↦ z / (1 - z) ^ 2) 0 = 1
    exact h.deriv.trans (by norm_num)

lemma rotate_normalizedUnivalent {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {lam : ℂ} (hlam : ‖lam‖ = 1) : NormalizedUnivalent (rotate lam f) := by
  have hmap : Set.MapsTo (fun z : ℂ ↦ lam * z) unitDisk unitDisk := by
    intro z hz
    simpa only [mem_unitDisk, norm_mul, hlam, one_mul] using hz
  have hmul : conj lam * lam = 1 := conj_mul_self_of_norm_one hlam
  have hlam0 : lam ≠ 0 := by
    intro h
    simp [h] at hlam
  have hc0 : conj lam ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact zero_ne_one hmul
  refine ⟨?_, ?_, by simp [rotate, hf.map_zero], ?_⟩
  · have hlin : DifferentiableOn ℂ (fun z : ℂ ↦ lam * z) unitDisk := by fun_prop
    exact (hf.holomorphic.comp hlin hmap).const_mul (conj lam)
  · intro z hz w hw heq
    exact mul_left_cancel₀ hlam0 (hf.injective (hmap hz) (hmap hw) (mul_left_cancel₀ hc0 heq))
  · change deriv (fun z : ℂ ↦ conj lam * f (lam * z)) 0 = 1
    rw [deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul, mul_zero, hf.deriv_zero,
      mul_one, hmul]

private lemma iteratedDeriv_scale (n : ℕ) (lam : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    iteratedDeriv n (fun w ↦ f (lam * w)) z = lam ^ n * iteratedDeriv n f (lam * z) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    have hd : deriv (fun w ↦ f (lam * w)) = fun w ↦ lam * deriv f (lam * w) := by
      funext w
      simpa only [smul_eq_mul] using deriv_comp_mul_left lam f w
    rw [iteratedDeriv_succ', iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, ih, pow_succ]
    ring

/-- Rotation multiplies the `n`th coefficient by `lam ^ (n - 1)`. -/
theorem coeff_rotate (f : ℂ → ℂ) {lam : ℂ} (hlam : ‖lam‖ = 1) {n : ℕ} (hn : 1 ≤ n) :
    coeff (rotate lam f) n = lam ^ (n - 1) * coeff f n := by
  unfold coeff rotate
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_scale]
  rw [mul_zero, show lam ^ n = lam ^ (n - 1) * lam by rw [← pow_succ, Nat.sub_add_cancel hn]]
  calc
    _ = (conj lam * lam) * (lam ^ (n - 1) * ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0)) := by ring
    _ = _ := by rw [conj_mul_self_of_norm_one hlam, one_mul]

private lemma coeff_eq_of_hasFPowerSeriesOnBall {f : ℂ → ℂ} {a : ℕ → ℂ}
    {r : ENNReal} (h : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) 0 r)
    (n : ℕ) : coeff f n = a n := by
  rw [coeff, iteratedDeriv_eq_iteratedFDeriv, h.iteratedFDeriv_eq_sum_of_completeSpace]
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

private lemma hasFPowerSeriesOnBall_rotate_koebe {lam : ℂ} (hlam : ‖lam‖ = 1) :
    HasFPowerSeriesOnBall (rotate lam koebe)
      (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ conj lam * (n : ℂ) * lam ^ n)) 0
      ((1 / 2 : NNReal) : ENNReal) := by
  refine ⟨?_, by norm_num, ?_⟩
  · apply FormalMultilinearSeries.le_radius_of_summable
    simp only [FormalMultilinearSeries.ofScalars_norm, norm_mul, Complex.norm_conj,
      Complex.norm_natCast, norm_pow, hlam, one_mul, one_pow, mul_one, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat]
    exact summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ)) (by norm_num) |>.congr
      (fun n ↦ by rw [pow_one])
  · intro z hz
    have hz' : ‖z‖ < 1 := by
      rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right] at hz
      exact hz.trans (by norm_num)
    have h := hasSum_coe_mul_geometric_of_norm_lt_one
      (r := lam * z) (by simpa only [norm_mul, hlam, one_mul] using hz')
    simp only [zero_add, rotate, koebe, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul]
    convert h.mul_left (conj lam) using 1
    funext n
    rw [mul_pow]
    ring

/-- The coefficient of a Koebe rotation, for positive indices. -/
theorem coeff_rotate_koebe {lam : ℂ} (hlam : ‖lam‖ = 1) {n : ℕ} (hn : 1 ≤ n) :
    coeff (rotate lam koebe) n = (n : ℂ) * lam ^ (n - 1) := by
  rw [coeff_eq_of_hasFPowerSeriesOnBall (hasFPowerSeriesOnBall_rotate_koebe hlam),
    show lam ^ n = lam ^ (n - 1) * lam by rw [← pow_succ, Nat.sub_add_cancel hn]]
  calc
    conj lam * (n : ℂ) * (lam ^ (n - 1) * lam) = (conj lam * lam) * ((n : ℂ) * lam ^ (n - 1)) := by ring
    _ = _ := by rw [conj_mul_self_of_norm_one hlam, one_mul]

lemma coeff_congr_on_unitDisk {f g : ℂ → ℂ} (h : Set.EqOn f g unitDisk) (n : ℕ) :
    coeff f n = coeff g n := by
  have he : f =ᶠ[nhds 0] g := Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨unitDisk, Metric.isOpen_ball.mem_nhds zero_mem_unitDisk, h⟩
  rw [coeff, coeff, he.iteratedDeriv_eq]

/-- Coefficients of functions agreeing with a Koebe rotation on the disk. -/
lemma IsKoebeRotation.coefficients {f : ℂ → ℂ} (hf : IsKoebeRotation f) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ n : ℕ, 1 ≤ n → coeff f n = (n : ℂ) * lam ^ (n - 1) := by
  obtain ⟨lam, hlam, h⟩ := hf
  exact ⟨lam, hlam, fun n hn ↦ (coeff_congr_on_unitDisk h n).trans (coeff_rotate_koebe hlam hn)⟩

end Zalcman
