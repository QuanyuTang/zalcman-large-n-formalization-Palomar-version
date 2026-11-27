/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Basic
public import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The normalized logarithm and square root of a schlicht function divided by `z`

The desingularized function `dslope f 0` is holomorphic and nonzero on the unit disk.
Integrating its logarithmic derivative gives a distinguished holomorphic logarithm.
-/

@[expose] public section

namespace Zalcman

lemma unitDisk_isOpen : IsOpen unitDisk := Metric.isOpen_ball

lemma unitDisk_isPreconnected : IsPreconnected unitDisk := (convex_ball (0 : ℂ) 1).isPreconnected

lemma NormalizedUnivalent.mul_dslope {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (z : ℂ) :
    z * dslope f 0 z = f z := by
  simpa only [sub_zero, smul_eq_mul, hf.map_zero] using sub_smul_dslope f (0 : ℂ) z

lemma NormalizedUnivalent.dslope_holomorphic {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    DifferentiableOn ℂ (dslope f 0) unitDisk :=
  (Complex.differentiableOn_dslope (unitDisk_isOpen.mem_nhds zero_mem_unitDisk)).mpr hf.holomorphic

lemma NormalizedUnivalent.dslope_ne_zero {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {z : ℂ} (hz : z ∈ unitDisk) : dslope f 0 z ≠ 0 := by
  by_cases h : z = 0
  · simp [h, dslope_same, hf.deriv_zero]
  · intro hd
    have hz0 : f z = f 0 := by rw [← hf.mul_dslope z, hd, mul_zero, hf.map_zero]
    exact h (hf.injective hz zero_mem_unitDisk hz0)

/-- The normalized logarithmic derivative of `f(z) / z` has a primitive on the disk. -/
lemma exists_normalized_logarithm {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    ∃ G : ℂ → ℂ, G 0 = 0 ∧ ∀ z ∈ unitDisk,
      HasDerivAt G (deriv (dslope f 0) z / dslope f 0 z) z := by
  have hp := hf.dslope_holomorphic
  have hd : DifferentiableOn ℂ (fun z ↦ deriv (dslope f 0) z / dslope f 0 z) unitDisk :=
    (hp.deriv unitDisk_isOpen).div hp (fun _ hz ↦ hf.dslope_ne_zero hz)
  exact hd.isExactOn_ball.with_val_at 0 0

/-- The holomorphic logarithm of `f(z) / z`, normalized to vanish at zero. -/
noncomputable def normalizedLogarithm {f : ℂ → ℂ} (hf : NormalizedUnivalent f) : ℂ → ℂ :=
  (exists_normalized_logarithm hf).choose

@[simp] lemma normalizedLogarithm_zero {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    normalizedLogarithm hf 0 = 0 := (exists_normalized_logarithm hf).choose_spec.1

lemma hasDerivAt_normalizedLogarithm {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {z : ℂ} (hz : z ∈ unitDisk) :
    HasDerivAt (normalizedLogarithm hf) (deriv (dslope f 0) z / dslope f 0 z) z :=
  (exists_normalized_logarithm hf).choose_spec.2 z hz

lemma normalizedLogarithm_holomorphic {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    DifferentiableOn ℂ (normalizedLogarithm hf) unitDisk :=
  fun _ hz ↦ (hasDerivAt_normalizedLogarithm hf hz).differentiableAt.differentiableWithinAt

theorem exp_normalizedLogarithm {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {z : ℂ} (hz : z ∈ unitDisk) : Complex.exp (normalizedLogarithm hf z) = dslope f 0 z := by
  let q := fun w ↦ Complex.exp (normalizedLogarithm hf w) / dslope f 0 w
  have hq (w : ℂ) (hw : w ∈ unitDisk) : HasDerivAt q 0 w := by
    have hG := (hasDerivAt_normalizedLogarithm hf hw).cexp
    have hp := (hf.dslope_holomorphic.differentiableAt (unitDisk_isOpen.mem_nhds hw)).hasDerivAt
    have hp0 := hf.dslope_ne_zero hw
    convert hG.div hp hp0 using 1
    field_simp
    ring
  have heq : Set.EqOn q (fun _ ↦ 1) unitDisk :=
    unitDisk_isOpen.eqOn_of_deriv_eq unitDisk_isPreconnected
      (fun w hw ↦ (hq w hw).differentiableAt.differentiableWithinAt) (differentiableOn_const 1)
      (fun w hw ↦ by rw [(hq w hw).deriv, deriv_const]) zero_mem_unitDisk
      (by simp [q, dslope_same, hf.deriv_zero])
  exact (div_eq_one_iff_eq (hf.dslope_ne_zero hz)).mp (heq hz)

/-- The normalized square root of `f(z) / z` on the unit disk. -/
noncomputable def squareRoot {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (z : ℂ) : ℂ :=
  Complex.exp (normalizedLogarithm hf z / 2)

@[simp] lemma squareRoot_zero {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    squareRoot hf 0 = 1 := by simp [squareRoot]

lemma squareRoot_holomorphic {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    DifferentiableOn ℂ (squareRoot hf) unitDisk :=
  ((normalizedLogarithm_holomorphic hf).div_const 2).cexp

lemma squareRoot_sq {f : ℂ → ℂ} (hf : NormalizedUnivalent f) {z : ℂ} (hz : z ∈ unitDisk) :
    squareRoot hf z ^ 2 = dslope f 0 z := by
  rw [squareRoot, ← Complex.exp_nat_mul]
  convert exp_normalizedLogarithm hf hz using 2
  push_cast
  ring

theorem mul_squareRoot_sq {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {z : ℂ} (hz : z ∈ unitDisk) : z * squareRoot hf z ^ 2 = f z := by
  rw [squareRoot_sq hf hz, hf.mul_dslope]

/-- The coefficient `c_n` of the normalized square-root series. -/
noncomputable def rootCoeff {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ) : ℂ :=
  coeff (squareRoot hf) n

/-- The logarithmic coefficient `t_n` with the normalization `log C = ∑ (t_n / n) z^n`. -/
noncomputable def logCoeff {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ) : ℂ :=
  (n : ℂ) * coeff (fun z ↦ normalizedLogarithm hf z / 2) n

@[simp] lemma rootCoeff_zero {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    rootCoeff hf 0 = 1 := by simp [rootCoeff]

@[simp] lemma logCoeff_zero {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    logCoeff hf 0 = 0 := by simp [logCoeff]

open scoped BigOperators Topology

lemma coeff_mul {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisk)
    (hg : DifferentiableOn ℂ g unitDisk) (n : ℕ) :
    coeff (fun z ↦ f z * g z) n =
      ∑ i ∈ Finset.range (n + 1), coeff f i * coeff g (n - i) := by
  have hnhds := unitDisk_isOpen.mem_nhds zero_mem_unitDisk
  have hf' : ContDiffAt ℂ n f 0 := (hf.contDiffOn unitDisk_isOpen).contDiffAt hnhds
  have hg' : ContDiffAt ℂ n g 0 := (hg.contDiffOn unitDisk_isOpen).contDiffAt hnhds
  rw [coeff, show (fun z ↦ f z * g z) = f * g by rfl, iteratedDeriv_mul hf' hg', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hfac : (n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) =
      (n.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  have hinv (j : ℕ) : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  simp only [coeff]
  field_simp [hinv]
  linear_combination iteratedDeriv i f 0 * iteratedDeriv (n - i) g 0 * hfac

lemma coeff_deriv (f : ℂ → ℂ) (n : ℕ) : coeff (deriv f) n = (n + 1 : ℂ) * coeff f (n + 1) := by
  rw [coeff, coeff, ← iteratedDeriv_succ', Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have h₁ : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h₂ : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  field_simp

private lemma coeff_id_eq (n : ℕ) : coeff (fun z : ℂ ↦ z) n = if n = 1 then 1 else 0 := by
  by_cases hn : n = 1
  · simp [hn]
  · simp [coeff, iteratedDeriv_fun_id_zero, hn]

private lemma coeff_mul_id_succ {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisk) (n : ℕ) :
    coeff (fun z ↦ z * f z) (n + 1) = coeff f n := by
  have hid : DifferentiableOn ℂ (fun z : ℂ ↦ z) unitDisk := differentiableOn_id
  rw [coeff_mul hid hf]
  simp only [coeff_id_eq]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

/-- The coefficient identity obtained from `f(z) = z * C(z)^2`. -/
theorem coeff_succ_eq_sum_rootCoeff {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ) :
    coeff f (n + 1) = ∑ i ∈ Finset.range (n + 1), rootCoeff hf i * rootCoeff hf (n - i) := by
  have heq : Set.EqOn f (fun z ↦ z * (squareRoot hf z * squareRoot hf z)) unitDisk :=
    fun z hz ↦ by simpa only [pow_two] using (mul_squareRoot_sq hf hz).symm
  have hprod : DifferentiableOn ℂ (fun z ↦ squareRoot hf z * squareRoot hf z) unitDisk :=
    (squareRoot_holomorphic hf).fun_mul (squareRoot_holomorphic hf)
  rw [coeff_congr_on_unitDisk heq, coeff_mul_id_succ hprod,
    coeff_mul (squareRoot_holomorphic hf) (squareRoot_holomorphic hf)]
  rfl

/-- The coefficient identity obtained by differentiating `C = exp (G / 2)`. -/
theorem rootCoeff_succ_eq_sum_logCoeff {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ) :
    (n + 1 : ℂ) * rootCoeff hf (n + 1) =
      ∑ i ∈ Finset.range (n + 1), logCoeff hf (n + 1 - i) * rootCoeff hf i := by
  let g := fun z ↦ normalizedLogarithm hf z / 2
  have hg : DifferentiableOn ℂ g unitDisk := (normalizedLogarithm_holomorphic hf).div_const 2
  have heq : Set.EqOn (deriv (squareRoot hf)) (fun z ↦ squareRoot hf z * deriv g z) unitDisk := by
    intro z hz
    have hd := (hg.differentiableAt (unitDisk_isOpen.mem_nhds hz)).hasDerivAt.cexp
    change deriv (fun z ↦ Complex.exp (g z)) z = Complex.exp (g z) * deriv g z
    exact hd.deriv
  change (n + 1 : ℂ) * coeff (squareRoot hf) (n + 1) = _
  rw [← coeff_deriv, coeff_congr_on_unitDisk heq, coeff_mul (squareRoot_holomorphic hf)
    (hg.deriv unitDisk_isOpen)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hidx : n - i + 1 = n + 1 - i := by
    have := Finset.mem_range.mp hi
    omega
  simp only [coeff_deriv, ← Nat.cast_succ, Nat.succ_eq_add_one, hidx, logCoeff, rootCoeff, g,
    mul_comm]

lemma rootCoeff_one_eq_logCoeff_one {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    rootCoeff hf 1 = logCoeff hf 1 := by
  simpa using rootCoeff_succ_eq_sum_logCoeff hf 0

lemma coeff_two_eq_two_mul_logCoeff_one {f : ℂ → ℂ} (hf : NormalizedUnivalent f) :
    coeff f 2 = 2 * logCoeff hf 1 := by
  have h := coeff_succ_eq_sum_rootCoeff hf 1
  simpa [Finset.sum_range_succ, rootCoeff_one_eq_logCoeff_one hf, two_mul] using h

end Zalcman
