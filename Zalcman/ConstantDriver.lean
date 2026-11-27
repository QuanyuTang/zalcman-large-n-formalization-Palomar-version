/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.KoebeImage
public import Zalcman.LogarithmicCoefficients
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The radial transition for a constant unit driving phase

The Koebe rotation `z / (1 + κ z)^2` has nested positive dilates. Its inverse
gives an explicit holomorphic transition and both the spatial and time
derivatives needed to concatenate constant drivers.
-/

@[expose] public section

noncomputable section

namespace Zalcman

open Set
open scoped ComplexConjugate Topology

/-- The Koebe rotation associated to the constant direct-chain driver `κ`. -/
def driverKoebe (κ : ℂ) : ℂ → ℂ := rotate (-κ) koebe

private theorem conj_mul_unit {κ : ℂ} (hκ : ‖κ‖ = 1) : conj κ * κ = 1 := by
  rw [Complex.conj_mul', hκ]
  norm_num

/-- The rational formula for the Koebe rotation used by a constant driver. -/
theorem driverKoebe_apply {κ : ℂ} (hκ : ‖κ‖ = 1) (z : ℂ) :
    driverKoebe κ z = z / (1 + κ * z) ^ 2 := by
  unfold driverKoebe rotate koebe
  have hunit : conj (-κ) * (-κ) = 1 := conj_mul_unit (by simpa using hκ)
  rw [show 1 - (-κ) * z = 1 + κ * z by ring]
  calc
    _ = (conj (-κ) * (-κ)) * (z / (1 + κ * z) ^ 2) := by ring
    _ = _ := by rw [hunit, one_mul]

/-- The constant-driver Koebe function is normalized and univalent. -/
theorem normalizedUnivalent_driverKoebe {κ : ℂ} (hκ : ‖κ‖ = 1) :
    NormalizedUnivalent (driverKoebe κ) :=
  rotate_normalizedUnivalent koebe_normalizedUnivalent (by simpa using hκ)

private theorem one_add_mul_driver_ne_zero {κ z : ℂ} (hκ : ‖κ‖ = 1) (hz : z ∈ unitDisk) :
    1 + κ * z ≠ 0 := by
  have h : ‖κ * z‖ < 1 := by simpa only [norm_mul, hκ, one_mul] using mem_unitDisk.mp hz
  intro hzero
  have he : κ * z = -1 := by linear_combination hzero
  rw [he, norm_neg, norm_one] at h
  exact (lt_irrefl _ h)

/-- Spatial derivative of the Koebe map for the constant phase. -/
theorem hasDerivAt_driverKoebe {κ z : ℂ} (hκ : ‖κ‖ = 1) (hz : z ∈ unitDisk) :
    HasDerivAt (driverKoebe κ) ((1 - κ * z) / (1 + κ * z) ^ 3) z := by
  have h₀ := one_add_mul_driver_ne_zero hκ hz
  have hlin : HasDerivAt (fun w : ℂ => 1 + κ * w) κ z := by
    simpa only [id, mul_one] using ((hasDerivAt_id z).const_mul κ).const_add (1 : ℂ)
  have h := (hasDerivAt_id z).div (hlin.fun_pow 2) (pow_ne_zero 2 h₀)
  have he : driverKoebe κ = fun w : ℂ => w / (1 + κ * w) ^ 2 := funext (driverKoebe_apply hκ)
  rw [he]
  convert h using 1 <;> try rfl
  norm_num
  field_simp [h₀]; ring

private theorem driverKoebe_deriv_ne_zero {κ z : ℂ} (hκ : ‖κ‖ = 1) (hz : z ∈ unitDisk) :
    deriv (driverKoebe κ) z ≠ 0 := by
  rw [(hasDerivAt_driverKoebe hκ hz).deriv]
  apply div_ne_zero _ (pow_ne_zero 3 (one_add_mul_driver_ne_zero hκ hz))
  simpa only [neg_mul, ← sub_eq_add_neg] using one_add_mul_driver_ne_zero
    (κ := -κ) (by simpa only [norm_neg] using hκ) hz

private theorem driverKoebe_image {κ : ℂ} (hκ : ‖κ‖ = 1) :
    driverKoebe κ '' unitDisk = (fun w => conj (-κ) * w) '' (koebe '' unitDisk) := by
  let a := -κ
  have ha : ‖a‖ = 1 := by simp [a, hκ]
  have hmap (z : ℂ) (hz : z ∈ unitDisk) : a * z ∈ unitDisk := by
    simpa only [mem_unitDisk, norm_mul, ha, one_mul] using hz
  have hconj (z : ℂ) (hz : z ∈ unitDisk) : conj a * z ∈ unitDisk := by
    simpa only [mem_unitDisk, norm_mul, Complex.norm_conj, ha, one_mul] using hz
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨koebe (a * z), ⟨a * z, hmap z hz, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨conj a * z, hconj z hz, ?_⟩
    have he : a * (conj a * z) = z := by
      rw [← mul_assoc, mul_comm a, conj_mul_unit ha, one_mul]
    change conj a * koebe (a * (conj a * z)) = conj a * koebe z
    rw [he]

private theorem scaled_driverKoebe_mem_image {κ z : ℂ} (hκ : ‖κ‖ = 1) (hz : z ∈ unitDisk)
    {s : ℝ} (hs : 0 ≤ s) : (Real.exp (-s) : ℂ) * driverKoebe κ z ∈ driverKoebe κ '' unitDisk := by
  have hz' : driverKoebe κ z ∈ driverKoebe κ '' unitDisk := mem_image_of_mem _ hz
  rw [driverKoebe_image hκ] at hz' ⊢
  obtain ⟨w, hw, he⟩ := hz'
  refine ⟨(Real.exp (-s) : ℂ) * w, ?_, ?_⟩
  · have h := koebe_scaled_image_mono (Real.exp_pos (-s)) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs))
    obtain ⟨a, ha, hwa⟩ := hw
    have hw' := h (show (Real.exp (-s) : ℂ) * w ∈
        (fun z => (Real.exp (-s) : ℂ) * koebe z) '' unitDisk from
      ⟨a, ha, congrArg ((Real.exp (-s) : ℂ) * ·) hwa⟩)
    simpa only [Complex.ofReal_one, one_mul] using hw'
  · rw [← he]
    ring

/-- The inverse transition through time difference `s` for a constant driving phase. -/
def constantDriverTransition (κ : ℂ) (s : ℝ) (z : ℂ) : ℂ :=
  Function.invFunOn (driverKoebe κ) unitDisk ((Real.exp (-s) : ℂ) * driverKoebe κ z)

/-- The transition stays in the disk and rescales the Koebe coordinate. -/
theorem constantDriverTransition_spec {κ z : ℂ} (hκ : ‖κ‖ = 1) (hz : z ∈ unitDisk)
    {s : ℝ} (hs : 0 ≤ s) :
    constantDriverTransition κ s z ∈ unitDisk ∧
      driverKoebe κ (constantDriverTransition κ s z) = (Real.exp (-s) : ℂ) * driverKoebe κ z := by
  obtain ⟨w, hw, he⟩ := scaled_driverKoebe_mem_image hκ hz hs
  have hInv := (normalizedUnivalent_driverKoebe hκ).injective.leftInvOn_invFunOn hw
  have hval : constantDriverTransition κ s z = w := by
    unfold constantDriverTransition
    rw [← he, hInv]
  exact ⟨hval.symm ▸ hw, hval.symm ▸ he⟩

private theorem hasDerivAt_driverKoebe_inverse {κ w : ℂ} (hκ : ‖κ‖ = 1) (hw : w ∈ unitDisk) :
    HasDerivAt (Function.invFunOn (driverKoebe κ) unitDisk)
      (deriv (driverKoebe κ) w)⁻¹ (driverKoebe κ w) := by
  have hn := normalizedUnivalent_driverKoebe hκ
  have ha := hn.holomorphic.analyticOnNhd unitDisk_isOpen w hw
  have hd := (ha.contDiffAt (n := 1)).hasStrictDerivAt (by norm_num)
  refine (hd.to_local_left_inverse (driverKoebe_deriv_ne_zero hκ hw) ?_).hasDerivAt
  filter_upwards [unitDisk_isOpen.mem_nhds hw] with z hz
  exact hn.injective.leftInvOn_invFunOn hz

/-- The inverse transition is jointly continuous in elapsed time and in the disk variable. -/
theorem continuousOn_constantDriverTransition {κ : ℂ} (hκ : ‖κ‖ = 1) :
    ContinuousOn (fun p : ℝ × ℂ ↦ constantDriverTransition κ p.1 p.2)
      (Ici 0 ×ˢ unitDisk) := by
  have hcInv : ContinuousOn (Function.invFunOn (driverKoebe κ) unitDisk)
      (driverKoebe κ '' unitDisk) := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hasDerivAt_driverKoebe_inverse hκ hw).continuousAt.continuousWithinAt
  have hExp : Continuous (fun t : ℝ ↦ (Real.exp (-t) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)
  have hK : ContinuousOn (driverKoebe κ) unitDisk :=
    (normalizedUnivalent_driverKoebe hκ).holomorphic.continuousOn
  have hpair : ContinuousOn (fun p : ℝ × ℂ ↦ (Real.exp (-p.1) : ℂ) * driverKoebe κ p.2)
      (Ici 0 ×ˢ unitDisk) :=
    (hExp.comp continuous_fst).continuousOn.mul
      (hK.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2))
  exact hcInv.comp hpair (fun _ hp ↦ scaled_driverKoebe_mem_image hκ hp.2 hp.1)

/-- The spatial derivative of the constant-driver transition. -/
theorem hasDerivAt_constantDriverTransition {κ z : ℂ} (hκ : ‖κ‖ = 1) (hz : z ∈ unitDisk)
    {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (constantDriverTransition κ s)
      ((deriv (driverKoebe κ) (constantDriverTransition κ s z))⁻¹ *
        ((Real.exp (-s) : ℂ) * deriv (driverKoebe κ) z)) z := by
  have h := constantDriverTransition_spec hκ hz hs
  have hInv := hasDerivAt_driverKoebe_inverse hκ h.1
  rw [h.2] at hInv
  exact hInv.comp z (((hasDerivAt_driverKoebe hκ hz).deriv.symm ▸
    hasDerivAt_driverKoebe hκ hz).const_mul (Real.exp (-s) : ℂ))

/-- The derivative in elapsed real time has the negative inverse Löwner sign. -/
theorem hasDerivAt_constantDriverTransition_time {κ z : ℂ} (hκ : ‖κ‖ = 1) (hz : z ∈ unitDisk)
    {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun t => constantDriverTransition κ t z)
      (-(driverKoebe κ (constantDriverTransition κ s z) /
        deriv (driverKoebe κ) (constantDriverTransition κ s z))) s := by
  let w := constantDriverTransition κ s z
  have h := constantDriverTransition_spec hκ hz hs
  have hInv := hasDerivAt_driverKoebe_inverse hκ h.1
  rw [h.2] at hInv
  have hm := (hasDerivAt_id (Real.exp (-s) : ℂ)).mul_const (driverKoebe κ z)
  have hcomp := (hInv.comp (Real.exp (-s) : ℂ) hm).comp_ofReal.scomp s ((hasDerivAt_id s).neg.exp)
  convert hcomp using 1 <;> try rfl
  rw [show driverKoebe κ w = (Real.exp (-s) : ℂ) * driverKoebe κ z from h.2]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one,
    Pi.neg_apply, id, one_mul]
  ring

/-- Constant-driver transitions compose additively in elapsed time. -/
theorem constantDriverTransition_add {κ z : ℂ} (hκ : ‖κ‖ = 1) (hz : z ∈ unitDisk)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    constantDriverTransition κ (s + t) z = constantDriverTransition κ s (constantDriverTransition κ t z) := by
  have hst := constantDriverTransition_spec hκ hz (add_nonneg hs ht)
  have ht' := constantDriverTransition_spec hκ hz ht
  have hs' := constantDriverTransition_spec hκ ht'.1 hs
  apply (normalizedUnivalent_driverKoebe hκ).injective hst.1 hs'.1
  rw [hst.2, hs'.2, ht'.2, neg_add, Real.exp_add, Complex.ofReal_mul, mul_assoc]

/-- The transition at zero elapsed time is the identity on the disk. -/
theorem constantDriverTransition_zero {κ z : ℂ} (hκ : ‖κ‖ = 1) (hz : z ∈ unitDisk) :
    constantDriverTransition κ 0 z = z := by
  simpa only [constantDriverTransition, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul] using
    (normalizedUnivalent_driverKoebe hκ).injective.leftInvOn_invFunOn hz

/-- Every positive-time transition is injective on the disk and has the stated normalization. -/
theorem constantDriverTransition_normalization {κ : ℂ} (hκ : ‖κ‖ = 1) {s : ℝ} (hs : 0 ≤ s) :
    DifferentiableOn ℂ (constantDriverTransition κ s) unitDisk ∧
    InjOn (constantDriverTransition κ s) unitDisk ∧
    MapsTo (constantDriverTransition κ s) unitDisk unitDisk ∧
    constantDriverTransition κ s 0 = 0 ∧
    deriv (constantDriverTransition κ s) 0 = (Real.exp (-s) : ℂ) := by
  have hk := normalizedUnivalent_driverKoebe hκ
  have h₀ := constantDriverTransition_spec hκ zero_mem_unitDisk hs
  have hzero : constantDriverTransition κ s 0 = 0 := by
    apply hk.injective h₀.1 zero_mem_unitDisk
    rw [h₀.2, hk.map_zero, mul_zero]
  refine ⟨(fun z hz => (hasDerivAt_constantDriverTransition hκ hz hs).differentiableAt.differentiableWithinAt),
    ?_, (fun z hz => (constantDriverTransition_spec hκ hz hs).1), hzero, ?_⟩
  · intro z hz w hw he
    have h := congrArg (driverKoebe κ) he
    rw [(constantDriverTransition_spec hκ hz hs).2, (constantDriverTransition_spec hκ hw hs).2] at h
    exact hk.injective hz hw (mul_left_cancel₀ (by exact_mod_cast Real.exp_ne_zero (-s)) h)
  · rw [(hasDerivAt_constantDriverTransition hκ zero_mem_unitDisk hs).deriv, hzero, hk.deriv_zero,
      inv_one, mul_one, one_mul]

/-- The Loewner equation with constant driver for one backwards-composed interval. -/
theorem hasDerivAt_constantDriverPiece {κ z : ℂ} (hκ : ‖κ‖ = 1) (hz : z ∈ unitDisk)
    {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H unitDisk) {u b : ℝ} (hub : u ≤ b) :
    HasDerivAt (fun t => H (constantDriverTransition κ (b - t) z))
      (z * ((1 + κ * z) / (1 - κ * z)) *
        deriv (fun w => H (constantDriverTransition κ (b - u) w)) z) u := by
  let s := b - u
  let w := constantDriverTransition κ s z
  have hs : 0 ≤ s := sub_nonneg.mpr hub
  have hw := constantDriverTransition_spec hκ hz hs
  have hHc := (hH.differentiableAt (unitDisk_isOpen.mem_nhds hw.1)).hasDerivAt
  have hSpace := hHc.comp z (hasDerivAt_constantDriverTransition hκ hz hs)
  have hSpatial : deriv (fun v => H (constantDriverTransition κ (b - u) v)) z =
      deriv H w * ((deriv (driverKoebe κ) w)⁻¹ *
        ((Real.exp (-s) : ℂ) * deriv (driverKoebe κ) z)) := hSpace.deriv
  have hφt := (hasDerivAt_constantDriverTransition_time hκ hz hs).scomp u
    ((hasDerivAt_id u).const_sub b)
  have hφ : HasDerivAt (fun t => constantDriverTransition κ (b - t) z)
      (driverKoebe κ w / deriv (driverKoebe κ) w) u := by
    simpa only [Function.comp_def, id, zero_sub, neg_smul, one_smul, neg_neg, w, s] using hφt
  have h := (hHc.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt u hφ
  have hRatio : z * ((1 + κ * z) / (1 - κ * z)) = driverKoebe κ z / deriv (driverKoebe κ) z := by
    have h₁ := one_add_mul_driver_ne_zero hκ hz
    have h₂ : 1 - κ * z ≠ 0 := by
      simpa only [neg_mul, ← sub_eq_add_neg] using one_add_mul_driver_ne_zero
        (κ := -κ) (by simpa only [norm_neg] using hκ) hz
    rw [driverKoebe_apply hκ, (hasDerivAt_driverKoebe hκ hz).deriv]
    field_simp [h₁, h₂]
  rw [hRatio, hSpatial]
  convert h using 1 <;> try rfl
  change (driverKoebe κ z / deriv (driverKoebe κ) z) *
      (deriv H w * ((deriv (driverKoebe κ) w)⁻¹ *
        ((Real.exp (-s) : ℂ) * deriv (driverKoebe κ) z))) =
      (driverKoebe κ w / deriv (driverKoebe κ) w) * deriv H w
  rw [show driverKoebe κ w = (Real.exp (-s) : ℂ) * driverKoebe κ z from hw.2]
  field_simp [driverKoebe_deriv_ne_zero hκ hz, driverKoebe_deriv_ne_zero hκ hw.1]

/-- The time derivative on a constant-driver interval is jointly continuous. -/
theorem continuousOn_constantDriverPiece_time_deriv {κ : ℂ} (hκ : ‖κ‖ = 1)
    {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H unitDisk) (b : ℝ) :
    ContinuousOn
      (fun p : ℝ × ℂ ↦ p.2 * ((1 + κ * p.2) / (1 - κ * p.2)) *
        deriv (fun z ↦ H (constantDriverTransition κ (b - p.1) z)) p.2)
      (Iic b ×ˢ unitDisk) := by
  let A := Iic b ×ˢ unitDisk
  let W (p : ℝ × ℂ) := constantDriverTransition κ (b - p.1) p.2
  have hmap : MapsTo (fun p : ℝ × ℂ ↦ (b - p.1, p.2)) A (Ici 0 ×ˢ unitDisk) := by
    intro p hp
    exact ⟨sub_nonneg.mpr hp.1, hp.2⟩
  have hW : ContinuousOn W A :=
    (continuousOn_constantDriverTransition hκ).comp
      (((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn) hmap
  have hWD : MapsTo W A unitDisk := fun _ hp ↦
    (constantDriverTransition_spec hκ hp.2 (sub_nonneg.mpr hp.1)).1
  have hH' : ContinuousOn (deriv H) unitDisk :=
    ((hH.analyticOnNhd unitDisk_isOpen).deriv).continuousOn
  have hK' : ContinuousOn (deriv (driverKoebe κ)) unitDisk :=
    (((normalizedUnivalent_driverKoebe hκ).holomorphic.analyticOnNhd unitDisk_isOpen).deriv).continuousOn
  have hE : Continuous (fun p : ℝ × ℂ ↦ (Real.exp (-(b - p.1)) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp ((continuous_const.sub continuous_fst).neg))
  have hSpatial : ContinuousOn
      (fun p : ℝ × ℂ ↦ deriv (fun z ↦ H (constantDriverTransition κ (b - p.1) z)) p.2) A := by
    apply ((hH'.comp hW hWD).mul
      (((hK'.comp hW hWD).inv₀ (fun p hp ↦ driverKoebe_deriv_ne_zero hκ (hWD hp))).mul
        (hE.continuousOn.mul (hK'.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2))))).congr
    intro p hp
    have hφ := hasDerivAt_constantDriverTransition hκ hp.2 (sub_nonneg.mpr hp.1)
    have hd := (hH.differentiableAt (unitDisk_isOpen.mem_nhds (hWD hp))).hasDerivAt
    exact (hd.comp p.2 hφ).deriv
  have hnum : Continuous (fun p : ℝ × ℂ ↦ 1 + κ * p.2) :=
    continuous_const.add (continuous_const.mul continuous_snd)
  have hden : Continuous (fun p : ℝ × ℂ ↦ 1 - κ * p.2) :=
    continuous_const.sub (continuous_const.mul continuous_snd)
  have hnz (p : ℝ × ℂ) (hp : p ∈ A) : 1 - κ * p.2 ≠ 0 := by
    simpa only [neg_mul, ← sub_eq_add_neg] using one_add_mul_driver_ne_zero
      (κ := -κ) (by simpa only [norm_neg] using hκ) hp.2
  exact (continuous_snd.continuousOn.mul
    (hnum.continuousOn.div hden.continuousOn hnz)).mul hSpatial

end Zalcman
