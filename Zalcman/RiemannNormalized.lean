/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Basic
public import Zalcman.Upstream.Brennan.Distortion
public import Zalcman.Upstream.Crouzeix.RiemannProper
public import Mathlib.Analysis.Calculus.Deriv.CompMul

@[expose] public section

/-!
# Normalizing conformal maps from the disk

Invert the Riemann map and rotate the disk so that the derivative at the
origin is a positive real number. This derivative is the conformal radius.
-/

namespace Zalcman

open scoped Topology

/-- A normalized conformal map from the disk onto a proper simply connected plane domain. -/
theorem exists_disk_map_with_positive_derivative {U : Set ℂ} (hU : IsOpen U)
    (hproper : U ≠ Set.univ) (hc : IsSimplyConnected U) {a : ℂ} (ha : a ∈ U) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F unitDisk ∧ Set.BijOn F unitDisk U ∧
      F 0 = a ∧ ∃ r : ℝ, 0 < r ∧ deriv F 0 = (r : ℂ) := by
  obtain ⟨f, hf, hfder, hbij⟩ :=
    OAI.CrouzeixHilbert.Conformal.riemann_mapping_proper hU hproper hc ha
  have hbij' : Set.BijOn f U unitDisk := hbij
  let g := Function.invFunOn f U
  have hgInv (z : ℂ) (hz : z ∈ U) : g (f z) = z :=
    hf.injective.leftInvOn_invFunOn hz
  have hg₀ : g 0 = a := by simpa only [hf.normalized] using hgInv a ha
  have hgAt (z : ℂ) (hz : z ∈ U) : HasDerivAt g (deriv f z)⁻¹ (f z) := by
    have hA := hf.holomorphic.analyticOnNhd hU z hz
    have hd := (hA.contDiffAt (n := 1)).hasStrictDerivAt (by norm_num)
    have hn := OAI.Brennan.univalent_deriv_ne_zero hU ⟨hf.holomorphic, hf.injective⟩ hz
    refine (hd.to_local_left_inverse hn ?_).hasDerivAt
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hgInv w hw
  have hgD : DifferentiableOn ℂ g unitDisk := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hbij'.surjOn hw
    exact (hgAt z hz).differentiableAt.differentiableWithinAt
  have hfg (w : ℂ) (hw : w ∈ unitDisk) : f (g w) = w := by
    obtain ⟨z, hz, rfl⟩ := hbij'.surjOn hw
    rw [hgInv z hz]
  have hgBij : Set.BijOn g unitDisk U := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨z, hz, rfl⟩ := hbij'.surjOn hw
      rwa [hgInv z hz]
    · intro z hz w hw he
      rw [← hfg z hz, ← hfg w hw, he]
    · intro z hz
      exact ⟨f z, hbij'.mapsTo hz, hgInv z hz⟩
  let d := deriv g 0
  have hd' : d = (deriv f a)⁻¹ := by simpa only [d, hf.normalized] using (hgAt a ha).deriv
  have hd0 : d ≠ 0 := by rw [hd']; exact inv_ne_zero hfder
  let r := ‖d‖
  have hr : 0 < r := norm_pos_iff.mpr hd0
  let c : ℂ := (r : ℂ) / d
  have hc₁ : ‖c‖ = 1 := by
    dsimp only [c, r]
    rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (norm_pos_iff.mpr hd0).ne']
  have hc₀ : c ≠ 0 := by
    intro hz
    simp [hz] at hc₁
  have hc_map : Set.MapsTo (fun z : ℂ ↦ c * z) unitDisk unitDisk := by
    intro z hz
    rwa [mem_unitDisk, norm_mul, hc₁, one_mul, ← mem_unitDisk]
  have hcBij : Set.BijOn (fun z : ℂ ↦ c * z) unitDisk unitDisk := by
    refine ⟨hc_map, fun z _ w _ he ↦ mul_left_cancel₀ hc₀ he, ?_⟩
    intro z hz
    refine ⟨z / c, ?_, ?_⟩
    · rw [mem_unitDisk, norm_div, hc₁, div_one]
      exact mem_unitDisk.mp hz
    · change c * (z / c) = z
      rw [mul_comm, div_mul_cancel₀ _ hc₀]
  have hscale : DifferentiableOn ℂ (fun z : ℂ ↦ c * z) unitDisk := by fun_prop
  refine ⟨fun z ↦ g (c * z), hgD.comp hscale hc_map, hgBij.comp hcBij,
    by simpa only [mul_zero] using hg₀, r, hr, ?_⟩
  rw [deriv_comp_mul_left, smul_eq_mul, mul_zero]
  change c * d = (r : ℂ)
  exact div_mul_cancel₀ _ hd0

end Zalcman
