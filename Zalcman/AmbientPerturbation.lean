/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Data.Set.Piecewise
public import Mathlib.Tactic.Abel
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Tactic.NormNum

/-!
# Extending a small deformation to the plane

A displacement supported away from the edge of an open set extends by zero.
If its derivative is small in the image coordinates of a holomorphic map,
adding it to the identity defines an ambient homeomorphism.
-/

@[expose] public section

namespace Zalcman

open Set Filter
open scoped Topology NNReal

/-- Adding a perturbation with Lipschitz constant smaller than one is a homeomorphism. -/
theorem exists_homeomorph_add_lipschitz {d : ℂ → ℂ} {c : ℝ≥0}
    (hl : LipschitzWith c d) (hc : c < 1) :
    ∃ e : ℂ ≃ₜ ℂ, ∀ x, e x = x + d x := by
  let e₀ := ContinuousLinearEquiv.refl ℝ ℂ
  let F := fun x : ℂ ↦ x + d x
  have happrox : ApproximatesLinearOn F (e₀ : ℂ →L[ℝ] ℂ) univ c := by
    intro x _ y _
    have heq : F x - F y - (e₀ : ℂ →L[ℝ] ℂ) (x - y) = d x - d y := by
      change x + d x - (y + d y) - (x - y) = d x - d y
      abel
    rw [heq, ← dist_eq_norm, ← dist_eq_norm]
    exact hl.dist_le_mul x y
  have hn : ‖(e₀.symm : ℂ →L[ℝ] ℂ)‖₊ = 1 :=
    by simpa only [e₀, ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl] using
      (ContinuousLinearMap.nnnorm_id (𝕜 := ℝ) (E := ℂ))
  have hsmall : c < ‖(e₀.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by simpa only [hn, inv_one] using hc
  exact ⟨happrox.toHomeomorph F (Or.inr hsmall), fun _ ↦ rfl⟩

/-- A differentiable displacement supported in a closed subset of its domain admits
an extension by the identity when its derivative norm is uniformly small. -/
theorem exists_homeomorph_of_supported_displacement {U K : Set ℂ} {d : ℂ → ℂ} {c : ℝ≥0}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) (hc : c < 1)
    (hd : DifferentiableOn ℝ d U) (hzero : ∀ x ∈ U \ K, d x = 0)
    (hbound : ∀ x ∈ U, ‖fderiv ℝ d x‖₊ ≤ c) :
    ∃ e : ℂ ≃ₜ ℂ, (∀ x ∈ U, e x = x + d x) ∧ EqOn e id Kᶜ := by
  classical
  let g := U.piecewise d (0 : ℂ → ℂ)
  have hgU {x : ℂ} (hx : x ∈ U) : g =ᶠ[𝓝 x] d := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact piecewise_eq_of_mem _ _ _ hy
  have hgzero {x : ℂ} (hx : x ∈ Kᶜ) : g x = 0 := by
    by_cases hxU : x ∈ U
    · exact (piecewise_eq_of_mem _ _ _ hxU).trans (hzero x ⟨hxU, hx⟩)
    · exact piecewise_eq_of_notMem _ _ _ hxU
  have hgK {x : ℂ} (hx : x ∈ Kᶜ) : g =ᶠ[𝓝 x] (0 : ℂ → ℂ) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact hgzero hy
  have hgd : Differentiable ℝ g := by
    intro x
    by_cases hx : x ∈ U
    · exact (hd.differentiableAt (hU.mem_nhds hx)).congr_of_eventuallyEq (hgU hx)
    · exact (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq (hgK (fun hk ↦ hx (hKU hk)))
  have hgb (x : ℂ) : ‖fderiv ℝ g x‖₊ ≤ c := by
    by_cases hx : x ∈ U
    · rw [(hgU hx).fderiv_eq]
      exact hbound x hx
    · rw [(hgK (fun hk ↦ hx (hKU hk))).fderiv_eq, fderiv_zero, Pi.zero_apply, nnnorm_zero]
      exact zero_le
  obtain ⟨e, he⟩ := exists_homeomorph_add_lipschitz (lipschitzWith_of_nnnorm_fderiv_le hgd hgb) hc
  refine ⟨e, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [he x, show g x = d x from piecewise_eq_of_mem _ _ _ hx]
  · rw [he x, hgzero hx, add_zero, id_eq]

/-- A small source-coordinate displacement can be transported through a holomorphic
embedding and extended to an ambient homeomorphism. The closed support is carried to
the image of `K`. -/
theorem exists_homeomorph_of_holomorphic_displacement {U K : Set ℂ} {f d : ℂ → ℂ} {c : ℝ≥0}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hc : c < 1)
    (hf : DifferentiableOn ℂ f U) (hfi : InjOn f U) (hfn : ∀ z ∈ U, deriv f z ≠ 0)
    (hd : DifferentiableOn ℝ d U) (hzero : ∀ z ∈ U \ K, d z = 0)
    (hsmall : ∀ z ∈ U, ‖fderiv ℝ d z‖ ≤ (c : ℝ) * ‖deriv f z‖) :
    ∃ e : ℂ ≃ₜ ℂ, (∀ z ∈ U, e (f z) = f z + d z) ∧ EqOn e id (f '' K)ᶜ := by
  let g := Function.invFunOn f U
  have hleft {z : ℂ} (hz : z ∈ U) : g (f z) = z := hfi.leftInvOn_invFunOn hz
  have hstrict {z : ℂ} (hz : z ∈ U) : HasStrictDerivAt f (deriv f z) z :=
    ((hf.analyticOnNhd hU z hz).contDiffAt (n := 1)).hasStrictDerivAt (by norm_num)
  have hOI : IsOpen (f '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z, hz, rfl⟩
    rw [← (hstrict hz).map_nhds_eq (hfn z hz)]
    exact image_mem_map (hU.mem_nhds hz)
  have hKI := (hK.image_of_continuousOn (hf.continuousOn.mono hKU)).isClosed
  have hInv {z : ℂ} (hz : z ∈ U) : HasDerivAt g (deriv f z)⁻¹ (f z) := by
    refine ((hstrict hz).to_local_left_inverse (hfn z hz) ?_).hasDerivAt
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hleft hw
  have hD (z : ℂ) (hz : z ∈ U) : HasFDerivAt (d ∘ g)
      ((fderiv ℝ d z).comp ((ContinuousLinearMap.toSpanSingleton ℂ
        ((deriv f z)⁻¹)).restrictScalars ℝ)) (f z) := by
    have hdz : HasFDerivAt d (fderiv ℝ d z) (g (f z)) := by
      rw [hleft hz]
      exact (hd.differentiableAt (hU.mem_nhds hz)).hasFDerivAt
    exact hdz.comp (f z) ((hInv hz).hasFDerivAt.restrictScalars ℝ)
  have hdg : DifferentiableOn ℝ (d ∘ g) (f '' U) := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hD z hz).differentiableAt.differentiableWithinAt
  have hzero' (w : ℂ) (hw : w ∈ (f '' U) \ (f '' K)) : (d ∘ g) w = 0 := by
    obtain ⟨z, hz, rfl⟩ := hw.1
    rw [Function.comp_apply, hleft hz]
    exact hzero z ⟨hz, fun hzK ↦ hw.2 ⟨z, hzK, rfl⟩⟩
  have hbound (w : ℂ) (hw : w ∈ f '' U) : ‖fderiv ℝ (d ∘ g) w‖₊ ≤ c := by
    obtain ⟨z, hz, rfl⟩ := hw
    let A := (ContinuousLinearMap.toSpanSingleton ℂ ((deriv f z)⁻¹)).restrictScalars ℝ
    have hder : fderiv ℝ (d ∘ g) (f z) = (fderiv ℝ d z).comp A := (hD z hz).fderiv
    rw [hder, ← NNReal.coe_le_coe]
    change ‖(fderiv ℝ d z).comp A‖ ≤ (c : ℝ)
    calc
      _ ≤ ‖fderiv ℝ d z‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ((c : ℝ) * ‖deriv f z‖) * ‖A‖ := mul_le_mul_of_nonneg_right (hsmall z hz) (norm_nonneg _)
      _ = _ := by
        dsimp only [A]
        rw [ContinuousLinearMap.norm_restrictScalars, ContinuousLinearMap.norm_toSpanSingleton,
          norm_inv, mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hfn z hz)), mul_one]
  obtain ⟨e, he, heOut⟩ := exists_homeomorph_of_supported_displacement hOI hKI (image_mono hKU) hc
    hdg hzero' hbound
  refine ⟨e, fun z hz ↦ ?_, heOut⟩
  rw [he (f z) ⟨z, hz, rfl⟩, Function.comp_apply, hleft hz]

end Zalcman
