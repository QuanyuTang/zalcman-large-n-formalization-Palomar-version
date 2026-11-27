/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.LoewnerLogODE
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Tactic.Ring

/-!
# Time slopes under exponential normalization

Scaling a direct radial chain by its conformal radius gives the normalized
map velocity and the corresponding Taylor coefficient equations.
-/

public section

namespace Zalcman

open Filter Set
open scoped BigOperators Topology Uniformity

private theorem fixed_locallyUniform {ι : Type*} {l : Filter ι} (f : ℂ → ℂ) :
    TendstoLocallyUniformlyOn (fun _ : ι ↦ f) f l unitDisk := by
  intro v hv x hx
  exact ⟨unitDisk, self_mem_nhdsWithin, Eventually.of_forall fun _ _ _ ↦ refl_mem_uniformity hv⟩

private theorem scalar_locallyUniform {a : ℝ → ℂ} {A : ℂ} {l : Filter ℝ}
    (h : Tendsto a l (𝓝 A)) :
    TendstoLocallyUniformlyOn (fun t (_ : ℂ) ↦ a t) (fun _ ↦ A) l unitDisk :=
  (tendstoLocallyUniformlyOn_iff_forall_isCompact unitDisk_isOpen).mpr
    fun K _ _ ↦ h.tendstoUniformlyOn_const K

theorem hasDerivAt_exp_neg_ofReal (u : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (Real.exp (-t) : ℂ)) (-(Real.exp (-u) : ℂ)) u := by
  have hn := (hasDerivAt_neg' u).exp
  simpa only [mul_neg, mul_one, Complex.ofReal_neg, Complex.ofRealCLM_apply,
    Function.comp_def] using Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u hn

/-- Exponential normalization changes the direct radial velocity into the
velocity of the normalized maps. -/
theorem tendstoLocallyUniformlyOn_slope_exp_normalization
    {F : ℝ → ℂ → ℂ} {u : ℝ} {D : ℂ → ℂ}
    (hF : DifferentiableOn ℂ (F u) unitDisk) (hD : DifferentiableOn ℂ D unitDisk)
    (hS : TendstoLocallyUniformlyOn (fun t z ↦ slope (fun s ↦ F s z) u t)
      (fun z ↦ z * deriv (F u) z * D z) (𝓝[≠] u) unitDisk) :
    let G (t : ℝ) (z : ℂ) := (Real.exp (-t) : ℂ) * F t z
    TendstoLocallyUniformlyOn (fun t z ↦ slope (fun s ↦ G s z) u t)
      (fun z ↦ z * deriv (G u) z * D z - G u z) (𝓝[≠] u) unitDisk := by
  let E (t : ℝ) : ℂ := Real.exp (-t)
  let G (t : ℝ) (z : ℂ) := E t * F t z
  have hEC : Tendsto E (𝓝[≠] u) (𝓝 (E u)) :=
    (hasDerivAt_exp_neg_ofReal u).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hES := scalar_locallyUniform (hasDerivAt_exp_neg_ofReal u).tendsto_slope
  have hSc : ContinuousOn (fun z ↦ z * deriv (F u) z * D z) unitDisk :=
    (continuous_id.continuousOn.mul (hF.deriv unitDisk_isOpen).continuousOn).mul hD.continuousOn
  have hProd :=
    (hES.fun_mul₀ (fixed_locallyUniform (F u)) continuousOn_const hF.continuousOn).fun_add
      ((scalar_locallyUniform hEC).fun_mul₀ hS continuousOn_const hSc)
  change TendstoLocallyUniformlyOn (fun t z ↦ slope (fun s ↦ G s z) u t)
    (fun z ↦ z * deriv (G u) z * D z - G u z) (𝓝[≠] u) unitDisk
  refine (hProd.congr (fun t z _ ↦ ?_)).congr_right (fun z hz ↦ ?_)
  · simp only [G, slope_def_module, Complex.real_smul]
    ring
  · have hFz := (hF.differentiableAt (unitDisk_isOpen.mem_nhds hz)).hasDerivAt
    have hG : HasDerivAt (G u) (E u * deriv (F u) z) z := hFz.const_mul (E u)
    change (-E u) * F u z + E u * (z * deriv (F u) z * D z) =
      z * deriv (G u) z * D z - G u z
    rw [hG.deriv]
    dsimp only [G]
    ring

/-- Taking Taylor coefficients after exponential normalization gives the
finite radial differential system. -/
theorem hasDerivAt_radialTaylorCoeff_exp_normalization
    {F : ℝ → ℂ → ℂ} {u : ℝ} {κ : ℂ} (hκ : ‖κ‖ ≤ 1)
    (hF : ∀ t, DifferentiableOn ℂ (F t) unitDisk)
    (hS : TendstoLocallyUniformlyOn (fun t z ↦ slope (fun s ↦ F s z) u t)
      (fun z ↦ z * deriv (F u) z * radialDriver κ z) (𝓝[≠] u) unitDisk) (k : ℕ) :
    let G (t : ℝ) (z : ℂ) := (Real.exp (-t) : ℂ) * F t z
    HasDerivAt (fun t ↦ coeff (G t) (k + 1))
      ((k : ℂ) * coeff (G u) (k + 1) + 2 *
        ∑ j ∈ Finset.range k, ((j : ℂ) + 1) * coeff (G u) (j + 1) * κ ^ (k - j)) u :=
  hasDerivAt_radialTaylorCoeff hκ (fun t ↦ (hF t).const_mul _)
    (tendstoLocallyUniformlyOn_slope_exp_normalization (hF u) (radialDriver_holomorphic hκ) hS) k

end Zalcman
