/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.ChainTime
public import Zalcman.CoefficientVelocity
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.BoundedVariation
import Mathlib.Tactic.NormNum

/-!
# Time regularity of nested-chain coefficients
-/

public section

namespace Zalcman

open Filter MeasureTheory Set
open scoped NNReal

/-- Each Taylor coefficient is absolutely continuous on a bounded time
interval, and all coefficients are differentiable on one common conull set
in its interior. -/
theorem nested_chain_coefficients_time_regular {F : ℝ → ℂ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Ici 0, DifferentiableOn ℂ (F t) unitDisk)
    (hi : ∀ t ∈ Ici 0, InjOn (F t) unitDisk) (h₀ : ∀ t ∈ Ici 0, F t 0 = 0)
    (h₁ : ∀ t ∈ Ici 0, deriv (F t) 0 = (Real.exp t : ℂ))
    (hsub : ∀ s ∈ Ici 0, ∀ t ∈ Ici 0, s ≤ t → F s '' unitDisk ⊆ F t '' unitDisk) :
    (∀ n, AbsolutelyContinuousOnInterval (fun t ↦ coeff (F t) n) 0 T) ∧
      ∀ᵐ u : ℝ ∂volume, u ∈ Ioo 0 T → ∀ n,
        HasDerivAt (fun t ↦ coeff (F t) n) (deriv (fun t ↦ coeff (F t) n) u) u := by
  let r : ℝ≥0 := 1 / 2
  have hr : 0 < r := by norm_num [r]
  have hr' : (r : ℝ) < 1 := by norm_num [r]
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_nested_chain (T := T) (NNReal.coe_nonneg r) hr'
    hd hi h₀ h₁ hsub
  have hLip (n : ℕ) : LipschitzOnWith (K / r ^ n) (fun t ↦ coeff (F t) n) (Icc 0 T) := by
    refine lipschitzOnWith_coeff hr hr' (fun t ht ↦ hd t ht.1) (fun z hz ↦ hK z ?_) n
    have hzn : ‖z‖ = (r : ℝ) := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    exact hzn.le
  refine ⟨fun n ↦ ?_, ?_⟩
  · have h := hLip n
    rw [← uIcc_of_le hT] at h
    exact h.absolutelyContinuousOnInterval
  · have hD : ∀ᵐ u : ℝ ∂volume, ∀ n : ℕ,
        u ∈ Icc 0 T → DifferentiableWithinAt ℝ (fun t ↦ coeff (F t) n) (Icc 0 T) u :=
      ae_all_iff.mpr fun n ↦ (hLip n).ae_differentiableWithinAt_of_mem_real
    exact hD.mono fun u hu hmem n ↦
      ((hu n ⟨hmem.1.le, hmem.2.le⟩).differentiableAt (Icc_mem_nhds hmem.1 hmem.2)).hasDerivAt

end Zalcman
