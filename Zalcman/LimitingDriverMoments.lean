/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CoefficientVelocity
public import Zalcman.ComplexTriangular
public import Zalcman.FiniteDriverMoments
public import Zalcman.LogarithmicCoefficients
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FieldSimp

/-!
# Finite driving moments from limits of radial transitions

The Taylor coefficient of each time slope converges by scalar time
regularity. The locally uniform transition remainder vanishes, so lower
triangular inversion recovers all coefficients of the limiting driver.
-/
public section

namespace Zalcman

open Filter Finset
open scoped Topology

/-- The limiting coefficient vector of the driver is obtained by triangular
inversion from the time-slope coefficients. -/
theorem tendsto_driver_coeff_of_transition_error {ι : Type*} {l : Filter ι}
    {A p : ι → ℂ → ℂ} {g : ℂ → ℂ} {c : ι → ℂ} {v : ℕ → ℂ}
    (hA : ∀ᶠ i in l, DifferentiableOn ℂ (A i) unitDisk)
    (hp : ∀ᶠ i in l, DifferentiableOn ℂ (p i) unitDisk)
    (hg : DifferentiableOn ℂ g unitDisk) (hg₀ : g 0 = 0) (hg₁ : coeff g 1 ≠ 0)
    (hc : Tendsto c l (𝓝 (1 : ℂ)))
    (hv : ∀ n, Tendsto (fun i ↦ coeff (A i) (n + 1)) l (𝓝 (v n)))
    (hE : TendstoLocallyUniformlyOn (fun i z ↦ A i z - c i * (p i z * g z))
      (fun _ ↦ 0) l unitDisk) (n : ℕ) :
    Tendsto (fun i ↦ coeff (p i) n) l
      (𝓝 (complexTriangularSolution (fun m k ↦ coeff g (m + 1 - k)) v n)) := by
  let E (i : ι) (z : ℂ) := A i z - c i * (p i z * g z)
  have hED : ∀ᶠ i in l, DifferentiableOn ℂ (E i) unitDisk := by
    filter_upwards [hA, hp] with i hAi hpi
    exact hAi.sub ((hpi.fun_mul hg).const_mul (c i))
  have hE₀ (r : ℕ) : coeff (fun _ : ℂ ↦ (0 : ℂ)) r = 0 := by
    simp [coeff]
  have hEC (r : ℕ) : Tendsto (fun i ↦ coeff (E i) r) l (𝓝 0) := by
    simpa only [hE₀] using tendsto_coeff hE hED r
  refine tendsto_of_complex_triangular_sums (B := fun m k ↦ coeff g (m + 1 - k))
    (fun m ↦ by rw [show m + 1 - m = 1 by omega]; exact hg₁) ?_ n
  intro m
  have h := ((hv m).sub (hEC (m + 1))).div hc one_ne_zero
  simp only [sub_zero, div_one] at h
  refine h.congr' ?_
  filter_upwards [hA, hp, hc.eventually_ne one_ne_zero] with i hAi hpi hci
  have hExp : coeff (E i) (m + 1) = coeff (A i) (m + 1) - c i *
      (∑ k ∈ range (m + 1), coeff g (m + 1 - k) * coeff (p i) k) := by
    dsimp only [E]
    rw [coeff_sub hAi ((hpi.fun_mul hg).const_mul (c i)), coeff_const_mul, coeff_mul hpi hg,
      sum_range_succ, Nat.sub_self, coeff_zero, hg₀, mul_zero, add_zero]
    simp only [mul_comm]
  change (coeff (A i) (m + 1) - coeff (E i) (m + 1)) / c i = _
  rw [hExp, sub_sub_cancel, mul_div_cancel_left₀ _ hci]

/-- The positive-degree coefficients in the limiting driver remain in the
closed unit-moment hull after dividing by two. -/
theorem limiting_driver_coeff_mem_closedUnitMomentHull {ι : Type*} {l : Filter ι} [NeBot l]
    {p : ι → ℂ → ℂ} {m : ℕ → ℂ}
    (hp : ∀ᶠ i in l, DifferentiableOn ℂ (p i) unitDisk ∧ p i 0 = 1 ∧
      ∀ z ∈ unitDisk, 0 ≤ (p i z).re)
    (hm : ∀ n, Tendsto (fun i ↦ coeff (p i) n) l (𝓝 (m n))) (M : ℕ) :
    (fun k : Fin M ↦ m (k.val + 1) / 2) ∈ closedUnitMomentHull M := by
  have hClosed : IsClosed (closedUnitMomentHull M) := isClosed_closure
  have hLimit : Tendsto (fun i (k : Fin M) ↦ coeff (p i) (k.val + 1) / 2) l
      (𝓝 (fun k ↦ m (k.val + 1) / 2)) :=
    tendsto_pi_nhds.mpr fun k ↦ (hm (k.val + 1)).div_const 2
  apply hClosed.mem_of_tendsto hLimit
  filter_upwards [hp] with i hi
  exact coeff_mem_closedUnitMomentHull hi.1 hi.2.1 hi.2.2 M

end Zalcman
