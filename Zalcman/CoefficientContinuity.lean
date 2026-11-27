/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.CoefficientBound
public import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Tactic.Ring

/-!
# Continuity of Taylor and logarithmic coefficients

Locally uniform convergence on the unit disk gives convergence of each Taylor
coefficient. The coefficient recursions give the corresponding convergence for
the normalized square-root and logarithmic coefficients and for the Milin sums.
-/

public section

namespace Zalcman

open Filter
open scoped BigOperators Topology

section Limits

variable {ι : Type*} {l : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ}

lemma tendsto_coeff (h : TendstoLocallyUniformlyOn F f l unitDisk)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) unitDisk) (n : ℕ) :
    Tendsto (fun i ↦ coeff (F i) n) l (𝓝 (coeff f n)) := by
  have hder (n : ℕ) : TendstoLocallyUniformlyOn (fun i ↦ iteratedDeriv n (F i))
        (iteratedDeriv n f) l unitDisk ∧
      (∀ᶠ i in l, DifferentiableOn ℂ (iteratedDeriv n (F i)) unitDisk) := by
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using And.intro h hF
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · simpa only [iteratedDeriv_succ, Function.comp_def] using
          ih.1.deriv ih.2 unitDisk_isOpen
      · simpa only [iteratedDeriv_succ] using
          ih.2.mono (fun _ hi ↦ hi.deriv unitDisk_isOpen)
  exact tendsto_const_nhds.mul ((hder n).1.tendsto_at zero_mem_unitDisk)

lemma rootCoeff_succ_recursion {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ) :
    rootCoeff hf (n + 1) =
      (coeff f (n + 2) - ∑ i ∈ Finset.range n, rootCoeff hf (i + 1) * rootCoeff hf (n - i)) / 2 := by
  have he := coeff_succ_eq_sum_rootCoeff hf (n + 1)
  rw [Finset.sum_range_succ, Finset.sum_range_succ'] at he
  simp only [Nat.sub_zero, Nat.sub_self, rootCoeff_zero, one_mul, mul_one] at he
  have hsub (i : ℕ) : n + 1 - (i + 1) = n - i := by omega
  simp only [hsub] at he
  rw [he]
  ring

lemma logCoeff_succ_recursion {f : ℂ → ℂ} (hf : NormalizedUnivalent f) (n : ℕ) :
    logCoeff hf (n + 1) = (n + 1 : ℂ) * rootCoeff hf (n + 1) -
      ∑ i ∈ Finset.range n, logCoeff hf (n - i) * rootCoeff hf (i + 1) := by
  have he := rootCoeff_succ_eq_sum_logCoeff hf n
  rw [Finset.sum_range_succ'] at he
  simp only [Nat.sub_zero, rootCoeff_zero, mul_one] at he
  have hsub (i : ℕ) : n + 1 - (i + 1) = n - i := by omega
  simp only [hsub] at he
  rw [he]
  ring

variable (h : TendstoLocallyUniformlyOn F f l unitDisk)
variable (hF : ∀ i, NormalizedUnivalent (F i)) (hf : NormalizedUnivalent f)

include h

lemma tendsto_rootCoeff (n : ℕ) :
    Tendsto (fun i ↦ rootCoeff (hF i) n) l (𝓝 (rootCoeff hf n)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [rootCoeff_zero] using tendsto_const_nhds
    | succ n =>
      simp only [rootCoeff_succ_recursion _ n]
      apply Tendsto.div_const
      apply (tendsto_coeff h (Eventually.of_forall fun i ↦ (hF i).holomorphic) (n + 2)).sub
      refine tendsto_finsetSum _ fun j hj ↦ (ih (j + 1) ?_).mul (ih (n - j) (by omega))
      exact Nat.succ_lt_succ (Finset.mem_range.mp hj)

lemma tendsto_logCoeff (n : ℕ) :
    Tendsto (fun i ↦ logCoeff (hF i) n) l (𝓝 (logCoeff hf n)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [logCoeff_zero] using tendsto_const_nhds
    | succ n =>
      simp only [logCoeff_succ_recursion _ n]
      apply (tendsto_const_nhds.mul (tendsto_rootCoeff h hF hf (n + 1))).sub
      exact tendsto_finsetSum _ fun j _ ↦ (ih (n - j) (by omega)).mul
        (tendsto_rootCoeff h hF hf (j + 1))

lemma tendsto_milinSum (n : ℕ) :
    Tendsto (fun i ↦ (milinCoefficients (hF i)).milinSum n)
      l (𝓝 ((milinCoefficients hf).milinSum n)) := by
  simp only [MilinCoefficients.milinSum, milinCoefficients]
  exact tendsto_finsetSum _ fun j _ ↦ tendsto_const_nhds.mul
    (tendsto_const_nhds.sub ((tendsto_logCoeff h hF hf (j + 1)).norm.pow 2))

end Limits

end Zalcman
