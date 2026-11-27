/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.FiniteDriverChain
public import Zalcman.KoebeTail
public import Zalcman.RiemannTransition
import Mathlib.Tactic.Ring

/-!
# Replacing the terminal map of a nested chain

The inverse of the original terminal map embeds each earlier image in the
disk. Composing with a dilated Koebe map changes the terminal map, preserves
nesting, and tends to the original initial map as the terminal time grows.
-/

public section

namespace Zalcman

open Filter Set
open scoped Topology

/-- A nested family can be approximated at its initial time by nested families
with an exact terminal Koebe map. -/
theorem exists_terminalKoebe_nested_chain_approximation
    {F : ℝ → ℂ → ℂ}
    (hF : ∀ t ∈ Ici 0, ExponentialDiskMap t (F t))
    (hsub : ∀ s ∈ Ici 0, ∀ t ∈ Ici 0, s ≤ t → F s '' unitDisk ⊆ F t '' unitDisk) :
    ∃ G : ℝ → ℝ → ℂ → ℂ,
      TendstoLocallyUniformlyOn (fun T ↦ G T 0) (F 0) atTop unitDisk ∧
      ∀ T > 0, (∀ t ∈ Ici 0, ExponentialDiskMap t (G T t)) ∧
        (∀ s ∈ Ici 0, ∀ t ∈ Ici 0, s ≤ t → G T s '' unitDisk ⊆ G T t '' unitDisk) ∧
        EqOn (G T T) (fun z ↦ (Real.exp T : ℂ) * koebe z) unitDisk := by
  classical
  have ex (T : ℝ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ unitDisk ∧ MapsTo φ unitDisk unitDisk ∧
        φ 0 = 0 ∧ EqOn (fun z ↦ F T (φ z)) (F t) unitDisk ∧
        deriv φ 0 = (Real.exp (t - T) : ℂ) := by
    have hT : 0 ≤ T := ht.1.trans ht.2
    obtain ⟨φ, hd, hm, h₀, he, h₁⟩ := exists_normalized_disk_transition
      (hF t ht.1).holomorphic (hF T hT).holomorphic (hF T hT).injective
      (hF t ht.1).map_zero (hF T hT).map_zero (hsub t ht.1 T hT ht.2)
    refine ⟨φ, hd, hm, h₀, he, ?_⟩
    rw [h₁, (hF t ht.1).deriv_zero, (hF T hT).deriv_zero, Real.exp_sub, Complex.ofReal_div]
  choose φ hφd hφm hφ₀ hφe hφ₁ using ex
  let K (t : ℝ) (z : ℂ) := (Real.exp t : ℂ) * koebe z
  let G (T t : ℝ) (z : ℂ) := if ht : t ∈ Icc (0 : ℝ) T then K T (φ T t ht z) else K t z
  have hIn {T t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : G T t = fun z ↦ K T (φ T t ht z) := by
    funext z
    simp only [G, dite_eq_left ht]
  have hOut {T t : ℝ} (ht : t ∉ Icc (0 : ℝ) T) : G T t = K t := by
    funext z
    simp only [G, dite_eq_right ht]
  have hK (t : ℝ) : ExponentialDiskMap t (K t) :=
    .of_normalizedUnivalent koebe_normalizedUnivalent t
  have hEt (T : ℝ) : (Real.exp T : ℂ) * (Real.exp (-T) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  have hEq (T : ℝ) (hT : 0 ≤ T) : EqOn (G T T) (K T) unitDisk := by
    have ht : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
    intro z hz
    have h := (hF T hT).injective (hφm T T ht hz) hz (hφe T T ht hz)
    rw [hIn ht]
    exact congrArg (K T) h
  refine ⟨G, ?_, fun T hT ↦ ⟨?_, ?_, hEq T hT.le⟩⟩
  · let ψ (T : ℝ) : ℂ → ℂ := if hT : 0 ≤ T then φ T 0 ⟨le_rfl, hT⟩ else id
    let g (T : ℝ) (z : ℂ) := (Real.exp (-T) : ℂ) * F T z
    have hG : ∀ᶠ T : ℝ in atTop, G T 0 = fun z ↦ (Real.exp T : ℂ) * koebe (ψ T z) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      rw [hIn (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)]
      simp only [K, ψ, dite_eq_left hT]
    have hg : ∀ᶠ T : ℝ in atTop, NormalizedUnivalent (g T) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact (hF T hT).normalizedUnivalent
    have hp : ∀ᶠ T : ℝ in atTop, MapsTo (ψ T) unitDisk unitDisk := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      simpa only [ψ, dite_eq_left hT] using hφm T 0 ⟨le_rfl, hT⟩
    have he : ∀ᶠ T : ℝ in atTop,
        EqOn (F 0) (fun z ↦ (Real.exp T : ℂ) * g T (ψ T z)) unitDisk := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      intro z hz
      simp only [g, ψ, dite_eq_left hT, ← mul_assoc, hEt T, one_mul]
      exact (hφe T 0 ⟨le_rfl, hT⟩ hz).symm
    refine (tendstoLocallyUniformlyOn_koebe_tail
      (hF 0 le_rfl).holomorphic.continuousOn hg hp he).congr_inseparable ?_
    filter_upwards [hG] with T hT z _
    exact Inseparable.of_eq (congrFun hT z).symm
  · intro t ht
    by_cases h : t ∈ Icc (0 : ℝ) T
    · rw [hIn h]
      have hφi : InjOn (φ T t h) unitDisk := by
        intro z hz w hw he
        apply (hF t ht).injective hz hw
        exact (hφe T t h hz).symm.trans ((congrArg (F T) he).trans (hφe T t h hw))
      refine ⟨(hK T).holomorphic.comp (hφd T t h) (hφm T t h),
        (hK T).injective.comp hφi (hφm T t h), ?_, ?_⟩
      · simp only [hφ₀ T t h, (hK T).map_zero]
      · have hK' := ((hK T).holomorphic.differentiableAt
          (unitDisk_isOpen.mem_nhds (hφm T t h zero_mem_unitDisk))).hasDerivAt
        have hφ' := ((hφd T t h).differentiableAt (unitDisk_isOpen.mem_nhds zero_mem_unitDisk)).hasDerivAt
        change deriv (K T ∘ φ T t h) 0 = _
        rw [(hK'.comp 0 hφ').deriv, hφ₀ T t h, (hK T).deriv_zero, hφ₁ T t h,
          ← Complex.ofReal_mul, ← Real.exp_add]
        rw [show T + (t - T) = t by ring]
    · rw [hOut h]
      exact hK t
  · intro s hs t ht hst
    by_cases htT : t ≤ T
    · have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs, hst.trans htT⟩
      have htT' : t ∈ Icc (0 : ℝ) T := ⟨ht, htT⟩
      rw [hIn hsT, hIn htT']
      rintro _ ⟨z, hz, rfl⟩
      have hIm := hsub s hs t ht hst (mem_image_of_mem (F s) hz)
      obtain ⟨w, hw, he⟩ := hIm
      refine ⟨w, hw, ?_⟩
      have e : φ T t htT' w = φ T s hsT z := by
        apply (hF T hT.le).injective (hφm T t htT' hw) (hφm T s hsT hz)
        exact (hφe T t htT' hw).trans (he.trans (hφe T s hsT hz).symm)
      exact congrArg (K T) e
    · rw [hOut (fun h ↦ htT h.2)]
      by_cases hsT : s ≤ T
      · rw [hIn (show s ∈ Icc (0 : ℝ) T from ⟨hs, hsT⟩)]
        apply Subset.trans _ (koebe_scaled_image_mono (Real.exp_pos T) (Real.exp_le_exp.mpr (le_of_not_ge htT)))
        rintro _ ⟨z, hz, rfl⟩
        exact mem_image_of_mem (K T) (hφm T s ⟨hs, hsT⟩ hz)
      · rw [hOut (fun h ↦ hsT h.2)]
        exact koebe_scaled_image_mono (Real.exp_pos s) (Real.exp_le_exp.mpr hst)

end Zalcman
