/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.Area
public import Mathlib.Analysis.Calculus.FDeriv.Norm
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-!
# Sharp lower growth on the unit disk

We follow the inverse image of a straight segment from zero to a point of
minimum modulus on the boundary of the image of a smaller disk.
-/

namespace Zalcman

open Set Filter
open scoped Topology

private lemma hasDerivAt_disk_inverse {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {z : ℂ} (hz : z ∈ unitDisk) :
    HasDerivAt (Function.invFunOn f unitDisk) (deriv f z)⁻¹ (f z) := by
  have ha := hf.holomorphic.analyticOnNhd Metric.isOpen_ball z hz
  have hd := (ha.contDiffAt (n := 1)).hasStrictDerivAt (by norm_num)
  refine (hd.to_local_left_inverse (hf.deriv_ne_zero hz) ?_).hasDerivAt
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  exact hf.injective.leftInvOn_invFunOn hw

private lemma image_disk_open {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    {r : ℝ} (hr : r ≤ 1) : IsOpen (f '' Metric.ball 0 r) := by
  have h := (hf.holomorphic.analyticOnNhd Metric.isOpen_ball).is_constant_or_isOpen
    (convex_ball (0 : ℂ) 1).isPreconnected
  rcases h with ⟨c, hc⟩ | hopen
  · exfalso
    have hm : (1 / 2 : ℂ) ∈ unitDisk := by norm_num [mem_unitDisk, norm_div]
    have hcontr := hf.injective zero_mem_unitDisk hm
      ((hc 0 zero_mem_unitDisk).trans (hc _ hm).symm)
    norm_num at hcontr
  · exact hopen _ (Metric.ball_subset_ball hr) Metric.isOpen_ball

private lemma ball_subset_image_of_boundary_minimum {f : ℂ → ℂ}
    (hf : NormalizedUnivalent f) {r d : ℝ} (hr : 0 < r) (hr₁ : r < 1) (hd : 0 < d)
    (hmin : ∀ w ∈ Metric.sphere (0 : ℂ) r, d ≤ ‖f w‖) :
    Metric.ball (0 : ℂ) d ⊆ f '' Metric.ball 0 r := by
  let A := f '' Metric.ball (0 : ℂ) r
  let B := f '' Metric.closedBall (0 : ℂ) r
  have hA : IsOpen A := image_disk_open hf hr₁.le
  have hB : IsClosed B := ((isCompact_closedBall (0 : ℂ) r).image_of_continuousOn
    (hf.holomorphic.continuousOn.mono (Metric.closedBall_subset_ball hr₁))).isClosed
  have hAB : Disjoint A Bᶜ := by
    rw [Set.disjoint_left]
    intro w hw hwb
    exact hwb (image_mono Metric.ball_subset_closedBall hw)
  have hcover : Metric.ball (0 : ℂ) d ⊆ A ∪ Bᶜ := by
    intro w hw
    by_cases hwB : w ∈ B
    · obtain ⟨v, hv, rfl⟩ := hwB
      left
      refine ⟨v, ?_, rfl⟩
      have hvle : ‖v‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hv
      have hvlt : ‖v‖ < r := by
        by_contra hbad
        have hvs : v ∈ Metric.sphere (0 : ℂ) r := by
          simpa [Metric.mem_sphere, dist_zero_right] using le_antisymm hvle (le_of_not_gt hbad)
        have hwd : ‖f v‖ < d := by simpa [Metric.mem_ball, dist_zero_right] using hw
        exact (not_lt_of_ge (hmin v hvs)) hwd
      simpa [Metric.mem_ball, dist_zero_right] using hvlt
    · exact Or.inr hwB
  have hnon : (Metric.ball (0 : ℂ) d ∩ A).Nonempty := by
    refine ⟨0, Metric.mem_ball_self hd, 0, Metric.mem_ball_self hr, hf.map_zero⟩
  exact (convex_ball (0 : ℂ) d).isPreconnected.subset_left_of_subset_union
    hA hB.isOpen_compl hAB hcover hnon

private lemma hasDerivAt_lowerGrowthProfile (s : ℝ) (hs : 0 ≤ s) :
    HasDerivAt (fun x : ℝ ↦ x / (1 + x) ^ 2) ((1 - s) / (1 + s) ^ 3) s := by
  have hden : 1 + s ≠ 0 := by linarith
  let v : ℝ := (1 * (1 + s) ^ 2 - s * (2 * (1 + s) ^ (2 - 1 : ℕ) * (0 + 1))) /
    ((1 + s) ^ 2) ^ 2
  have hd : HasDerivAt (fun x : ℝ ↦ x / (1 + x) ^ 2) v s := (hasDerivAt_id s).div
    (((hasDerivAt_const s (1 : ℝ)).add (hasDerivAt_id s)).pow 2) (pow_ne_zero 2 hden)
  have hv : v = (1 - s) / (1 + s) ^ 3 := by
    dsimp [v]
    field_simp [hden]
    ring
  exact hv ▸ hd

/-- The sharp lower half of the growth theorem for normalized univalent functions. -/
theorem sharp_lower_growth {f : ℂ → ℂ} (hf : NormalizedUnivalent f) {z : ℂ}
    (hz : z ∈ unitDisk) : ‖z‖ / (1 + ‖z‖) ^ 2 ≤ ‖f z‖ := by
  by_cases hzero : z = 0
  · simp [hzero, hf.map_zero]
  let r : ℝ := ‖z‖
  have hr : 0 < r := norm_pos_iff.mpr hzero
  have hr₁ : r < 1 := mem_unitDisk.mp hz
  have hsphere : Metric.sphere (0 : ℂ) r ⊆ unitDisk :=
    Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball hr₁)
  have hzs : z ∈ Metric.sphere (0 : ℂ) r := by simp [r]
  obtain ⟨z₀, hz₀s, hmin⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMinOn ⟨z, hzs⟩
    (hf.holomorphic.continuousOn.mono hsphere).norm
  have hz₀ : z₀ ∈ unitDisk := hsphere hz₀s
  have hz₀norm : ‖z₀‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hz₀s
  let d : ℝ := ‖f z₀‖
  have hd : 0 < d := by
    apply norm_pos_iff.mpr
    intro h
    have he := hf.injective hz₀ zero_mem_unitDisk (h.trans hf.map_zero.symm)
    exact hr.ne' (by simpa [he] using hz₀norm.symm)
  have hmin' : ∀ w ∈ Metric.sphere (0 : ℂ) r, d ≤ ‖f w‖ := isMinOn_iff.mp hmin
  have hdle : d ≤ ‖f z‖ := hmin' z hzs
  have hball := ball_subset_image_of_boundary_minimum hf hr hr₁ hd hmin'
  let ζ : ℂ := f z₀ / (d : ℂ)
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hζ : ‖ζ‖ = 1 := by
    dsimp only [ζ]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd,
      show ‖f z₀‖ = d from rfl, div_self hd.ne']
  have hdζ : (d : ℂ) * ζ = f z₀ := by
    dsimp [ζ]
    field_simp
  have hsegment (t : ℝ) (ht : t ∈ Icc 0 d) : (t : ℂ) * ζ ∈ f '' unitDisk := by
    rcases lt_or_eq_of_le ht.2 with htlt | htd
    · apply image_mono (Metric.ball_subset_ball hr₁.le) (hball ?_)
      rwa [Metric.mem_ball, dist_zero_right, norm_mul, hζ, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht.1]
    · exact ⟨z₀, hz₀, by rw [htd, hdζ]⟩
  let g := Function.invFunOn f unitDisk
  let γ : ℝ → ℂ := fun t ↦ g ((t : ℂ) * ζ)
  have hγ (t : ℝ) (ht : t ∈ Icc 0 d) : γ t ∈ unitDisk ∧ f (γ t) = (t : ℂ) * ζ := by
    obtain ⟨w, hw, he⟩ := hsegment t ht
    dsimp only [γ, g]
    rw [← he]
    exact ⟨Function.invFunOn_apply_mem hw, Function.invFunOn_apply_eq hw⟩
  have hγ₀ : γ 0 = 0 := by
    change g (((0 : ℝ) : ℂ) * ζ) = 0
    rw [Complex.ofReal_zero, zero_mul]
    exact (congrArg g hf.map_zero.symm).trans (hf.injective.leftInvOn_invFunOn zero_mem_unitDisk)
  have hγd : γ d = z₀ := by
    change g ((d : ℂ) * ζ) = z₀
    rw [hdζ]
    exact hf.injective.leftInvOn_invFunOn hz₀
  have hgd (t : ℝ) (ht : t ∈ Icc 0 d) :
      HasDerivAt γ (ζ * (deriv f (γ t))⁻¹) t := by
    obtain ⟨hmem, he⟩ := hγ t ht
    have hinv := hasDerivAt_disk_inverse hf hmem
    rw [he] at hinv
    have hin : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * ζ) ζ t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const ζ
    have hout := hinv.scomp t hin
    change HasDerivAt γ (ζ * (deriv f (γ t))⁻¹) t at hout
    exact hout
  have hγc : ContinuousOn γ (Icc 0 d) := fun t ht ↦ (hgd t ht).continuousAt.continuousWithinAt
  let J : ℝ → ℝ := fun t ↦ t - ‖γ t‖ / (1 + ‖γ t‖) ^ 2
  have hJc : ContinuousOn J (Icc 0 d) := by
    apply continuousOn_id.sub (hγc.norm.div ((continuousOn_const.add hγc.norm).pow 2) ?_)
    intro t _
    apply pow_ne_zero 2
    change 1 + ‖γ t‖ ≠ 0
    positivity
  have hJ (t : ℝ) (ht : t ∈ Ioo 0 d) : DifferentiableAt ℝ J t ∧ 0 ≤ deriv J t := by
    have htc : t ∈ Icc 0 d := Ioo_subset_Icc_self ht
    have hmem : γ t ∈ unitDisk := (hγ t htc).1
    have hγt : γ t ≠ 0 := by
      intro hzero'
      have he := (hγ t htc).2
      rw [hzero', hf.map_zero] at he
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
      have hzeta : ζ ≠ 0 := norm_pos_iff.mp (by rw [hζ]; exact zero_lt_one)
      exact mul_ne_zero htC hzeta he.symm
    let p : ℂ := ζ * (deriv f (γ t))⁻¹
    let L : ℂ →L[ℝ] ℝ := fderiv ℝ (norm : ℂ → ℝ) (γ t)
    have hNorm : DifferentiableAt ℝ (norm : ℂ → ℝ) (γ t) :=
      (contDiffAt_norm ℝ (n := 1) hγt).differentiableAt (by norm_num)
    have hρ : HasDerivAt (fun x ↦ ‖γ x‖) (L p) t :=
      hNorm.hasFDerivAt.comp_hasDerivAt t (hgd t htc)
    have hρle : L p ≤ ‖deriv f (γ t)‖⁻¹ := by
      have hLip := L.le_opNorm p
      have hLn : ‖L‖ = 1 := norm_fderiv_norm hNorm
      rw [hLn, one_mul] at hLip
      exact (le_abs_self _).trans (by simpa [p, norm_mul, hζ, norm_inv, Real.norm_eq_abs] using hLip)
    let a : ℝ := (1 - ‖γ t‖) / (1 + ‖γ t‖) ^ 3
    have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr (mem_unitDisk.mp hmem).le) (by positivity)
    have hal := (hf.distortion_bounds hmem).1
    have hpos : 0 < ‖deriv f (γ t)‖ := norm_pos_iff.mpr (hf.deriv_ne_zero hmem)
    have hprod : a * L p ≤ 1 := calc
      a * L p ≤ a * ‖deriv f (γ t)‖⁻¹ := mul_le_mul_of_nonneg_left hρle ha
      _ ≤ ‖deriv f (γ t)‖ * ‖deriv f (γ t)‖⁻¹ :=
        mul_le_mul_of_nonneg_right hal (inv_nonneg.mpr (norm_nonneg _))
      _ = 1 := mul_inv_cancel₀ hpos.ne'
    have hcomp := (hasDerivAt_lowerGrowthProfile (‖γ t‖) (norm_nonneg _)).comp t hρ
    have hjd : HasDerivAt J (1 - a * L p) t := (hasDerivAt_id t).sub hcomp
    exact ⟨hjd.differentiableAt, hjd.deriv.symm ▸ sub_nonneg.mpr hprod⟩
  have hm : MonotoneOn J (Icc 0 d) := monotoneOn_of_deriv_nonneg (convex_Icc 0 d) hJc
    (fun t ht ↦ (hJ t (by simpa only [interior_Icc] using ht)).1.differentiableWithinAt)
    (fun t ht ↦ (hJ t (by simpa only [interior_Icc] using ht)).2)
  have h0 : (0 : ℝ) ∈ Icc 0 d := ⟨le_rfl, hd.le⟩
  have hdd : d ∈ Icc 0 d := ⟨hd.le, le_rfl⟩
  have hJd := hm h0 hdd hd.le
  have hrd : r / (1 + r) ^ 2 ≤ d := by
    simp [J, hγ₀, hγd, hz₀norm] at hJd
    linarith
  exact hrd.trans hdle

end Zalcman
