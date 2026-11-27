/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.RiemannNormalized
public import Mathlib.Analysis.Complex.Schwarz

@[expose] public section

/-!
# Subordination and monotonicity of conformal radii

The inverse of the outer conformal map gives a disk transition. Its
derivative at the origin is the ratio of the two conformal radii.
-/

namespace Zalcman

open scoped Topology

/-- A nested pair of holomorphic disk maps has a normalized transition. -/
theorem exists_normalized_disk_transition {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisk) (hg : DifferentiableOn ℂ g unitDisk)
    (hgi : Set.InjOn g unitDisk) (hf₀ : f 0 = 0) (hg₀ : g 0 = 0)
    (hsub : f '' unitDisk ⊆ g '' unitDisk) :
    ∃ phi : ℂ → ℂ, DifferentiableOn ℂ phi unitDisk ∧
      Set.MapsTo phi unitDisk unitDisk ∧ phi 0 = 0 ∧
      Set.EqOn (fun z ↦ g (phi z)) f unitDisk ∧ deriv phi 0 = deriv f 0 / deriv g 0 := by
  let inv := Function.invFunOn g unitDisk
  let phi := fun z ↦ inv (f z)
  have hleft (z : ℂ) (hz : z ∈ unitDisk) : inv (g z) = z := hgi.leftInvOn_invFunOn hz
  have hphi₀ : phi 0 = 0 := by simpa only [phi, hf₀, hg₀] using hleft 0 zero_mem_unitDisk
  have hinv (z : ℂ) (hz : z ∈ unitDisk) :
      HasDerivAt inv (deriv g z)⁻¹ (g z) := by
    have ha := hg.analyticOnNhd Metric.isOpen_ball z hz
    have hd := (ha.contDiffAt (n := 1)).hasStrictDerivAt (by norm_num)
    have hn := OAI.Brennan.univalent_deriv_ne_zero Metric.isOpen_ball ⟨hg, hgi⟩ hz
    refine (hd.to_local_left_inverse hn ?_).hasDerivAt
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with x hx
    exact hleft x hx
  have hx (z : ℂ) (hz : z ∈ unitDisk) : ∃ w ∈ unitDisk, g w = f z :=
    hsub ⟨z, hz, rfl⟩
  have hdphi (z : ℂ) (hz : z ∈ unitDisk) :
      HasDerivAt phi ((deriv g (phi z))⁻¹ * deriv f z) z := by
    obtain ⟨w, hw, heq⟩ := hx z hz
    have hφw : phi z = w := by rw [show phi z = inv (f z) from rfl, ← heq, hleft w hw]
    have hinv' : HasDerivAt inv (deriv g w)⁻¹ (f z) := heq ▸ hinv w hw
    rw [hφw]
    exact hinv'.comp z (hf.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt
  have hmap : Set.MapsTo phi unitDisk unitDisk := by
    intro z hz
    obtain ⟨w, hw, heq⟩ := hx z hz
    show inv (f z) ∈ unitDisk
    rwa [← heq, hleft w hw]
  have he : Set.EqOn (fun z ↦ g (phi z)) f unitDisk := by
    intro z hz
    obtain ⟨w, hw, heq⟩ := hx z hz
    change g (inv (f z)) = f z
    rw [← heq, hleft w hw]
  refine ⟨phi, fun z hz ↦ (hdphi z hz).differentiableAt.differentiableWithinAt,
    hmap, hphi₀, he, ?_⟩
  rw [(hdphi 0 zero_mem_unitDisk).deriv, hphi₀, div_eq_mul_inv, mul_comm]

/-- Inclusion of the images gives monotonicity of the positive conformal radii. -/
theorem conformal_radius_le_of_image_subset {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisk) (hg : DifferentiableOn ℂ g unitDisk)
    (hgi : Set.InjOn g unitDisk) (hf₀ : f 0 = 0) (hg₀ : g 0 = 0)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s)
    (hfr : deriv f 0 = (r : ℂ)) (hgs : deriv g 0 = (s : ℂ))
    (hsub : f '' unitDisk ⊆ g '' unitDisk) : r ≤ s := by
  obtain ⟨phi, hd, hm, h₀, _, hder⟩ :=
    exists_normalized_disk_transition hf hg hgi hf₀ hg₀ hsub
  have hm' : Set.MapsTo phi unitDisk (Metric.closedBall (phi 0) 1) := by
    rw [h₀]
    exact fun z hz ↦ Metric.ball_subset_closedBall (hm hz)
  have hh := Complex.norm_deriv_le_one_of_mapsTo_ball
    (R := 1) (c := (0 : ℂ)) hd hm' zero_lt_one
  rw [hder, hfr, hgs, norm_div, Complex.norm_of_nonneg hr, Complex.norm_of_nonneg hs.le] at hh
  exact (div_le_one hs).mp hh

end Zalcman
