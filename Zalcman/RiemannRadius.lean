/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.RiemannTransition
public import Zalcman.Upstream.Crouzeix.Montel
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Tactic.NormNum

/-!
# Conformal radii of nested domains

Schwarz rigidity proves strict monotonicity and uniqueness. For increasing unions,
compact subdisks exhaust the limiting image. For decreasing intersections, the
transition into the first domain is a normal family of disk self-maps.
-/

@[expose] public section

namespace Zalcman

open Set Filter
open scoped Topology

private theorem isOpen_disk_image_of_deriv_ne_zero {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisk) (hd : deriv f 0 ≠ 0) : IsOpen (f '' unitDisk) := by
  rcases (hf.analyticOnNhd Metric.isOpen_ball).is_constant_or_isOpen
      (convex_ball (0 : ℂ) 1).isPreconnected with ⟨c, hc⟩ | ho
  · exfalso
    have hev : f =ᶠ[𝓝 0] fun _ : ℂ ↦ c := by
      filter_upwards [Metric.isOpen_ball.mem_nhds zero_mem_unitDisk] with z hz
      exact hc z hz
    exact hd ((hasDerivAt_const (0 : ℂ) c).congr_of_eventuallyEq hev).deriv
  · exact ho unitDisk Subset.rfl Metric.isOpen_ball

/-- A disk self-map fixing the origin whose derivative is one is the identity. -/
theorem eqOn_id_of_disk_transition_deriv_eq_one {phi : ℂ → ℂ}
    (hd : DifferentiableOn ℂ phi unitDisk) (hm : MapsTo phi unitDisk unitDisk)
    (h₀ : phi 0 = 0) (hder : deriv phi 0 = 1) : EqOn phi id unitDisk := by
  have hc : MapsTo phi unitDisk (Metric.closedBall (phi 0) 1) := by
    rw [h₀]
    exact fun z hz ↦ Metric.ball_subset_closedBall (hm hz)
  have hs : ‖dslope phi (0 : ℂ) 0‖ = (1 : ℝ) / 1 := by
    rw [dslope_same, hder, norm_one, div_one]
  have hrigid := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hd hc zero_mem_unitDisk hs
  intro z hz
  simpa [h₀, dslope_same, hder, smul_eq_mul] using hrigid hz

/-- Equality of positive radii for nested images forces the two maps to agree. -/
theorem eqOn_of_image_subset_of_conformal_radius_eq {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisk) (hg : DifferentiableOn ℂ g unitDisk)
    (hgi : InjOn g unitDisk) (hf₀ : f 0 = 0) (hg₀ : g 0 = 0)
    (hder : deriv f 0 = deriv g 0) (hgn : deriv g 0 ≠ 0)
    (hsub : f '' unitDisk ⊆ g '' unitDisk) : EqOn f g unitDisk := by
  obtain ⟨phi, hd, hm, h₀, heq, hφ⟩ := exists_normalized_disk_transition hf hg hgi hf₀ hg₀ hsub
  have hφ₁ : deriv phi 0 = 1 := by rw [hφ, hder, div_self hgn]
  have hid := eqOn_id_of_disk_transition_deriv_eq_one hd hm h₀ hφ₁
  intro z hz
  exact (heq hz).symm.trans (congrArg g (hid hz))

/-- A proper inclusion of images strictly increases the positive conformal radius. -/
theorem conformal_radius_lt_of_image_ssubset {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisk) (hg : DifferentiableOn ℂ g unitDisk)
    (hgi : InjOn g unitDisk) (hf₀ : f 0 = 0) (hg₀ : g 0 = 0)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s)
    (hfr : deriv f 0 = (r : ℂ)) (hgs : deriv g 0 = (s : ℂ))
    (hsub : f '' unitDisk ⊂ g '' unitDisk) : r < s := by
  refine lt_of_le_of_ne
    (conformal_radius_le_of_image_subset hf hg hgi hf₀ hg₀ hr hs hfr hgs hsub.le) ?_
  intro hrs
  have hder : deriv f 0 = deriv g 0 := by rw [hfr, hgs, hrs]
  have hgn : deriv g 0 ≠ 0 := hgs.symm ▸ Complex.ofReal_ne_zero.mpr hs.ne'
  have heq := eqOn_of_image_subset_of_conformal_radius_eq hf hg hgi hf₀ hg₀ hder hgn hsub.le
  exact hsub.ne (heq.image_eq)

/-- Two normalized Riemann maps onto the same domain coincide on the disk. -/
theorem eqOn_of_image_eq_of_positive_conformal_radius {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisk) (hg : DifferentiableOn ℂ g unitDisk)
    (hfi : InjOn f unitDisk) (hgi : InjOn g unitDisk) (hf₀ : f 0 = 0) (hg₀ : g 0 = 0)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hfr : deriv f 0 = (r : ℂ)) (hgs : deriv g 0 = (s : ℂ))
    (himage : f '' unitDisk = g '' unitDisk) : EqOn f g unitDisk := by
  have hrs := conformal_radius_le_of_image_subset hf hg hgi hf₀ hg₀ hr.le hs hfr hgs himage.le
  have hsr := conformal_radius_le_of_image_subset hg hf hfi hg₀ hf₀ hs.le hr hgs hfr himage.ge
  have hder : deriv f 0 = deriv g 0 := by rw [hfr, hgs, le_antisymm hrs hsr]
  exact eqOn_of_image_subset_of_conformal_radius_eq hf hg hgi hf₀ hg₀ hder
    (hgs.symm ▸ Complex.ofReal_ne_zero.mpr hs.ne') himage.le

/-- The conformal radii of an increasing sequence converge to that of the union. -/
theorem tendsto_conformal_radius_of_iUnion {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    {r : ℕ → ℝ} {R : ℝ} (hF : ∀ n, DifferentiableOn ℂ (F n) unitDisk)
    (hFi : ∀ n, InjOn (F n) unitDisk) (hF₀ : ∀ n, F n 0 = 0)
    (hr : ∀ n, 0 < r n) (hFr : ∀ n, deriv (F n) 0 = (r n : ℂ))
    (hG : DifferentiableOn ℂ G unitDisk) (hGi : InjOn G unitDisk) (hG₀ : G 0 = 0)
    (hR : 0 < R) (hGR : deriv G 0 = (R : ℂ))
    (hmono : Monotone (fun n ↦ F n '' unitDisk))
    (hcover : (⋃ n, F n '' unitDisk) = G '' unitDisk) : Tendsto r atTop (𝓝 R) := by
  have hrmono : Monotone r := fun i j hij ↦
    conformal_radius_le_of_image_subset (hF i) (hF j) (hFi j) (hF₀ i) (hF₀ j)
      (hr i).le (hr j) (hFr i) (hFr j) (hmono hij)
  have hrle (n : ℕ) : r n ≤ R := by
    apply conformal_radius_le_of_image_subset (hF n) hG hGi (hF₀ n) hG₀ (hr n).le hR (hFr n) hGR
    rw [← hcover]
    exact subset_iUnion (fun n ↦ F n '' unitDisk) n
  have hbound : BddAbove (range r) := ⟨R, forall_mem_range.mpr hrle⟩
  have hopen (n : ℕ) : IsOpen (F n '' unitDisk) :=
    isOpen_disk_image_of_deriv_ne_zero (hF n)
      ((hFr n).symm ▸ Complex.ofReal_ne_zero.mpr (hr n).ne')
  have hsup : (⨆ n, r n) = R := by
    refine le_antisymm (ciSup_le hrle) (le_of_forall_lt ?_)
    intro a ha
    obtain ⟨b, hb, hbR⟩ := exists_between (max_lt (show a < R from ha) hR)
    have hb₀ : 0 < b := (le_max_right a 0).trans_lt hb
    have hab : a < b := (le_max_left a 0).trans_lt hb
    let q := b / R
    have hq₀ : 0 < q := div_pos hb₀ hR
    have hq₁ : q < 1 := (div_lt_one hR).2 hbR
    have hqR : q * R = b := div_mul_cancel₀ b hR.ne'
    have hsmall : Metric.closedBall (0 : ℂ) q ⊆ unitDisk := Metric.closedBall_subset_ball hq₁
    let K := G '' Metric.closedBall (0 : ℂ) q
    have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) q).image_of_continuousOn
      (hG.continuousOn.mono hsmall)
    have hKcover : K ⊆ ⋃ n, F n '' unitDisk := by
      rw [hcover]
      exact image_mono hsmall
    obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n ↦ F n '' unitDisk) hopen hKcover
      hmono.directed_le
    let H := fun z : ℂ ↦ G ((q : ℂ) * z)
    have hmapK : MapsTo (fun z : ℂ ↦ (q : ℂ) * z) unitDisk (Metric.closedBall 0 q) := by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_of_nonneg hq₀.le]
      exact mul_le_of_le_one_right hq₀.le (mem_unitDisk.mp hz).le
    have hmap : MapsTo (fun z : ℂ ↦ (q : ℂ) * z) unitDisk unitDisk :=
      fun z hz ↦ hsmall (hmapK hz)
    have hH : DifferentiableOn ℂ H unitDisk := hG.comp (by fun_prop) hmap
    have hH₀ : H 0 = 0 := by simpa [H] using hG₀
    have hHb : deriv H 0 = (b : ℂ) := by
      simp only [H, deriv_comp_mul_left, smul_eq_mul, mul_zero, hGR, ← Complex.ofReal_mul, hqR]
    have hHsub : H '' unitDisk ⊆ F n '' unitDisk := by
      rintro _ ⟨z, hz, rfl⟩
      exact hn ⟨_, hmapK hz, rfl⟩
    exact hab.trans_le (le_ciSup_of_le hbound n <|
      conformal_radius_le_of_image_subset hH (hF n) (hFi n) hH₀ (hF₀ n)
        hb₀.le (hr n) hHb (hFr n) hHsub)
  simpa only [hsup] using tendsto_atTop_ciSup hrmono hbound

/-- The conformal radii of an increasing exhaustion of the plane tend to infinity. -/
theorem tendsto_conformal_radius_atTop_of_iUnion_univ {F : ℕ → ℂ → ℂ} {r : ℕ → ℝ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) unitDisk) (hFi : ∀ n, InjOn (F n) unitDisk)
    (hF₀ : ∀ n, F n 0 = 0) (hr : ∀ n, 0 < r n) (hFr : ∀ n, deriv (F n) 0 = (r n : ℂ))
    (hmono : Monotone (fun n ↦ F n '' unitDisk))
    (hcover : (⋃ n, F n '' unitDisk) = univ) : Tendsto r atTop atTop := by
  have hrmono : Monotone r := fun i j hij ↦
    conformal_radius_le_of_image_subset (hF i) (hF j) (hFi j) (hF₀ i) (hF₀ j)
      (hr i).le (hr j) (hFr i) (hFr j) (hmono hij)
  have hopen (n : ℕ) : IsOpen (F n '' unitDisk) :=
    isOpen_disk_image_of_deriv_ne_zero (hF n)
      ((hFr n).symm ▸ Complex.ofReal_ne_zero.mpr (hr n).ne')
  refine tendsto_atTop.mpr fun a ↦ ?_
  let b := max a 1
  have hb : 0 < b := zero_lt_one.trans_le (le_max_right a 1)
  have hball : Metric.closedBall (0 : ℂ) b ⊆ ⋃ n, F n '' unitDisk := by rw [hcover]; exact subset_univ _
  obtain ⟨n, hn⟩ := (isCompact_closedBall (0 : ℂ) b).elim_directed_cover
    (fun n ↦ F n '' unitDisk) hopen hball hmono.directed_le
  let H := fun z : ℂ ↦ (b : ℂ) * z
  have hH : DifferentiableOn ℂ H unitDisk := by fun_prop
  have hH₀ : H 0 = 0 := mul_zero _
  have hHb : deriv H 0 = (b : ℂ) := by simp [H]
  have hsub : H '' unitDisk ⊆ F n '' unitDisk := by
    rintro _ ⟨z, hz, rfl⟩
    apply hn
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖(b : ℂ) * z‖ ≤ b
    rw [norm_mul, Complex.norm_of_nonneg hb.le]
    exact mul_le_of_le_one_right hb.le (mem_unitDisk.mp hz).le
  have hle := conformal_radius_le_of_image_subset hH (hF n) (hFi n) hH₀ (hF₀ n)
    hb.le (hr n) hHb (hFr n) hsub
  filter_upwards [eventually_ge_atTop n] with j hj
  exact (le_max_left a 1).trans (hle.trans (hrmono hj))

private theorem norm_disk_transition_le {phi : ℂ → ℂ}
    (hphi : DifferentiableOn ℂ phi unitDisk) (hmap : MapsTo phi unitDisk unitDisk)
    (hphi₀ : phi 0 = 0) {z : ℂ} (hz : z ∈ unitDisk) : ‖phi z‖ ≤ ‖z‖ := by
  have hc : MapsTo phi unitDisk (Metric.closedBall (0 : ℂ) 1) :=
    fun _ hv ↦ Metric.ball_subset_closedBall (hmap hv)
  exact Complex.norm_le_norm_of_mapsTo_ball hphi hc hphi₀ (mem_unitDisk.mp hz)

/-- Decreasing images converge in conformal radius to the interior of their intersection.
A subsequence of the normalized maps also converges locally uniformly to the limiting map. -/
theorem tendsto_conformal_radius_of_interior_iInter {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    {r : ℕ → ℝ} {R : ℝ} (hF : ∀ n, DifferentiableOn ℂ (F n) unitDisk)
    (hFi : ∀ n, InjOn (F n) unitDisk) (hF₀ : ∀ n, F n 0 = 0)
    (hr : ∀ n, 0 < r n) (hFr : ∀ n, deriv (F n) 0 = (r n : ℂ))
    (hG : DifferentiableOn ℂ G unitDisk) (hGi : InjOn G unitDisk) (hG₀ : G 0 = 0)
    (hR : 0 < R) (hGR : deriv G 0 = (R : ℂ))
    (hanti : Antitone (fun n ↦ F n '' unitDisk))
    (hkernel : interior (⋂ n, F n '' unitDisk) = G '' unitDisk) :
    Tendsto r atTop (𝓝 R) ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      TendstoLocallyUniformlyOn (F ∘ σ) G atTop unitDisk := by
  have hopen : IsOpen unitDisk := Metric.isOpen_ball
  have hranti : Antitone r := fun i j hij ↦
    conformal_radius_le_of_image_subset (hF j) (hF i) (hFi i) (hF₀ j) (hF₀ i)
      (hr j).le (hr i) (hFr j) (hFr i) (hanti hij)
  have hrle (n : ℕ) : R ≤ r n := by
    apply conformal_radius_le_of_image_subset hG (hF n) (hFi n) hG₀ (hF₀ n) hR.le (hr n) hGR (hFr n)
    rw [← hkernel]
    exact interior_subset.trans (iInter_subset (fun j ↦ F j '' unitDisk) n)
  let L := ⨅ n, r n
  have hRL : R ≤ L := le_ciInf hrle
  have hL : 0 < L := hR.trans_le hRL
  have hrt : Tendsto r atTop (𝓝 L) := tendsto_atTop_ciInf hranti ⟨R, forall_mem_range.mpr hrle⟩
  have hex (n : ℕ) := exists_normalized_disk_transition (hF n) (hF 0) (hFi 0)
    (hF₀ n) (hF₀ 0) (hanti (Nat.zero_le n))
  choose phi hphi hmap hphi₀ heq hphiDer using hex
  have hnorm (n : ℕ) {z : ℂ} (hz : z ∈ unitDisk) : ‖phi n z‖ ≤ ‖z‖ :=
    norm_disk_transition_le (hphi n) (hmap n) (hphi₀ n) hz
  obtain ⟨psi, σ, hσ, hlim, hpsi, _⟩ := OAI.CrouzeixHilbert.Conformal.montel hopen phi hphi
    (fun n z hz ↦ (hnorm n hz).trans (mem_unitDisk.mp hz).le)
  have hpsiNorm {z : ℂ} (hz : z ∈ unitDisk) : ‖psi z‖ ≤ ‖z‖ :=
    le_of_tendsto (hlim.tendsto_at hz).norm (.of_forall fun n ↦ hnorm (σ n) hz)
  have hpsiMap : MapsTo psi unitDisk unitDisk :=
    fun _ hz ↦ mem_unitDisk.mpr ((hpsiNorm hz).trans_lt (mem_unitDisk.mp hz))
  let H := fun z ↦ F 0 (psi z)
  have hH : DifferentiableOn ℂ H unitDisk := (hF 0).comp hpsi hpsiMap
  have hconv : TendstoLocallyUniformlyOn (F ∘ σ) H atTop unitDisk := by
    refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).mpr ?_
    intro K hKD hK
    by_cases hK₀ : K.Nonempty
    · obtain ⟨w, hw, hwmax⟩ := hK.exists_isMaxOn hK₀ continuous_norm.continuousOn
      let K' := Metric.closedBall (0 : ℂ) ‖w‖
      have hK'D : K' ⊆ unitDisk := Metric.closedBall_subset_ball (mem_unitDisk.mp (hKD hw))
      have hK' : IsCompact K' := isCompact_closedBall (0 : ℂ) ‖w‖
      have hu := hK'.uniformContinuousOn_of_continuous ((hF 0).continuousOn.mono hK'D)
      have hmax {z : ℂ} (hz : z ∈ K) : ‖z‖ ≤ ‖w‖ := hwmax hz
      have hreach (i : ℕ) (z : ℂ) (hz : z ∈ K) : (phi ∘ σ) i z ∈ K' := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (hnorm (σ i) (hKD hz)).trans (hmax hz)
      have hreach' (z : ℂ) (hz : z ∈ K) : psi z ∈ K' := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (hpsiNorm (hKD hz)).trans (hmax hz)
      have hku := (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).mp hlim K hKD hK
      have hcomp := UniformContinuousOn.comp_tendstoUniformlyOn_eventually
        (.of_forall hreach) hreach' hu hku
      exact hcomp.congr (.of_forall fun n z hz ↦ heq (σ n) (hKD hz))
    · rw [not_nonempty_iff_eq_empty.mp hK₀]
      exact tendstoUniformlyOn_empty
  have hH₀ : H 0 = 0 := tendsto_nhds_unique (hconv.tendsto_at zero_mem_unitDisk)
    (tendsto_const_nhds.congr fun n ↦ (hF₀ (σ n)).symm)
  have hHL : deriv H 0 = (L : ℂ) := by
    have hs := (hconv.deriv (.of_forall fun n ↦ hF (σ n)) hopen).tendsto_at zero_mem_unitDisk
    have hsr : Tendsto (fun n ↦ (r (σ n) : ℂ)) atTop (𝓝 (L : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp (hrt.comp hσ.tendsto_atTop)
    exact tendsto_nhds_unique (hs.congr fun n ↦ hFr (σ n)) hsr
  have hHinter : H '' unitDisk ⊆ ⋂ n, F n '' unitDisk := by
    rintro _ ⟨z, hz, rfl⟩
    refine mem_iInter.mpr fun j ↦ ?_
    let K := Metric.closedBall (0 : ℂ) ‖z‖
    have hKD : K ⊆ unitDisk := Metric.closedBall_subset_ball (mem_unitDisk.mp hz)
    have hK : IsCompact (F j '' K) := (isCompact_closedBall _ _).image_of_continuousOn
      ((hF j).continuousOn.mono hKD)
    have htrap : ∀ᶠ n in atTop, F (σ n) z ∈ F j '' K := by
      filter_upwards [hσ.tendsto_atTop.eventually (eventually_ge_atTop j)] with n hn
      obtain ⟨theta, hd, hm, h₀, hθ, _⟩ := exists_normalized_disk_transition (hF (σ n))
        (hF j) (hFi j) (hF₀ (σ n)) (hF₀ j) (hanti hn)
      refine ⟨theta z, ?_, hθ hz⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_disk_transition_le hd hm h₀ hz
    exact image_mono hKD (hK.isClosed.mem_of_tendsto (hconv.tendsto_at hz) htrap)
  have hHopen : IsOpen (H '' unitDisk) :=
    isOpen_disk_image_of_deriv_ne_zero hH (hHL.symm ▸ Complex.ofReal_ne_zero.mpr hL.ne')
  have hHsub : H '' unitDisk ⊆ G '' unitDisk := by
    rw [← hkernel]
    exact hHopen.subset_interior_iff.mpr hHinter
  have hLR := conformal_radius_le_of_image_subset hH hG hGi hH₀ hG₀ hL.le hR hHL hGR hHsub
  have hLR' : L = R := le_antisymm hLR hRL
  have hHGder : deriv H 0 = deriv G 0 := by rw [hHL, hGR, hLR']
  have hHG := eqOn_of_image_subset_of_conformal_radius_eq hH hG hGi hH₀ hG₀ hHGder
    (hGR.symm ▸ Complex.ofReal_ne_zero.mpr hR.ne') hHsub
  exact ⟨hLR' ▸ hrt, σ, hσ, hconv.congr_right hHG⟩

end Zalcman
