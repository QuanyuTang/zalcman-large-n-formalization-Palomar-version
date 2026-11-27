/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.ConstantDriver
public import Zalcman.LocallyUniformTimeSlope
public import Zalcman.LoewnerLogODE
public import Zalcman.PiecewiseUnitControl
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Nested holomorphic chains for finite unit drivers

One constant interval is solved by a Koebe transition. Adjacent
intervals are joined at their common terminal map.
-/

public section

namespace Zalcman

open Filter MeasureTheory Set
open scoped Topology

/-- A disk embedding with the direct Löwner normalization at time `t`. -/
structure ExponentialDiskMap (t : ℝ) (F : ℂ → ℂ) : Prop where
  holomorphic : DifferentiableOn ℂ F unitDisk
  injective : InjOn F unitDisk
  map_zero : F 0 = 0
  deriv_zero : deriv F 0 = (Real.exp t : ℂ)

/-- Multiplying a normalized map by `exp t` gives the direct-chain normalization. -/
theorem ExponentialDiskMap.of_normalizedUnivalent {f : ℂ → ℂ} (hf : NormalizedUnivalent f)
    (t : ℝ) : ExponentialDiskMap t (fun z ↦ (Real.exp t : ℂ) * f z) := by
  have hne := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)
  refine ⟨hf.holomorphic.const_mul _, fun _ hz _ hw he ↦
    hf.injective hz hw (mul_left_cancel₀ hne he), ?_, ?_⟩
  · rw [hf.map_zero, mul_zero]
  · rw [deriv_const_mul_field, hf.deriv_zero, mul_one]

/-- Dividing by `exp t` normalizes the map. -/
theorem ExponentialDiskMap.normalizedUnivalent {t : ℝ} {F : ℂ → ℂ}
    (hF : ExponentialDiskMap t F) :
    NormalizedUnivalent (fun z ↦ (Real.exp (-t) : ℂ) * F z) := by
  have hne := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (-t))
  refine ⟨hF.holomorphic.const_mul _, fun _ hz _ hw he ↦
    hF.injective hz hw (mul_left_cancel₀ hne he), ?_, ?_⟩
  · rw [hF.map_zero, mul_zero]
  · rw [deriv_const_mul_field, hF.deriv_zero, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, Complex.ofReal_one]

/-- Holomorphic nested maps with the specified almost-everywhere unit-driver velocity. -/
structure FiniteDriverChain (a b : ℝ) (κ : ℝ → ℂ) (H : ℂ → ℂ) where
  maps : ℝ → ℂ → ℂ
  map_on : ∀ t ∈ Icc a b, ExponentialDiskMap t (maps t)
  nested : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → maps s '' unitDisk ⊆ maps t '' unitDisk
  terminal : EqOn (maps b) H unitDisk
  seams : Finset ℝ
  velocity_off_seams : ∀ u ∈ Ioo a b, u ∉ seams → ‖κ u‖ = 1 ∧
    TendstoLocallyUniformlyOn (fun t z ↦ slope (fun s ↦ maps s z) u t)
      (fun z ↦ z * radialDriver (κ u) z * deriv (maps u) z) (𝓝[≠] u) unitDisk

/-- The seam times form a null set. -/
theorem FiniteDriverChain.velocity {a b : ℝ} {κ : ℝ → ℂ} {H : ℂ → ℂ}
    (P : FiniteDriverChain a b κ H) :
    ∀ᵐ u : ℝ ∂volume, u ∈ Ioo a b → ‖κ u‖ = 1 ∧
      TendstoLocallyUniformlyOn (fun t z ↦ slope (fun s ↦ P.maps s z) u t)
        (fun z ↦ z * radialDriver (κ u) z * deriv (P.maps u) z) (𝓝[≠] u) unitDisk := by
  filter_upwards [P.seams.finite_toSet.countable.ae_notMem (volume : Measure ℝ)] with u hNot hu
  exact P.velocity_off_seams u hu hNot

/-- A single time point has the prescribed terminal map. -/
def FiniteDriverChain.singleton {b : ℝ} {H : ℂ → ℂ}
    (hH : ExponentialDiskMap b H) (κ : ℝ → ℂ) : FiniteDriverChain b b κ H where
  maps := fun _ ↦ H
  map_on := fun _ ht ↦ (le_antisymm ht.2 ht.1).symm ▸ hH
  nested := fun _ _ _ _ _ ↦ Subset.rfl
  terminal := fun _ _ ↦ rfl
  seams := ∅
  velocity_off_seams := fun _ hu _ ↦ (lt_asymm hu.1 hu.2).elim

/-- The backwards composition with one Koebe transition realizes a single
constant interval with the given terminal map. -/
noncomputable def FiniteDriverChain.constant {a b : ℝ} {κ : ℂ} (hκ : ‖κ‖ = 1)
    {H : ℂ → ℂ} (hH : ExponentialDiskMap b H) :
    FiniteDriverChain a b (fun _ ↦ κ) H where
  maps := fun t z ↦ H (constantDriverTransition κ (b - t) z)
  map_on := by
    intro t ht
    obtain ⟨hd, hi, hmap, hz, hder⟩ :=
      constantDriverTransition_normalization hκ (sub_nonneg.mpr ht.2)
    refine ⟨hH.holomorphic.comp hd hmap, hH.injective.comp hi hmap, ?_, ?_⟩
    · rw [hz, hH.map_zero]
    · have hH' := (hH.holomorphic.differentiableAt
        (unitDisk_isOpen.mem_nhds (hmap zero_mem_unitDisk))).hasDerivAt
      have ht' := (hd.differentiableAt (unitDisk_isOpen.mem_nhds zero_mem_unitDisk)).hasDerivAt
      change deriv (H ∘ constantDriverTransition κ (b - t)) 0 = _
      rw [(hH'.comp 0 ht').deriv, hz, hder, hH.deriv_zero, ← Complex.ofReal_mul, ← Real.exp_add]
      rw [show b + -(b - t) = t by ring]
  nested := by
    intro s hs t ht hst _ hz
    obtain ⟨z, hz, rfl⟩ := hz
    have h₁ := sub_nonneg.mpr ht.2
    have h₂ := sub_nonneg.mpr hst
    refine ⟨constantDriverTransition κ (t - s) z, (constantDriverTransition_spec hκ hz h₂).1, ?_⟩
    change H (constantDriverTransition κ (b - t) (constantDriverTransition κ (t - s) z)) =
      H (constantDriverTransition κ (b - s) z)
    rw [← constantDriverTransition_add hκ hz h₁ h₂, sub_add_sub_cancel]
  terminal := by
    intro z hz
    simp only [sub_self, constantDriverTransition_zero hκ hz]
  seams := ∅
  velocity_off_seams := by
    refine fun u hu _ ↦ ⟨hκ, ?_⟩
    let F (t : ℝ) (z : ℂ) := H (constantDriverTransition κ (b - t) z)
    let G (t : ℝ) (z : ℂ) := z * radialDriver κ z * deriv (F t) z
    have hG : ContinuousOn (fun p : ℝ × ℂ ↦ G p.1 p.2) (Iio b ×ˢ unitDisk) := by
      have hSub : Iio b ×ˢ unitDisk ⊆ Iic b ×ˢ unitDisk := fun _ hp ↦ ⟨hp.1.le, hp.2⟩
      simpa only [G, F, radialDriver] using
        (continuousOn_constantDriverPiece_time_deriv hκ hH.holomorphic b).mono hSub
    exact tendstoLocallyUniformlyOn_slope_of_continuous_time_deriv
      isOpen_Iio hu.2 unitDisk_isOpen hG (fun t ht z hz ↦ by
        simpa only [G, F, radialDriver] using hasDerivAt_constantDriverPiece hκ hz hH.holomorphic ht.le)

/-- Adjacent realized intervals can be joined when the driver agrees with
the local drivers on both interiors. -/
noncomputable def FiniteDriverChain.join {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    {κ κL κR : ℝ → ℂ} {H : ℂ → ℂ}
    (R : FiniteDriverChain b c κR H) (L : FiniteDriverChain a b κL (R.maps b))
    (hκL : EqOn κ κL (Ioo a b)) (hκR : EqOn κ κR (Ioo b c)) :
    FiniteDriverChain a c κ H := by
  classical
  let F (t : ℝ) : ℂ → ℂ := if t ≤ b then L.maps t else R.maps t
  have hFₗ {t : ℝ} (ht : t ≤ b) : F t = L.maps t := ite_eq_left ht
  have hFᵣ {t : ℝ} (ht : b < t) : F t = R.maps t := ite_eq_right (not_le_of_gt ht)
  have hImg : L.maps b '' unitDisk = R.maps b '' unitDisk := L.terminal.image_eq
  let S := insert b (L.seams ∪ R.seams)
  refine ⟨F, ?_, ?_, ?_, S, ?_⟩
  · intro t ht
    rcases le_or_gt t b with h | h
    · rw [hFₗ h]
      exact L.map_on t ⟨ht.1, h⟩
    · rw [hFᵣ h]
      exact R.map_on t ⟨h.le, ht.2⟩
  · intro s hs t ht hst
    rcases le_or_gt t b with htb | hbt
    · rw [hFₗ (hst.trans htb), hFₗ htb]
      exact L.nested s ⟨hs.1, hst.trans htb⟩ t ⟨ht.1, htb⟩ hst
    · rw [hFᵣ hbt]
      rcases le_or_gt s b with hsb | hbs
      · rw [hFₗ hsb]
        refine (L.nested s ⟨hs.1, hsb⟩ b ⟨hab, le_rfl⟩ hsb).trans ?_
        rw [hImg]
        exact R.nested b ⟨le_rfl, hbc⟩ t ⟨hbt.le, ht.2⟩ hbt.le
      · rw [hFᵣ hbs]
        exact R.nested s ⟨hbs.le, hs.2⟩ t ⟨hbt.le, ht.2⟩ hst
  · rcases hbc.lt_or_eq with h | rfl
    · rw [hFᵣ h]
      exact R.terminal
    · rw [hFₗ le_rfl]
      exact L.terminal.trans R.terminal
  · intro u hu hNot
    have hub : u ≠ b := fun eq ↦ hNot (Finset.mem_insert.mpr (Or.inl eq))
    have hLu : u ∉ L.seams := fun h ↦ hNot (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hRu : u ∉ R.seams := fun h ↦ hNot (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
    rcases lt_or_gt_of_ne hub with h | h
    · obtain ⟨hUnit, hSlope⟩ := L.velocity_off_seams u ⟨hu.1, h⟩ hLu
      rw [hκL ⟨hu.1, h⟩, hFₗ h.le]
      refine ⟨hUnit, hSlope.congr_inseparable ?_⟩
      have hn : ∀ᶠ t in 𝓝[≠] u, t ∈ Iio b := nhdsWithin_le_nhds (Iio_mem_nhds h)
      filter_upwards [hn] with t ht z _
      exact Inseparable.of_eq (by rw [slope_def_module, slope_def_module,
        hFₗ (show t ≤ b from ht.le), hFₗ h.le])
    · obtain ⟨hUnit, hSlope⟩ := R.velocity_off_seams u ⟨h, hu.2⟩ hRu
      rw [hκR ⟨h, hu.2⟩, hFᵣ h]
      refine ⟨hUnit, hSlope.congr_inseparable ?_⟩
      have hn : ∀ᶠ t in 𝓝[≠] u, t ∈ Ioi b := nhdsWithin_le_nhds (Ioi_mem_nhds h)
      filter_upwards [hn] with t ht z _
      exact Inseparable.of_eq (by rw [slope_def_module, slope_def_module, hFᵣ ht, hFᵣ h])

private theorem prefix_control_eq_on {n : ℕ} {a : ℕ → ℝ} {q : ℕ → ℝ → ℂ} :
    EqOn (glueIntervalControls (n + 1) a q) (glueIntervalControls n a q) (Ioo (a 0) (a n)) := by
  intro t ht
  have hn : t ∉ Ioc (a n) (a (n + 1)) := fun hn ↦ (not_lt_of_ge hn.1.le) ht.2
  simp only [glueIntervalControls, Finset.sum_range_succ, indicator_of_notMem hn, add_zero]

/-- Realize a finite partition whose component controls already have
realizations for arbitrary terminal maps. -/
theorem exists_finiteDriverChain_of_partition {n : ℕ} {a : ℕ → ℝ} {q : ℕ → ℝ → ℂ}
    (ha : Monotone a)
    (hq : ∀ i < n, ∀ H, ExponentialDiskMap (a (i + 1)) H →
      Nonempty (FiniteDriverChain (a i) (a (i + 1)) (q i) H))
    {H : ℂ → ℂ} (hH : ExponentialDiskMap (a n) H) :
    Nonempty (FiniteDriverChain (a 0) (a n) (glueIntervalControls n a q) H) := by
  induction n generalizing H with
  | zero => exact ⟨FiniteDriverChain.singleton hH _⟩
  | succ n ih =>
    obtain ⟨R⟩ := hq n (Nat.lt_succ_self _) H hH
    obtain ⟨L⟩ := ih (fun i hi ↦ hq i (hi.trans (Nat.lt_succ_self _)))
      (R.map_on (a n) ⟨le_rfl, ha (Nat.le_succ n)⟩)
    exact ⟨FiniteDriverChain.join (ha (Nat.zero_le n)) (ha (Nat.le_succ n)) R L
      prefix_control_eq_on (fun _ ht ↦
        glueIntervalControls_eq_on_piece ha (Finset.mem_range.mpr (Nat.lt_succ_self n))
          ⟨ht.1, ht.2.le⟩)⟩

/-- Every finite step function of unit phases has a nested holomorphic realization. -/
theorem exists_finiteDriverChain_of_intervalControl {n : ℕ} {a : ℕ → ℝ}
    {ζ : ℕ → ℂ} (ha : Monotone a) (hζ : ∀ i ∈ Finset.range n, ‖ζ i‖ = 1)
    {H : ℂ → ℂ} (hH : ExponentialDiskMap (a n) H) :
    Nonempty (FiniteDriverChain (a 0) (a n) (intervalControl n a ζ) H) :=
  exists_finiteDriverChain_of_partition ha
    (fun i hi _ hHi ↦ ⟨FiniteDriverChain.constant (hζ i (Finset.mem_range.mpr hi)) hHi⟩) hH

end Zalcman
