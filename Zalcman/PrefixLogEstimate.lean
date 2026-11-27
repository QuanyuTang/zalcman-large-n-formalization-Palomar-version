/-
Authors: Yuyam Cheung, Tao Hu, Quanyu Tang
-/
module

public import Zalcman.MilinStability
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Estimating a low logarithmic coefficient from a nearly constant block

Selecting one least-squares error from each of a block of rows controls a
fixed low logarithmic coefficient. In these rows, the constant-coefficient
approximation also controls the Gram products.
-/

public section

namespace Zalcman.MilinCoefficients

open Finset
open scoped ComplexConjugate

private theorem gram_phaseError_le {a b α : ℂ} {r B : ℝ} (hα : ‖α‖ = 1)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) :
    ‖(r : ℂ) * a * conj b - 1‖ ^ 2 ≤
      3 * (B ^ 4 * (r - 1) ^ 2 + B ^ 2 * ‖a - α‖ ^ 2 + ‖b - α‖ ^ 2) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans ha
  have heq : (r : ℂ) * a * conj b - 1 =
      ((r : ℂ) - 1) * a * conj b + (a - α) * conj b + α * (conj b - conj α) := by
    have hunit : α * conj α = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hα]; norm_num
    calc
      _ = (((r : ℂ) - 1) * a * conj b + (a - α) * conj b + α * (conj b - conj α)) +
          (α * conj α - 1) := by ring
      _ = _ := by rw [hunit, sub_self, add_zero]
  have h₁ : ‖((r : ℂ) - 1) * a * conj b‖ ≤ B ^ 2 * |r - 1| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, norm_mul, norm_mul,
      Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |r - 1| * B * B := mul_le_mul (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
        hb (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have h₂ : ‖(a - α) * conj b‖ ≤ B * ‖a - α‖ := by
    rw [norm_mul, Complex.norm_conj, mul_comm B]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have h₃ : ‖α * (conj b - conj α)‖ = ‖b - α‖ := by
    rw [norm_mul, ← map_sub, Complex.norm_conj, hα, one_mul]
  have htri : ‖(r : ℂ) * a * conj b - 1‖ ≤ B ^ 2 * |r - 1| + B * ‖a - α‖ + ‖b - α‖ := by
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h₁ h₂)) h₃.le)
  have hh := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hsq (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    nlinarith only [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
  refine hh.trans ((hsq _ _ _).trans_eq ?_)
  rw [mul_pow, mul_pow, sq_abs]
  ring

private theorem norm_sub_sq_le_two (a b c : ℂ) :
    ‖a - c‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b - c‖ ^ 2 := by
  have hl : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
    rw [← sub_add_sub_cancel a b c]
    exact norm_add_le _ _
  have hs := pow_le_pow_left₀ (norm_nonneg _) hl 2
  nlinarith only [hs, sq_nonneg (‖a - b‖ - ‖b - c‖)]

/-- A finite set of rows bounds the squared error of any logarithmic coefficient in the prefix. -/
theorem mul_norm_logCoeff_sub_one_sq_le {d : MilinCoefficients} {n J k : ℕ}
    (hJn : 2 * J ≤ n) (hk : 0 < k) (hkJ : k ≤ J) {α : ℂ} (hα : ‖α‖ = 1)
    {B E R S : ℝ} (hB : ∀ i < n, ‖d.c i‖ ≤ B)
    (hE : (∑ i ∈ range n, ‖d.c i - α‖ ^ 2) ≤ E)
    (hR : (∑ j ∈ Ico J (2 * J), ((j : ℝ) / d.partialMass j - 1) ^ 2) ≤ R)
    (hS : (∑ j ∈ Ico J (2 * J), d.remainder j) ≤ S) :
    (J : ℝ) * ‖d.t k - 1‖ ^ 2 ≤ 2 * S + 6 * (B ^ 4 * R + (B ^ 2 + 1) * E) := by
  let I := Ico J (2 * J)
  let w (i : ℕ) := ‖d.c i - α‖ ^ 2
  have hbase : (∑ j ∈ I, w j) ≤ E :=
    (sum_le_sum_of_subset_of_nonneg (fun _ hj => mem_range.mpr ((mem_Ico.mp hj).2.trans_le hJn))
      (fun _ _ _ => sq_nonneg _)).trans hE
  have hshift : (∑ j ∈ I, w (j - k)) ≤ E := by
    have hsub : I.image (fun j => j - k) ⊆ range n := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      have hj' := (mem_Ico.mp hj).2
      exact mem_range.mpr (by omega)
    have hinj : Set.InjOn (fun j => j - k) (↑I : Set ℕ) := by
      intro i hi j hj he
      have h₁ := (mem_Ico.mp (mem_coe.mp hi)).1
      have h₂ := (mem_Ico.mp (mem_coe.mp hj)).1
      change i - k = j - k at he
      omega
    have hle := sum_le_sum_of_subset_of_nonneg (f := w) hsub (fun _ _ _ => sq_nonneg _)
    rw [sum_image hinj] at hle
    exact hle.trans hE
  have hpoint (j : ℕ) (hj : j ∈ I) : ‖d.t k - 1‖ ^ 2 ≤ 2 * d.remainder j +
      6 * (B ^ 4 * ((j : ℝ) / d.partialMass j - 1) ^ 2 + B ^ 2 * w j + w (j - k)) := by
    obtain ⟨hjlo, hjhi⟩ := mem_Ico.mp hj
    have hj₀ : 0 < j := by omega
    have he := d.remainder_eq_sum_norm_sq hj₀
    simp only [Complex.ofReal_div, Complex.ofReal_natCast] at he
    let v := ((j : ℂ) / (d.partialMass j : ℂ)) * d.c j * conj (d.c (j - k))
    have hr : ‖d.t k - v‖ ^ 2 ≤ d.remainder j := by
      rw [he]
      have hp := single_le_sum (s := range j)
        (f := fun i => ‖d.t (j - i) - (j : ℂ) / (d.partialMass j : ℂ) * d.c j * conj (d.c i)‖ ^ 2)
        (fun i _ => sq_nonneg _) (mem_range.mpr (show j - k < j by omega))
      rw [show j - (j - k) = k by omega] at hp
      exact hp
    have hv : ‖v - 1‖ ^ 2 ≤
        3 * (B ^ 4 * ((j : ℝ) / d.partialMass j - 1) ^ 2 + B ^ 2 * w j + w (j - k)) := by
      simpa only [v, w, Complex.ofReal_div, Complex.ofReal_natCast] using
        gram_phaseError_le (r := (j : ℝ) / d.partialMass j) hα (hB j (by omega)) (hB (j - k) (by omega))
    linarith only [norm_sub_sq_le_two (d.t k) v 1, hr, hv]
  have hCard : I.card = J := by dsimp [I]; rw [Nat.card_Ico]; omega
  calc
    _ = ∑ j ∈ I, ‖d.t k - 1‖ ^ 2 := by simp only [sum_const, hCard, nsmul_eq_mul]
    _ ≤ ∑ j ∈ I, (2 * d.remainder j +
        6 * (B ^ 4 * ((j : ℝ) / d.partialMass j - 1) ^ 2 + B ^ 2 * w j + w (j - k))) :=
      sum_le_sum hpoint
    _ = 2 * (∑ j ∈ I, d.remainder j) +
        6 * (B ^ 4 * (∑ j ∈ I, ((j : ℝ) / d.partialMass j - 1) ^ 2) +
          B ^ 2 * (∑ j ∈ I, w j) + ∑ j ∈ I, w (j - k)) := by
      simp only [sum_add_distrib, ← mul_sum]
    _ ≤ 2 * S + 6 * (B ^ 4 * R + B ^ 2 * E + E) :=
      add_le_add (mul_le_mul_of_nonneg_left hS (by norm_num))
        (mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hR (by positivity))
            (mul_le_mul_of_nonneg_left hbase (sq_nonneg B))) hshift) (by norm_num))
    _ = _ := by ring

/-- Near saturation controls the sum of squared mass-ratio errors on the selected rows. -/
theorem sum_partialMass_ratio_error_Ico_le {d : MilinCoefficients} {n J : ℕ}
    (hn : 6 ≤ n) (hJ : 0 < J) (hJn : 2 * J ≤ n) (hT : ∀ j, 0 ≤ d.milinSum j)
    (hD : (n : ℝ) - ‖d.squareCoeff n‖ ≤ 3) :
    (∑ j ∈ Ico J (2 * J), ((j : ℝ) / d.partialMass j - 1) ^ 2) ≤
      (6912 * 288 : ℝ) * ((n : ℝ) - ‖d.squareCoeff n‖) := by
  let D : ℝ := n - ‖d.squareCoeff n‖
  let C : ℝ := 6912 * 288
  have hD₀ : 0 ≤ D := sub_nonneg.mpr (d.norm_squareCoeff_le_index (by omega) (hT n))
  have hJR : 0 < (J : ℝ) := by exact_mod_cast hJ
  calc
    _ ≤ ∑ _j ∈ Ico J (2 * J), C * D / (J : ℝ) := by
      apply sum_le_sum
      intro j hj
      have hj' := mem_Ico.mp hj
      have hj₀ : 0 < j := by omega
      have hjn : j ≤ n := by omega
      let A := d.partialMass j
      have hA : 0 < A := d.partialMass_pos hj₀
      have hM : (j : ℝ) ≤ 288 * A := d.index_le_mul_partialMass hT hn hj₀ hjn hD
      have hJj : (J : ℝ) ≤ j := by exact_mod_cast hj'.1
      have hLower : (J : ℝ) / 288 ≤ A := by
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 288)).mpr
        linarith only [hM, hJj]
      calc
        _ = (((j : ℝ) - A) ^ 2 / A) / A := by
          change ((j : ℝ) / A - 1) ^ 2 = (((j : ℝ) - A) ^ 2 / A) / A
          field_simp [hA.ne']
        _ ≤ 6912 * D / A := div_le_div_of_nonneg_right
          (d.partialMass_deficit_sq_div_le hT hn hj₀ hjn hD) hA.le
        _ ≤ 6912 * D / ((J : ℝ) / 288) := div_le_div_of_nonneg_left (by positivity) (by positivity) hLower
        _ = _ := by dsimp [C]; ring
    _ = _ := by
      simp only [sum_const, Nat.card_Ico, show 2 * J - J = J by omega, nsmul_eq_mul]
      field_simp <;> ring

/-- The weighted least-squares bound controls the unweighted sum on low rows. -/
theorem sum_remainder_Ico_le {d : MilinCoefficients} {n J : ℕ} (hJ : 0 < J)
    (hJn : 2 * J ≤ n) (hJSq : J ^ 2 ≤ n)
    (hWeighted : ∑ i ∈ range (n - 1), d.remainder (i + 1) / ((i : ℝ) + 1) ^ 2 ≤
      8 * ((n : ℝ) - ‖d.squareCoeff n‖) / n) :
    (∑ j ∈ Ico J (2 * J), d.remainder j) ≤ 32 * ((n : ℝ) - ‖d.squareCoeff n‖) := by
  let w (i : ℕ) := d.remainder (i + 1) / ((i : ℝ) + 1) ^ 2
  have hw (i : ℕ) : 0 ≤ w i := div_nonneg (d.remainder_nonneg (by omega)) (sq_nonneg _)
  have hW : (∑ j ∈ Ico J (2 * J), w (j - 1)) ≤ 8 * ((n : ℝ) - ‖d.squareCoeff n‖) / n := by
    rw [sum_Ico_eq_sum_range, show 2 * J - J = J by omega]
    change (∑ i ∈ range J, w (J + i - 1)) ≤ _
    have hIdx (i : ℕ) : J + i - 1 = (J - 1) + i := by omega
    have h := sum_range_add w (J - 1) J
    have hle := sum_le_sum_of_subset_of_nonneg (f := w)
      (range_mono (show J - 1 + J ≤ n - 1 by omega)) (fun i _ _ => hw i)
    rw [h] at hle
    have hNonneg : 0 ≤ ∑ i ∈ range (J - 1), w i := sum_nonneg (fun i _ => hw i)
    change (∑ i ∈ range (n - 1), w i) ≤ _ at hWeighted
    calc
      _ = ∑ i ∈ range J, w ((J - 1) + i) := sum_congr rfl (fun i _ ↦ congrArg w (hIdx i))
      _ ≤ _ := by linarith only [hle, hNonneg, hWeighted]
  have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hJCast : (J : ℝ) ^ 2 ≤ n := by exact_mod_cast hJSq
  calc
    _ ≤ ∑ j ∈ Ico J (2 * J), (4 * (n : ℝ)) * w (j - 1) := by
      apply sum_le_sum
      intro j hj
      have hj' := mem_Ico.mp hj
      have hj₀ : 0 < j := by omega
      have hjR : (0 : ℝ) < j := by positivity
      have hJs : (j : ℝ) ≤ 2 * (J : ℝ) := by exact_mod_cast (show j ≤ 2 * J by omega)
      have hR : (j : ℝ) ^ 2 ≤ 4 * n := by
        have hpow := pow_le_pow_left₀ hjR.le hJs 2
        nlinarith only [hpow, hJCast]
      have hwj : w (j - 1) = d.remainder j / (j : ℝ) ^ 2 := by
        simp only [w, Nat.sub_add_cancel (show 1 ≤ j by omega), Nat.cast_sub (show 1 ≤ j by omega),
          Nat.cast_one, sub_add_cancel]
      rw [hwj, ← mul_div_assoc]
      apply (le_div_iff₀ (pow_pos hjR 2)).mpr
      simpa only [mul_comm (d.remainder j)] using mul_le_mul_of_nonneg_right hR (d.remainder_nonneg hj₀)
    _ = (4 * (n : ℝ)) * ∑ j ∈ Ico J (2 * J), w (j - 1) := by rw [mul_sum]
    _ ≤ (4 * (n : ℝ)) * (8 * ((n : ℝ) - ‖d.squareCoeff n‖) / n) :=
      mul_le_mul_of_nonneg_left hW (by positivity)
    _ = _ := by field_simp <;> ring

end Zalcman.MilinCoefficients
