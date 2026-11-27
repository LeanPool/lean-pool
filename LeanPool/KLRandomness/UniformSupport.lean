/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.UniformSupportCount
public import LeanPool.KLRandomness.FiniteProbability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Intersection moments of an actual uniform fixed-size support

The one- and two-coordinate inclusion counts yield the mean and a variance
bound for intersection with any unread set.  A finite Markov argument then
gives the support tail estimate used by Lemma 4.  All averages are over the
actual finite type `Support M m`, not supplied moment hypotheses.
-/

@[expose] public section

namespace Klr.UniformSupport

open FiniteProbability
open scoped BigOperators

variable {M m : ℕ}

/-- The indicator that the sampled support contains a fixed pool position. -/
def inclusion (a : Fin M) (S : Support M m) : ℝ := if a ∈ S.val then 1 else 0

theorem probability_contains_one (hm1 : 1 ≤ m) (hmM : m ≤ M) (a : Fin M) :
    probability {S : Support M m | a ∈ S.val} = (m : ℝ) / M := by
  rw [probability_eq_card, card_contains_one hm1, card_support]
  exact choose_ratio_one hm1 hmM

theorem average_inclusion (hm1 : 1 ≤ m) (hmM : m ≤ M) (a : Fin M) :
    average (inclusion (m := m) a) = (m : ℝ) / M := by
  calc
    average (inclusion (m := m) a) = probability {S : Support M m | a ∈ S.val} := by
      unfold probability
      apply average_congr
      intro S
      by_cases h : a ∈ S.val <;> simp [inclusion, h]
    _ = _ := probability_contains_one hm1 hmM a

theorem probability_contains_pair (hm2 : 2 ≤ m) (hmM : m ≤ M)
    (a b : Fin M) (hab : a ≠ b) :
    probability {S : Support M m | a ∈ S.val ∧ b ∈ S.val} =
      ((m : ℝ) * (m - 1)) / ((M : ℝ) * (M - 1)) := by
  rw [probability_eq_card, card_contains_pair hm2 a b hab, card_support]
  exact choose_ratio_pair hm2 hmM

theorem average_inclusion_mul_le (hm2 : 2 ≤ m) (hmM : m ≤ M) (a b : Fin M) :
    average (fun S : Support M m => inclusion a S * inclusion b S) ≤
      ((m : ℝ) / M) ^ 2 + if a = b then (m : ℝ) / M else 0 := by
  by_cases hab : a = b
  · subst b
    have he : (fun S : Support M m => inclusion a S * inclusion a S) = inclusion a := by
      funext S
      simp [inclusion]
    rw [he, average_inclusion (by omega) hmM]
    simp only [ite_true]
    nlinarith [sq_nonneg ((m : ℝ) / M)]
  · have he : average (fun S : Support M m => inclusion a S * inclusion b S) =
        probability {S : Support M m | a ∈ S.val ∧ b ∈ S.val} := by
      unfold probability
      apply average_congr
      intro S
      by_cases ha : a ∈ S.val <;> by_cases hb : b ∈ S.val <;> simp [inclusion, ha, hb]
    rw [he, probability_eq_card, card_contains_pair hm2 a b hab, card_support]
    simpa only [ite_eq_right hab, add_zero] using choose_ratio_pair_le_sq hm2 hmM

/-- The size of the sampled support's intersection with the fixed unread set. -/
def intersectionSize (D : Finset (Fin M)) (S : Support M m) : ℝ := (S.val ∩ D).card

theorem intersectionSize_nonneg (D : Finset (Fin M)) (S : Support M m) :
    0 ≤ intersectionSize D S := Nat.cast_nonneg _

theorem intersectionSize_eq_sum (D : Finset (Fin M)) (S : Support M m) :
    intersectionSize D S = ∑ a : D, inclusion a.val S := by
  rw [Finset.sum_coe_sort D (fun a => inclusion a S)]
  unfold intersectionSize
  simp only [inclusion, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext a
  simp [and_comm]

/-- The exact mean intersection size `m*|D|/M`. -/
noncomputable def mean (D : Finset (Fin M)) (m : ℕ) : ℝ := (m : ℝ) * D.card / M

theorem average_intersectionSize (hm1 : 1 ≤ m) (hmM : m ≤ M) (D : Finset (Fin M)) :
    average (intersectionSize (m := m) D) = mean D m := by
  change average (fun S : Support M m => intersectionSize D S) = _
  simp_rw [intersectionSize_eq_sum]
  rw [average_sum]
  simp only [average_inclusion hm1 hmM, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul]
  unfold mean
  ring

/-- A sufficient second-moment estimate, derived from negative pair correlations. -/
theorem average_intersectionSize_sq_le (hm2 : 2 ≤ m) (hmM : m ≤ M)
    (D : Finset (Fin M)) :
    average (fun S : Support M m => (intersectionSize D S) ^ 2) ≤ mean D m ^ 2 + mean D m := by
  have he (S : Support M m) : (intersectionSize D S)^2 =
      ∑ a : D, ∑ b : D, inclusion a.val S * inclusion b.val S := by
    rw [intersectionSize_eq_sum, pow_two, Finset.sum_mul_sum]
  simp_rw [he]
  rw [average_sum]
  simp_rw [average_sum]
  calc
    _ ≤ ∑ a : D, ∑ b : D,
        (((m : ℝ) / M)^2 + if a.val = b.val then (m : ℝ) / M else 0) := by
      apply Finset.sum_le_sum
      intro a _
      exact Finset.sum_le_sum fun b _ => average_inclusion_mul_le hm2 hmM a.val b.val
    _ = mean D m ^ 2 + mean D m := by
      have hinner (a : D) :
          (∑ b : D, (((m : ℝ) / M)^2 + if a.val = b.val then (m : ℝ) / M else 0)) =
            (D.card : ℝ) * ((m : ℝ) / M)^2 + (m : ℝ) / M := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_coe, nsmul_eq_mul, Subtype.val_inj]
        simp
      simp_rw [hinner]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      unfold mean
      ring

/-- The variance of sampling without replacement is at most the mean. -/
theorem variance_le_mean (hm2 : 2 ≤ m) (hmM : m ≤ M) (D : Finset (Fin M)) :
    average (fun S : Support M m => (intersectionSize D S - mean D m)^2) ≤ mean D m := by
  have : Nonempty (Support M m) := support_nonempty hmM
  have he : (fun S : Support M m => (intersectionSize D S - mean D m)^2) =
      fun S => (intersectionSize D S)^2 - (2 * mean D m) * intersectionSize D S + mean D m^2 := by
    funext S
    ring
  rw [he, average_add, average_sub, average_const_mul, average_const,
    average_intersectionSize (by omega) hmM]
  have hs := average_intersectionSize_sq_le hm2 hmM D
  nlinarith

/-- Chebyshev's bound for an intersection smaller than `2r`, when its mean is at least `4r`. -/
theorem probability_small_intersection_le (hm2 : 2 ≤ m) (hmM : m ≤ M)
    (D : Finset (Fin M)) (r : ℕ) (hmean : 0 < mean D m)
    (hr : 4 * (r : ℝ) ≤ mean D m) :
    probability {S : Support M m | (S.val ∩ D).card < 2 * r} ≤ 4 / mean D m := by
  have : Nonempty (Support M m) := support_nonempty hmM
  have hhalf : 0 < (mean D m / 2)^2 := sq_pos_of_pos (by positivity)
  have hsub : {S : Support M m | (S.val ∩ D).card < 2 * r} ⊆
      {S | (mean D m / 2)^2 ≤ (intersectionSize D S - mean D m)^2} := by
    intro S hS
    change (S.val ∩ D).card < 2 * r at hS
    change (mean D m / 2)^2 ≤ (intersectionSize D S - mean D m)^2
    have hS' : intersectionSize D S < 2 * (r : ℝ) := by
      unfold intersectionSize
      exact_mod_cast hS
    have hneg : intersectionSize D S - mean D m ≤ -(mean D m / 2) := by linarith
    have hN := intersectionSize_nonneg D S
    nlinarith
  calc
    _ ≤ probability {S : Support M m |
        (mean D m / 2)^2 ≤ (intersectionSize D S - mean D m)^2} := probability_mono hsub
    _ ≤ average (fun S : Support M m => (intersectionSize D S - mean D m)^2) /
        (mean D m / 2)^2 :=
      probability_le_average_div _ (fun _ => sq_nonneg _) _ hhalf
    _ ≤ mean D m / (mean D m / 2)^2 :=
      div_le_div_of_nonneg_right (variance_le_mean hm2 hmM D) hhalf.le
    _ = 4 / mean D m := by field_simp; ring

/-- A dense unread set gives the uniform support tail bound used in Lemma 4. -/
theorem probability_small_intersection_le_density (hm2 : 2 ≤ m) (hmM : m ≤ M)
    (D : Finset (Fin M)) (r : ℕ) (τ : ℝ) (hτ : 0 < τ)
    (hD : τ * M ≤ (D.card : ℝ)) (hr : 4 * (r : ℝ) ≤ τ * m) :
    probability {S : Support M m | (S.val ∩ D).card < 2 * r} ≤ 4 / (τ * m) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hm : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmean : τ * m ≤ mean D m := by
    unfold mean
    apply (le_div_iff₀ hM).mpr
    nlinarith [mul_le_mul_of_nonneg_left hD hm.le]
  have hpos : 0 < τ * (m : ℝ) := mul_pos hτ hm
  exact (probability_small_intersection_le hm2 hmM D r (hpos.trans_le hmean)
    (hr.trans hmean)).trans (div_le_div_of_nonneg_left (by norm_num) hpos hmean)

end Klr.UniformSupport
