/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyMoments
public import Mathlib.MeasureTheory.Group.Integral

/-! # The moment recurrence when adjoining a new prime

The exact identity `M_q(pn)=2 M_q(n)+E_q(n,p)` is the starting point for
the differential inequality in the weighted Hooley mean estimate.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real MeasureTheory

theorem hooleyWindow_prime_mul {p n : ℕ} (hp : p.Prime) (hpn : ¬p ∣ n) (u : ℝ) :
    hooleyWindow (p * n) u = hooleyWindow n u + hooleyWindow n (u - Real.log p) := by
  unfold hooleyWindow
  rw [divisorWindow_mul (hp.coprime_iff_not_dvd.mpr hpn), hp.divisors]
  simp [hp.ne_one.symm]

/-- Mixed moments of a window and its translate. -/
noncomputable def hooleyMixedMoment (j k n : ℕ) (a : ℝ) : ℝ :=
  ∫ u : ℝ, hooleyWindow n u ^ j * hooleyWindow n (u - a) ^ k

theorem hooleyMixedMoment_nonneg (j k n : ℕ) (a : ℝ) : 0 ≤ hooleyMixedMoment j k n a :=
  integral_nonneg fun u => mul_nonneg (pow_nonneg (hooleyWindow_nonneg n u) j)
    (pow_nonneg (hooleyWindow_nonneg n (u - a)) k)

theorem integrable_hooleyMixedMoment (j k n : ℕ) (a : ℝ) (hjk : 0 < j + k) :
    Integrable (fun u => hooleyWindow n u ^ j * hooleyWindow n (u - a) ^ k) := by
  by_cases hj : 0 < j
  · apply (integrable_hooleyWindow_pow n hj).mul_bdd (c := (n.divisors.card : ℝ) ^ k)
      (((measurable_hooleyWindow n).comp (measurable_id.sub_const a)).pow_const
          k).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun u => by
      change ‖hooleyWindow n (u - a) ^ k‖ ≤ (n.divisors.card : ℝ) ^ k
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hooleyWindow_nonneg n (u - a)) k)]
      exact pow_le_pow_left₀ (hooleyWindow_nonneg n (u - a)) (hooleyWindow_le_card n (u - a)) k
  · have hj₀ : j = 0 := by omega
    have hk : 0 < k := by omega
    simpa only [hj₀, pow_zero, one_mul] using (integrable_hooleyWindow_pow n hk).comp_sub_right a

@[simp] theorem hooleyMixedMoment_zero_left (q n : ℕ) (a : ℝ) :
    hooleyMixedMoment 0 q n a = hooleyMoment q n := by
  simp only [hooleyMixedMoment, pow_zero, one_mul, hooleyMoment]
  exact integral_sub_right_eq_self (fun u => hooleyWindow n u ^ q) a

@[simp] theorem hooleyMixedMoment_zero_right (q n : ℕ) (a : ℝ) :
    hooleyMixedMoment q 0 n a = hooleyMoment q n := by
  simp only [hooleyMixedMoment, pow_zero, mul_one, hooleyMoment]

/-- The complete binomial expansion, with integrability of every term proved. -/
theorem hooleyMoment_prime_mul_expansion {p n q : ℕ}
    (hp : p.Prime) (hpn : ¬p ∣ n) (hq : 0 < q) :
    hooleyMoment q (p * n) = ∑ j ∈ range (q + 1),
      hooleyMixedMoment j (q - j) n (Real.log p) * (q.choose j : ℝ) := by
  unfold hooleyMoment
  simp_rw [hooleyWindow_prime_mul hp hpn, add_pow]
  have hi (j : ℕ) (hj : j ∈ range (q + 1)) :
      Integrable (fun u => hooleyWindow n u ^ j *
        hooleyWindow n (u - Real.log p) ^ (q - j) * (q.choose j : ℝ)) := by
    have hjq := mem_range.mp hj
    exact (integrable_hooleyMixedMoment j (q - j) n (Real.log p) (by omega)).mul_const _
  rw [integral_finsetSum _ hi]
  simp only [integral_mul_const, hooleyMixedMoment]

/-- The positive mixed terms, with the two pure powers removed. -/
noncomputable def hooleyPrimeCrossMoment (q n p : ℕ) : ℝ :=
  ∑ j ∈ Ico 1 q, hooleyMixedMoment j (q - j) n (Real.log p) * (q.choose j : ℝ)

theorem hooleyPrimeCrossMoment_nonneg (q n p : ℕ) : 0 ≤ hooleyPrimeCrossMoment q n p :=
  sum_nonneg fun _ _ => mul_nonneg (hooleyMixedMoment_nonneg _ _ _ _) (Nat.cast_nonneg _)

/-- The recurrence used before equation (2.10) of the weighted mean proof. -/
theorem hooleyMoment_prime_mul {p n q : ℕ}
    (hp : p.Prime) (hpn : ¬p ∣ n) (hq : 0 < q) :
    hooleyMoment q (p * n) = 2 * hooleyMoment q n + hooleyPrimeCrossMoment q n p := by
  rw [hooleyMoment_prime_mul_expansion hp hpn hq, sum_range_succ,
    sum_range_eq_add_Ico _ hq]
  simp only [Nat.sub_zero, Nat.sub_self, Nat.choose_zero_right, Nat.choose_self,
    Nat.cast_one, mul_one, hooleyMixedMoment_zero_left, hooleyMixedMoment_zero_right]
  unfold hooleyPrimeCrossMoment
  ring

end NairTenenbaum
