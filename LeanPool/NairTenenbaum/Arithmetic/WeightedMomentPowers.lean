/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Hooley.HooleyWeightedPrimeStep
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit

/-! # Fractional powers in the weighted prime step

Concavity supplies the finite weighted Hölder bound required when the
Dirichlet series uses `M_q(n)^(t/q)` with `0<t≤q`.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial

theorem weighted_sum_rpow_le {ι : Type*} (S : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hf : ∀ i ∈ S, 0 ≤ f i)
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (∑ i ∈ S, w i * f i ^ θ) ≤
      (∑ i ∈ S, w i) ^ (1 - θ) * (∑ i ∈ S, w i * f i) ^ θ := by
  let W := ∑ i ∈ S, w i
  have hW₀ : 0 ≤ W := sum_nonneg hw
  by_cases hW : W = 0
  · have hwi : ∀ i ∈ S, w i = 0 := (sum_eq_zero_iff_of_nonneg hw).mp hW
    rw [sum_eq_zero (fun i hi => by rw [hwi i hi, zero_mul])]
    exact mul_nonneg (Real.rpow_nonneg hW₀ _) (Real.rpow_nonneg
      (sum_nonneg fun i hi => mul_nonneg (hw i hi) (hf i hi)) _)
  have hWpos : 0 < W := lt_of_le_of_ne hW₀ (Ne.symm hW)
  have H := (Real.concaveOn_rpow hθ₀ hθ₁).le_map_sum (t := S)
    (w := fun i => w i / W) (p := f)
    (fun i hi => div_nonneg (hw i hi) hW₀)
    (by rw [← sum_div]; exact div_self hW)
    (fun i hi => hf i hi)
  simp only [smul_eq_mul] at H
  have Hleft : (∑ i ∈ S, w i / W * f i ^ θ) = (∑ i ∈ S, w i * f i ^ θ) / W := by
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    ring
  have Hright : (∑ i ∈ S, w i / W * f i) = (∑ i ∈ S, w i * f i) / W := by
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    ring
  rw [Hleft, Hright] at H
  have H' := (div_le_iff₀ hWpos).mp H
  apply H'.trans_eq
  rw [Real.div_rpow (sum_nonneg fun i hi => mul_nonneg (hw i hi) (hf i hi)) hW₀,
    Real.rpow_sub hWpos, Real.rpow_one]
  ring

/-- The explicit mixed error in the weighted prime recurrence. -/
noncomputable def hooleyPrimeErrorBound (Q : ℤ[X]) (q n : ℕ) : ℝ :=
  (Q.natDegree : ℝ) * ((Real.log 4 * Real.exp 2) * (4 : ℝ) ^ q *
    ((n.divisors.card : ℝ) ^ ((q : ℝ) / ((q : ℝ) - 1)) *
      hooleyMoment q n ^ (((q : ℝ) - 2) / ((q : ℝ) - 1))))

theorem hooleyPrimeErrorBound_nonneg (Q : ℤ[X]) (q n : ℕ) :
    0 ≤ hooleyPrimeErrorBound Q q n := by
  unfold hooleyPrimeErrorBound
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity)
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (hooleyMoment_nonneg q n) _)))

/-- The finite prime bound for the fractional moment used in the Dirichlet
series. Its main prime sum is left explicit for the prime-ideal input. -/
theorem root_weighted_hooleyMoment_rpow_prime_step {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) {q : ℕ} (hq : 1 < q)
    {σ θ : ℝ} (hσ : 1 ≤ σ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (∑ p ∈ S.filter (fun p => ¬p ∣ n), rootPrimeLogWeight Q σ p * hooleyMoment q (p * n) ^ θ) ≤
      (2 * hooleyMoment q n) ^ θ * (∑ p ∈ S, rootPrimeLogWeight Q σ p) +
      (∑ p ∈ S, rootPrimeLogWeight Q σ p) ^ (1 - θ) * hooleyPrimeErrorBound Q q n ^ θ := by
  let T := S.filter (fun p => ¬p ∣ n)
  have hT (p : ℕ) (hp : p ∈ T) : p.Prime := hS p (mem_filter.mp hp).1
  have hw (p : ℕ) (hp : p ∈ T) : 0 ≤ rootPrimeLogWeight Q σ p :=
    rootPrimeLogWeight_nonneg Q σ (hT p hp)
  have hmass : (∑ p ∈ T, rootPrimeLogWeight Q σ p) ≤ ∑ p ∈ S, rootPrimeLogWeight Q σ p := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro p hp _
    exact rootPrimeLogWeight_nonneg Q σ (hS p hp)
  have Hcross := weighted_sum_rpow_le T (rootPrimeLogWeight Q σ) (hooleyPrimeCrossMoment q n)
    hw (fun p _ => hooleyPrimeCrossMoment_nonneg q n p) hθ₀ hθ₁
  have Herr := root_weighted_hooleyCrossMoment_le hQ T hT n hq hσ
  have Herror : (∑ p ∈ T, rootPrimeLogWeight Q σ p * hooleyPrimeCrossMoment q n p ^ θ) ≤
      (∑ p ∈ S, rootPrimeLogWeight Q σ p) ^ (1 - θ) * hooleyPrimeErrorBound Q q n ^ θ := by
    apply Hcross.trans
    apply mul_le_mul
    · exact Real.rpow_le_rpow (sum_nonneg hw) hmass (by linarith)
    · exact Real.rpow_le_rpow
        (sum_nonneg fun p hp => mul_nonneg (hw p hp) (hooleyPrimeCrossMoment_nonneg q n p)) Herr hθ₀
    · exact Real.rpow_nonneg
        (sum_nonneg fun p hp => mul_nonneg (hw p hp) (hooleyPrimeCrossMoment_nonneg q n p)) _
    · exact Real.rpow_nonneg (sum_nonneg fun p hp => rootPrimeLogWeight_nonneg Q σ (hS p hp)) _
  calc
    _ ≤ ∑ p ∈ T, rootPrimeLogWeight Q σ p *
        ((2 * hooleyMoment q n) ^ θ + hooleyPrimeCrossMoment q n p ^ θ) := by
      apply sum_le_sum
      intro p hp
      rw [hooleyMoment_prime_mul (hT p hp) (mem_filter.mp hp).2 (by omega : 0 < q)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_add_le_add_rpow (mul_nonneg (by norm_num) (hooleyMoment_nonneg q n))
          (hooleyPrimeCrossMoment_nonneg q n p) hθ₀ hθ₁) (hw p hp)
    _ = (2 * hooleyMoment q n) ^ θ * (∑ p ∈ T, rootPrimeLogWeight Q σ p) +
        ∑ p ∈ T, rootPrimeLogWeight Q σ p * hooleyPrimeCrossMoment q n p ^ θ := by
      simp_rw [mul_add, sum_add_distrib]
      rw [mul_sum]
      congr 1
      apply sum_congr rfl
      intro p hp
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hmass
      (Real.rpow_nonneg (mul_nonneg (by norm_num) (hooleyMoment_nonneg q n)) _)) Herror

end NairTenenbaum
