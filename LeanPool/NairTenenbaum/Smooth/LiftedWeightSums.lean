/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Smooth.LiftedWeights

/-! # Comparing smooth and truncated sums under the squared-mass lift -/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

/-- Only positive arguments occur in the weight, so no sign assumption at zero
is needed for the scalar factors. -/
theorem weight_nonneg_of_positive {k r : ℕ} (γ : Fin k → Fin r → ℕ) (D : ℕ)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) {θ : Fin r → ℕ → ℝ}
    (hθ : ∀ i (n : ℕ+), 0 ≤ θ i n) (N : ℕ+) : 0 ≤ weight γ D F θ N := by
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (hF _) (Finset.prod_nonneg fun i _ => div_nonneg (hθ i _) (by positivity))

/-- An additional finite mass bound can be discarded from a truncated tuple sum. -/
theorem truncated_tupleWeight_sum_le {k r : ℕ} {F : ArithmeticMap k}
    (hF : ∀ n, 0 ≤ F n) {θ : Fin r → ℕ → ℝ} (hθ : ∀ i (n : ℕ+), 0 ≤ θ i n)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (D : ℕ) (N : ℕ+) (z : ℝ) :
    (∑ n ∈ (weightUpTo γ D N).filter (fun n => (weightedMass γ n : ℝ) ≤ z),
      pullback γ F n * ∏ i, θ i (n i) / (n i : ℝ)) ≤
      ∑ m ∈ positiveUpTo z, weight γ D F θ m := by
  classical
  have H := sum_weight_filter_eq γ hγ D F θ (fun m : ℕ+ => (m : ℝ) ≤ z) N
  simp only [PNat.mk_coe] at H
  refine H.symm.le.trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact (mem_positiveUpTo n z).mpr (Finset.mem_filter.mp hn).2
  · exact fun n _ _ => weight_nonneg_of_positive γ D hF hθ n

/-- Squaring the mass only reduces the truncated sum. -/
theorem truncated_liftedTupleWeight_sum_le {k r : ℕ} {F : ArithmeticMap k}
    (hF : ∀ n, 0 ≤ F n) {θ : Fin r → ℕ → ℝ} (hθ : ∀ i (n : ℕ+), 0 ≤ θ i n)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (D : ℕ) (N : ℕ+) (z : ℝ) :
    (∑ n ∈ (weightUpTo (liftedExponents γ) D N).filter
        (fun n => (weightedMass (liftedExponents γ) n : ℝ) ≤ z),
      rootTupleWeight (liftedExponents γ) (liftedArithmeticMap γ hγ F θ) (fun _ => X) n) ≤
      ∑ m ∈ positiveUpTo z, weight γ D F θ m := by
  classical
  simp_rw [rootTupleWeight_lifted]
  refine le_trans ?_ (truncated_tupleWeight_sum_le hF hθ γ hγ D N z)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hn, hz⟩
    rcases (mem_weightUpTo _ (liftedExponents_pos hγ) _ _ _).mp hn with ⟨hN, hd⟩
    rw [weightedMass_lifted] at hN hz
    have hm : weightedMass γ n ≤ weightedMass γ n ^ 2 := by
      have := weightedMass_pos γ n
      nlinarith
    exact Finset.mem_filter.mpr ⟨(mem_weightUpTo γ hγ D N n).mpr ⟨hm.trans hN, hd⟩,
      (by exact_mod_cast hm : (weightedMass γ n : ℝ) ≤ (weightedMass γ n ^ 2 : ℕ)).trans hz⟩
  · intro n _ _
    exact mul_nonneg (hF _) (Finset.prod_nonneg fun i _ => div_nonneg (hθ i _) (by positivity))

/-- The original tail embeds into the lifted tail with squared lower and upper
mass bounds. Smoothness and both dagger restrictions are retained. -/
theorem smooth_weight_tail_le_lifted {k r : ℕ} {F : ArithmeticMap k}
    (hF : ∀ n, 0 ≤ F n) {θ : Fin r → ℕ → ℝ} (hθ : ∀ i (n : ℕ+), 0 ≤ θ i n)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (D : ℕ) (N : ℕ+) (s : Finset ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∑ m ∈ (Finset.Icc 1 N).filter
        (fun m : ℕ+ => (m : ℕ) ∈ Nat.factoredNumbers s ∧ x < (m : ℝ)),
      weight γ D F θ m) ≤
      ∑ n ∈ (smoothWeightUpTo (liftedExponents γ) D s (N ^ 2)).filter
          (fun n => x ^ 2 < (weightedMass (liftedExponents γ) n : ℝ)),
        rootTupleWeight (liftedExponents γ) (liftedArithmeticMap γ hγ F θ) (fun _ => X) n := by
  classical
  rw [sum_weight_filter_eq γ hγ]
  simp_rw [rootTupleWeight_lifted]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    -- Reindexing retained a classical decision procedure for the whole predicate.
    rcases (@Finset.mem_filter (Tuple r)
      (fun a => weightedMass γ a ∈ Nat.factoredNumbers s ∧ x < (weightedMass γ a : ℝ))
      (fun _ => Classical.propDecidable _) _ _).mp hn with ⟨hn, hs, ht⟩
    change weightedMass γ n ∈ Nat.factoredNumbers s at hs
    change x < (weightedMass γ n : ℝ) at ht
    rcases (mem_weightUpTo γ hγ D N n).mp hn with ⟨hN, hd⟩
    apply Finset.mem_filter.mpr
    refine ⟨(mem_smoothWeightUpTo _ (liftedExponents_pos hγ) D s (N ^ 2) n).mpr ?_, ?_⟩
    · refine ⟨⟨?_, hd⟩, (weightedMass_mem_factoredNumbers_iff γ hγ n s).mp hs⟩
      simpa only [weightedMass_lifted, PNat.pow_coe] using Nat.pow_le_pow_left hN 2
    · simp only [weightedMass_lifted, Nat.cast_pow]
      nlinarith
  · intro n _ _
    exact mul_nonneg (hF _) (Finset.prod_nonneg fun i _ => div_nonneg (hθ i _) (by positivity))

end NairTenenbaum
