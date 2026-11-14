/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Sieve.BadPrimeMass

/-! # Exponential moments for the full bad-prime tuple kernel

The mass lost during whole-prime-power removal is retained in a small positive
moment. This allows a tail estimate for the original prefix mass, without a
bounded-valuation assumption at bad primes.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

theorem auxiliary_tupleLCM_moment_le {k r G : ℕ} {A B ε β : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (γ : Fin k → Fin r → ℕ) (n : Tuple r)
    (hG : 0 < G) (hr : r ≤ G) :
    ((∏ i, auxiliary A B ε (totalExponent γ i) (n i)) / (tupleLCM n : ℝ)) *
      (weightedMass γ n : ℝ) ^ β ≤
      ∏ i, fractionalAuxiliary A B ε (1 / (G : ℝ) - (totalExponent γ i : ℝ) * β)
        (totalExponent γ i) (n i) := by
  have H := mul_le_mul_of_nonneg_right (auxiliary_prod_div_tupleLCM_le (ε := ε) hA hB
    (totalExponent γ) n hG hr) (Real.rpow_nonneg (Nat.cast_nonneg (weightedMass γ n)) β)
  rw [weightedMass_rpow, ← Finset.prod_mul_distrib] at H
  rw [weightedMass_rpow]
  apply H.trans_eq
  apply Finset.prod_congr rfl
  intro i _
  have hn : (0 : ℝ) < n i := by exact_mod_cast (n i).pos
  have hp₁ := (Real.rpow_pos_of_pos hn (1 / (G : ℝ))).ne'
  have hp₂ := (Real.rpow_pos_of_pos hn ((totalExponent γ i : ℝ) * β)).ne'
  unfold fractionalAuxiliary
  rw [Real.rpow_sub hn]
  field_simp

/-- Uniform finite moment bound with an arbitrary fixed exponent gap. -/
theorem auxiliary_tupleLCM_moment_sum_le {k r G : ℕ} {A B ε β σ : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hσ : σ < 0) (hG : 0 < G) (hr : r ≤ G)
    (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, (totalExponent γ i : ℝ) * (ε + β) - 1 / (G : ℝ) ≤ σ)
    (s : Finset ℕ) (S : Finset (Tuple r)) (N : ℕ+)
    (hbox : ∀ n ∈ S, ∀ i, n i ≤ N)
    (hs : ∀ n ∈ S, ∀ i, (n i : ℕ) ∈ Nat.factoredNumbers s) :
    (∑ n ∈ S, ((∏ i, auxiliary A B ε (totalExponent γ i) (n i)) / (tupleLCM n : ℝ)) *
      (weightedMass γ n : ℝ) ^ β) ≤
      (B / (1 - (2 : ℝ) ^ σ)) ^ (G * (s.filter Nat.Prime).card) := by
  exact (Finset.sum_le_sum (fun n _ =>
    auxiliary_tupleLCM_moment_le hA (zero_le_one.trans hB) γ n hG hr)).trans
      (sum_prod_fractionalAuxiliary_le hA hB hε hσ hr (totalExponent γ)
        (fun i => 1 / (G : ℝ) - (totalExponent γ i : ℝ) * β)
        (fun i => by nlinarith [hγ i]) s S N hbox hs)

/-- Uniform bound for moments of the full bad-prime tuple kernel. -/
noncomputable def badPrimeMomentBound (B : ℝ) (g D : ℕ) : ℝ :=
  ((D ^ 3) ^ D.primeFactors.card : ℕ) *
    (B / (1 - (2 : ℝ) ^ (-3 / (4 * (g : ℝ))))) ^ (g * D.primeFactors.card)

theorem badPrimeMomentBound_pos {B : ℝ} (hB : 0 < B) {g D : ℕ} (hg : 0 < g) (hD : 0 < D) :
    0 < badPrimeMomentBound B g D := by
  have hσ : -3 / (4 * (g : ℝ)) < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hd : 0 < 1 - (2 : ℝ) ^ (-3 / (4 * (g : ℝ))) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hσ)
  exact mul_pos (by exact_mod_cast pow_pos (pow_pos hD 3) D.primeFactors.card)
    (pow_pos (div_pos hB hd) _)

theorem badPrime_moment_exponent_gap {g η : ℕ} (hg : 0 < g) (hη : η ≤ g)
    {ε β : ℝ} (hεβ : 0 ≤ ε + β) (hsmall : (g : ℝ) ^ 2 * (ε + β) ≤ 1 / 4) :
    (η : ℝ) * (ε + β) - 1 / (g : ℝ) ≤ -3 / (4 * (g : ℝ)) := by
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  have hge : (g : ℝ) * (ε + β) ≤ (1 / 4) / (g : ℝ) :=
    (le_div_iff₀ hg₀).mpr (by nlinarith)
  calc
    _ ≤ ((1 / 4) / (g : ℝ)) - 1 / (g : ℝ) :=
      sub_le_sub_right ((mul_le_mul_of_nonneg_right (by exact_mod_cast hη) hεβ).trans hge) _
    _ = _ := by ring

/-- Every bad-prime valuation is included, with a constant independent of the
cutoff and of the chosen small moment exponent. -/
theorem PolynomialSystem.badPrimeTupleKernel_moment_sum_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε β : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hβ : 0 ≤ β)
    (hg : 0 < P.total.natDegree) (hsmall : (P.total.natDegree : ℝ) ^ 2 * (ε + β) ≤ 1 / 4)
    (S : Finset (Tuple r)) (N : ℕ+) (hbox : ∀ n ∈ S, ∀ i, n i ≤ N)
    (hs : ∀ n ∈ S, ∀ i, (n i : ℕ) ∈ Nat.factoredNumbers P.badDiscriminant.primeFactors) :
    (∑ n ∈ S, badPrimeTupleKernel A B ε (totalExponent P.exponent) P.radical n *
      (weightedMass P.exponent n : ℝ) ^ β) ≤ badPrimeMomentBound B P.total.natDegree
          P.badDiscriminant := by
  let K : ℝ := ((P.badDiscriminant ^ 3) ^ P.badDiscriminant.primeFactors.card : ℕ)
  have hσ : -3 / (4 * (P.total.natDegree : ℝ)) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have H := auxiliary_tupleLCM_moment_sum_le hA hB hε hσ hg P.factor_count_le_degree P.exponent
    (fun i => badPrime_moment_exponent_gap hg (P.totalExponent_le_degree i) (by positivity) hsmall)
    P.badDiscriminant.primeFactors S N hbox hs
  rw [Finset.filter_eq_self.mpr (fun _ hp => Nat.prime_of_mem_primeFactors hp)] at H
  calc
    _ ≤ ∑ n ∈ S, K * (((∏ i, auxiliary A B ε (totalExponent P.exponent i) (n i)) /
        (tupleLCM n : ℝ)) * (weightedMass P.exponent n : ℝ) ^ β) := by
      apply Finset.sum_le_sum
      intro n hn
      have hρ : (rootCount P.radical (tupleLCM n) : ℝ) ≤ K := by
        dsimp only [K]
        exact_mod_cast P.radical_rootCount_bad_supported (tupleLCM_mem_factoredNumbers n _ (hs n
            hn))
      have haux : 0 ≤ ((∏ i, auxiliary A B ε (totalExponent P.exponent i) (n i)) /
          (tupleLCM n : ℝ)) * (weightedMass P.exponent n : ℝ) ^ β :=
        mul_nonneg (div_nonneg (Finset.prod_nonneg (fun i _ => auxiliary_nonneg hA
            (zero_le_one.trans hB) _ _))
          (Nat.cast_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have H' := mul_le_mul_of_nonneg_right hρ haux
      simpa only [badPrimeTupleKernel, mul_div_assoc, mul_assoc, mul_left_comm, mul_comm] using H'
    _ = K * ∑ n ∈ S, ((∏ i, auxiliary A B ε (totalExponent P.exponent i) (n i)) /
        (tupleLCM n : ℝ)) * (weightedMass P.exponent n : ℝ) ^ β := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left H (Nat.cast_nonneg _)

end NairTenenbaum
