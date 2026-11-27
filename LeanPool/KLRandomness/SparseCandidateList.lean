/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SparseCandidate
public import LeanPool.KLRandomness.SampleConcentration
public import LeanPool.KLRandomness.SparseParameters
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Existence of sparse rank-preserving candidate lists

This is the finite combinatorial existence assertion in Lemma 4.  All marginal
probabilities, concentration bounds, and eventual parameter inequalities are
proved for actual finite sample spaces in the imported modules.
-/

@[expose] public section

namespace Klr.SparseCandidateList

open FiniteProbability SampleConcentration SparseCandidate

variable {M m r J : ℕ}

/-- The two simultaneous requirements on a candidate list. Repetitions are
allowed, as in independent sampling with replacement. -/
structure IsGood (z : Fin J → Candidate M m r) (τ θ : ℝ) : Prop where
  incidence : ∀ a : Fin M,
    (count {c : Candidate M m r | a ∈ c.1.val} z : ℝ) ≤ 2 * ((m : ℝ) / M) * J
  preservesRank : ∀ D : Finset (Fin M), τ * M ≤ (D.card : ℝ) →
    (count {c : Candidate M m r | BadRank D c} z : ℝ) ≤ θ * J

/-- Finite parameter criterion for a sparse rank-preserving list. -/
theorem exists_goodList (hm2 : 2 ≤ m) (hmM : m ≤ M) (hrm : r + 1 ≤ m)
    (τ θ : ℝ) (hτ : 0 < τ) (hθ : 0 ≤ θ)
    (hr : 4 * (r : ℝ) ≤ τ * m)
    (hp : 4 / (τ * m) + 2 * (1 / 2 : ℝ) ^ r ≤ θ / 4)
    (hsmall : Real.exp ((M : ℝ) - θ * J / 4) +
      M * Real.exp (-(((m : ℝ) / M) * J) / 6) < 1) :
    ∃ z : Fin J → Candidate M m r, IsGood z τ θ := by
  classical
  have : Nonempty (Candidate M m r) := candidate_nonempty hmM hrm
  let A : Finset (Fin M) → Set (Candidate M m r) :=
    fun D => {c | τ * M ≤ (D.card : ℝ) ∧ BadRank D c}
  let B : Fin M → Set (Candidate M m r) := fun a => {c | a ∈ c.1.val}
  have hA : ∀ D, probability (A D) ≤ θ / 4 := by
    intro D
    by_cases hD : τ * M ≤ (D.card : ℝ)
    · have hsub : A D ⊆ {c : Candidate M m r | BadRank D c} := fun _ hc => hc.2
      exact (probability_mono hsub).trans
        ((probability_badRank_le hm2 hmM hrm D τ hτ hD hr).trans hp)
    · simp only [A, hD, false_and, Set.ofPred_false, probability_empty]
      positivity
  have hB : ∀ a, probability (B a) ≤ (m : ℝ) / M := by
    intro a
    exact le_of_eq (probability_contains (by omega) hmM hrm a)
  have htwo : (2 : ℝ) ^ M ≤ Real.exp M := by
    calc
      (2 : ℝ) ^ M ≤ (Real.exp 1) ^ M := by
        apply pow_le_pow_left₀ (by norm_num)
        have h := Real.add_one_le_exp (1 : ℝ)
        norm_num at h
        exact h
      _ = Real.exp M := by rw [← Real.exp_nat_mul]; simp
  have hs : Fintype.card (Finset (Fin M)) * Real.exp (-(θ * J) / 4) +
      Fintype.card (Fin M) * Real.exp (-(((m : ℝ) / M) * J) / 6) < 1 := by
    calc
      _ = (2 : ℝ) ^ M * Real.exp (-(θ * J) / 4) +
          M * Real.exp (-(((m : ℝ) / M) * J) / 6) := by simp
      _ ≤ Real.exp ((M : ℝ) - θ * J / 4) +
          M * Real.exp (-(((m : ℝ) / M) * J) / 6) := by
        apply add_le_add _ le_rfl
        calc
          (2 : ℝ) ^ M * Real.exp (-(θ * J) / 4) ≤
              Real.exp M * Real.exp (-(θ * J) / 4) := by gcongr
          _ = Real.exp ((M : ℝ) - θ * J / 4) := by
            rw [← Real.exp_add]
            congr 1
            ring
      _ < 1 := hsmall
  obtain ⟨z, hzA, hzB⟩ := exists_simultaneous_samples A B J θ ((m : ℝ) / M)
    hθ (by positivity) hA hB hs
  refine ⟨z, hzB, ?_⟩
  intro D hD
  have he : A D = {c : Candidate M m r | BadRank D c} := by
    ext c
    simp [A, hD]
  simpa only [he] using hzA D

/-- Lemma 4's combinatorial existence assertion, with the paper's polynomial
parameters, holds for every sufficiently large rank. -/
theorem eventually_exists_goodList (τ θ : ℝ) (hτ : 0 < τ) (hθ : 0 < θ) :
    ∀ᶠ r : ℕ in Filter.atTop,
      ∃ z : Fin (SparseParameters.listSize r) →
        Candidate (SparseParameters.blockSize r) (SparseParameters.supportSize r) r,
        IsGood z τ θ := by
  filter_upwards [SparseParameters.eventually_candidate_parameters τ θ hτ hθ]
    with r hr
  obtain ⟨hm2, hmM, hrm, hmargin, hsingle, hlist⟩ := hr
  have hM0 : (SparseParameters.blockSize r : ℝ) ≠ 0 := by
    have hn : SparseParameters.blockSize r ≠ 0 := by omega
    exact_mod_cast hn
  have he : ((SparseParameters.supportSize r : ℝ) / SparseParameters.blockSize r) *
      SparseParameters.listSize r =
      (SparseParameters.supportSize r : ℝ) * (SparseParameters.blockSize r : ℝ) ^ 2 := by
    simp only [SparseParameters.listSize, Nat.cast_pow]
    field_simp [hM0]
  apply exists_goodList hm2 hmM hrm τ θ hτ (le_of_lt hθ) hmargin hsingle
  rw [he]
  simpa only [neg_mul] using hlist

/-- Candidate lists can be obtained above any previously imposed lower bound
on the rank. This is the form needed for iterative stage choices. -/
theorem exists_goodList_above (τ θ : ℝ) (hτ : 0 < τ) (hθ : 0 < θ) (R : ℕ) :
    ∃ r ≥ R, ∃ z : Fin (SparseParameters.listSize r) →
      Candidate (SparseParameters.blockSize r) (SparseParameters.supportSize r) r,
      IsGood z τ θ := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_exists_goodList τ θ hτ hθ)
  exact ⟨max R N, le_max_left _ _, hN _ (le_max_right _ _)⟩

end Klr.SparseCandidateList
