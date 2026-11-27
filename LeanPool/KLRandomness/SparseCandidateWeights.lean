/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SparseCandidate
public import LeanPool.KLRandomness.SparseCandidateList
public import LeanPool.KLRandomness.SampleConcentration
public import LeanPool.KLRandomness.Sparse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Small support weight among rank-preserving candidates

The incidence conclusion of the finite sampling construction is exactly the
hypothesis of the deterministic sparse-support estimate.  If at most a `θ`
fraction of a nonempty list loses rank, restricting to the rank-preserving
indices costs only the factor `1 / (1 - θ)` in the support-weight bound.
-/

@[expose] public section

namespace Klr.SparseCandidateWeights

open SparseCandidate SampleConcentration
open scoped BigOperators

variable {M m r J : ℕ}

/-- The total nonnegative weight on a candidate's support. -/
def supportWeight (w : Fin M → ℝ) (c : Candidate M m r) : ℝ :=
  ∑ a ∈ c.1.val, w a

theorem supportWeight_nonneg (w : Fin M → ℝ) (hw : ∀ a, 0 ≤ w a)
    (c : Candidate M m r) : 0 ≤ supportWeight w c :=
  Finset.sum_nonneg fun a _ => hw a

/-- The sample count and the sparse-support incidence API count the same indices. -/
theorem incidence_eq_count (z : Fin J → Candidate M m r) (a : Fin M) :
    Sparse.incidence (fun j => (z j).1.val) a = count {c | a ∈ c.1.val} z := by
  classical
  unfold Sparse.incidence count
  congr 1
  ext j
  simp

/-- The selected list satisfies the deterministic average-weight estimate. -/
theorem average_supportWeight_le (z : Fin J → Candidate M m r) (hJ : 0 < J)
    (hinc : ∀ a, (count {c | a ∈ c.1.val} z : ℝ) ≤ 2 * ((m : ℝ) / M) * J)
    (w : Fin M → ℝ) (C : ℝ) (hw : ∀ a, 0 ≤ w a)
    (hC : ∑ a, (w a) ^ 2 ≤ C) :
    (∑ j, supportWeight w (z j)) / J ≤
      (2 * ((m : ℝ) / M)) * Real.sqrt ((M : ℝ) * C) := by
  have : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  have hi : ∀ a, (Sparse.incidence (fun j => (z j).1.val) a : ℝ) ≤
      (2 * ((m : ℝ) / M)) * Fintype.card (Fin J) := by
    intro a
    simpa only [incidence_eq_count, Fintype.card_fin] using hinc a
  simpa only [supportWeight, Fintype.card_fin] using
    Sparse.average_support_weights_le (fun j => (z j).1.val) w
      (2 * ((m : ℝ) / M)) C hw (by positivity) hi hC

/-- Restricting a support family to a subtype cannot increase any incidence. -/
theorem incidence_subtype_le {Q : Type*} [Fintype Q] (S : Q → Finset (Fin M))
    (P : Q → Prop) [Fintype {q // P q}] (a : Fin M) :
    Sparse.incidence (fun q : {q // P q} => S q.val) a ≤ Sparse.incidence S a := by
  classical
  unfold Sparse.incidence
  apply Finset.card_le_card_of_injOn (fun q : {q // P q} => q.val)
  · intro q hq
    simpa using hq
  · intro q _ q' _ h
    exact Subtype.ext h

/-- A rank-preserving candidate of small support weight exists in every list
whose incidence and bad-rank counts satisfy the sampling bounds. -/
theorem exists_rank_good_small_weight (z : Fin J → Candidate M m r) (hJ : 0 < J)
    (hinc : ∀ a, (count {c | a ∈ c.1.val} z : ℝ) ≤ 2 * ((m : ℝ) / M) * J)
    (D : Finset (Fin M)) (θ : ℝ) (hθ : θ < 1)
    (hrank : (count {c | BadRank D c} z : ℝ) ≤ θ * J)
    (w : Fin M → ℝ) (C : ℝ) (hw : ∀ a, 0 ≤ w a)
    (hC : ∑ a, (w a) ^ 2 ≤ C) :
    ∃ j, ¬ BadRank D (z j) ∧ supportWeight w (z j) ≤
      ((2 * ((m : ℝ) / M)) / (1 - θ)) * Real.sqrt ((M : ℝ) * C) := by
  classical
  let G := {j : Fin J // ¬ BadRank D (z j)}
  have hpartition : count {c | BadRank D c} z + Fintype.card G = J := by
    simpa only [count, G, Fintype.card_subtype, Finset.card_univ,
      Fintype.card_fin, Set.mem_ofPred_eq] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin J)))
        (fun j => BadRank D (z j)))
  have hpartition' : (count {c | BadRank D c} z : ℝ) + Fintype.card G = J := by
    exact_mod_cast hpartition
  have hgood : (1 - θ) * J ≤ (Fintype.card G : ℝ) := by linarith
  have hθpos : 0 < 1 - θ := sub_pos.mpr hθ
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hGpos : 0 < Fintype.card G := by
    have h := (mul_pos hθpos hJpos).trans_le hgood
    exact_mod_cast h
  have : Nonempty G := Fintype.card_pos_iff.mp hGpos
  have hδ : 0 ≤ 2 * ((m : ℝ) / M) := by positivity
  have hi : ∀ a, (Sparse.incidence (fun j : G => (z j.val).1.val) a : ℝ) ≤
      ((2 * ((m : ℝ) / M)) / (1 - θ)) * Fintype.card G := by
    intro a
    have hi0 : (Sparse.incidence (fun j : G => (z j.val).1.val) a : ℝ) ≤
        (Sparse.incidence (fun j => (z j).1.val) a : ℝ) := by
      exact_mod_cast incidence_subtype_le (fun j => (z j).1.val)
        (fun j => ¬ BadRank D (z j)) a
    calc
      _ ≤ 2 * ((m : ℝ) / M) * J := by
        exact hi0.trans (by simpa only [incidence_eq_count] using hinc a)
      _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hθpos).mpr
        nlinarith [mul_le_mul_of_nonneg_left hgood hδ]
  obtain ⟨j, hj⟩ := Sparse.exists_small_support (fun j : G => (z j.val).1.val) w
    ((2 * ((m : ℝ) / M)) / (1 - θ)) C hw (div_nonneg hδ hθpos.le) hi hC
  exact ⟨j.val, j.property, by simpa only [supportWeight, Fintype.card_fin] using hj⟩

/-- The average-weight bound applied directly to a list from Lemma 4. -/
theorem average_supportWeight_le_of_isGood (z : Fin J → Candidate M m r)
    {τ θ : ℝ} (hz : SparseCandidateList.IsGood z τ θ) (hJ : 0 < J)
    (w : Fin M → ℝ) (C : ℝ) (hw : ∀ a, 0 ≤ w a)
    (hC : ∑ a, (w a) ^ 2 ≤ C) :
    (∑ j, supportWeight w (z j)) / J ≤
      (2 * ((m : ℝ) / M)) * Real.sqrt ((M : ℝ) * C) :=
  average_supportWeight_le z hJ hz.incidence w C hw hC

/-- A dense unread set and a sparse rank-preserving list give a candidate
that both preserves rank and has the asserted small total support weight. -/
theorem exists_rank_good_small_weight_of_isGood (z : Fin J → Candidate M m r)
    {τ θ : ℝ} (hz : SparseCandidateList.IsGood z τ θ) (hJ : 0 < J) (hθ : θ < 1)
    (D : Finset (Fin M)) (hD : τ * M ≤ (D.card : ℝ))
    (w : Fin M → ℝ) (C : ℝ) (hw : ∀ a, 0 ≤ w a)
    (hC : ∑ a, (w a) ^ 2 ≤ C) :
    ∃ j, ¬ BadRank D (z j) ∧ supportWeight w (z j) ≤
      ((2 * ((m : ℝ) / M)) / (1 - θ)) * Real.sqrt ((M : ℝ) * C) :=
  exists_rank_good_small_weight z hJ hz.incidence D θ hθ (hz.preservesRank D hD)
    w C hw hC

end Klr.SparseCandidateWeights
