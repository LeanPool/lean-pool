/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Set.Card

/-!
# Minimum vertex counts in the reduction to VII

XII (3.1), page 245, uses the main theorem of VII and its Section 8
characterization of the parameter alpha by normal schismatic sets.
This file supplies the minimum-count steps of that reduction. The
minimum in VII's definition is attained as soon as a candidate exists,
and a bound on the vertex count of every candidate bounds alpha.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The minimum defining VII's alpha is attained if there is a
candidate. This is the minimum-count step used in XII (3.1), page 245. -/
theorem exists_alpha_candidate_at_minimum {S : Type*} [TopologicalSpace S]
    (G : Drawing S) (hex : ∃ X : Set S, GM07.IsAlphaCandidate G X) :
    ∃ X : Set S, GM07.IsAlphaCandidate G X ∧ (X ∩ G.V).ncard = GM07.alpha G := by
  have hne : {n : ℕ | ∃ X : Set S, GM07.IsAlphaCandidate G X ∧ (X ∩ G.V).ncard = n}.Nonempty := by
    obtain ⟨X, hX⟩ := hex
    exact ⟨(X ∩ G.V).ncard, X, hX, rfl⟩
  exact csInf_mem hne

/-- A lower bound for all candidate vertex counts is a lower bound
for VII's alpha. Candidate existence is needed because natural-number
infimum assigns zero to the empty set. -/
theorem alpha_ge_of_candidate_counts {S : Type*} [TopologicalSpace S]
    (G : Drawing S) {N : ℕ} (hex : ∃ X : Set S, GM07.IsAlphaCandidate G X)
    (hbound : ∀ X : Set S, GM07.IsAlphaCandidate G X → N ≤ (X ∩ G.V).ncard) :
    N ≤ GM07.alpha G := by
  obtain ⟨X, hX, hcount⟩ := exists_alpha_candidate_at_minimum G hex
  exact hcount ▸ hbound X hX

/-- Once every alpha candidate contains a normal schismatic set,
a vertex bound for the latter gives the alpha bound required by VII
(7.5). The containment step is the unnumbered argument of VII Section 8,
which XII (3.1) invokes on page 245. -/
theorem alpha_ge_of_schismatic_counts {S : Type*} [TopologicalSpace S]
    (G : Drawing S) {N : ℕ} (hex : ∃ X : Set S, GM07.IsAlphaCandidate G X)
    (hcontains : ∀ X : Set S, GM07.IsAlphaCandidate G X →
      ∃ Y : Set S, Y ⊆ X ∧ GM07.IsSchismatic Y ∧ G.IsNormal Y)
    (hbound : ∀ Y : Set S, GM07.IsSchismatic Y → G.IsNormal Y → N ≤ (Y ∩ G.V).ncard) :
    N ≤ GM07.alpha G := by
  apply alpha_ge_of_candidate_counts G hex
  intro X hX
  obtain ⟨Y, hYX, hY, hYn⟩ := hcontains X hX
  exact (hbound Y hY hYn).trans
    (Set.ncard_le_ncard (inter_subset_inter_left G.V hYX) (G.finite_V.subset inter_subset_right))

end GraphMinor.GM12
