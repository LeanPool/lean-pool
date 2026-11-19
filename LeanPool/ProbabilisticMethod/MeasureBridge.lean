/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.ProbabilisticMethod.RandomGraph
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs

/-!
# The finite `p`-biased cube as a product of Bernoulli measures

This file identifies the counting probability `Finset.bernoulliProb` with Mathlib's
measure-theoretic laws: the product of Bernoulli distributions on a set, `setBer(u, p)`, and the
binomial random graph `G(V, p)`. Every counting statement of this library is therefore a statement
about those measures.

## Main statements

* `Finset.setBernoulli_real_eq_bernoulliProb`: `setBer(U, p)` gives a family `S` of sets the
  probability `U.bernoulliProb p Q` of any event `Q` that agrees with `S` on the subsets of `U`.
* `SimpleGraph.binomialRandom_real_eq_bernoulliProb`: `G(V, p)` gives a set `S` of graphs the
  probability that `fromEdgeSet A ∈ S` for a `p`-random set `A` of possible edges.
* `SimpleGraph.binomialRandom_real_isClique`, `SimpleGraph.binomialRandom_real_isClique_compl`:
  a fixed `s` is a clique of `G(V, p)` with probability `p ^ C(|s|, 2)`, and independent with
  probability `(1 - p) ^ C(|s|, 2)`.
-/

public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped Finset

namespace Finset

variable {α : Type*} [DecidableEq α] [Countable α]

/-- The product of `p`-Bernoulli distributions on a finite set `U` is the finite `p`-biased cube:
it gives a family `S` of sets the probability of any event `Q` that agrees with `S` on the
subsets of `U`. -/
theorem setBernoulli_real_eq_bernoulliProb (U : Finset α) (p : I) {S : Set (Set α)}
    {Q : Finset α → Prop} [DecidablePred Q] (hQ : ∀ A ⊆ U, (A : Set α) ∈ S ↔ Q A) :
    setBer((U : Set α), p).real S = U.bernoulliProb p Q := by
  have hS : {s ∈ S | s ⊆ (U : Set α)} = ⋃ A ∈ U.powerset.filter Q, {(A : Set α)} := by
    ext s
    simp only [Set.mem_sep_iff, Set.mem_iUnion, Set.mem_singleton_iff, mem_filter, mem_powerset,
      exists_prop]
    constructor
    · rintro ⟨hs, hsU⟩
      lift s to Finset α using (U.finite_toSet.subset hsU)
      exact ⟨s, ⟨coe_subset.mp hsU, (hQ s (coe_subset.mp hsU)).mp hs⟩, rfl⟩
    · rintro ⟨A, ⟨hAU, hA⟩, rfl⟩
      exact ⟨(hQ A hAU).mpr hA, coe_subset.mpr hAU⟩
  rw [measureReal_def, setBernoulli_apply_eq_apply_subsets, ← measureReal_def, hS,
    measureReal_biUnion_finset (fun A _ B _ hAB => by simpa using hAB)
      (fun _ _ => measurableSet_singleton _), bernoulliProb]
  refine sum_congr rfl fun A hA => ?_
  have hAU := mem_powerset.mp (mem_filter.mp hA).1
  rw [setBernoulli_real_singleton p (coe_subset.mpr hAU) U.finite_toSet, ← coe_sdiff,
    Set.ncard_coe_finset, Set.ncard_coe_finset, bernoulliWeight]

end Finset

namespace SimpleGraph

variable {V : Type*}

section Fintype

variable [Fintype V] [DecidableEq V]

/-- The possible edges are the non-diagonal elements of `Sym2 V`. -/
theorem coe_possibleEdges : (possibleEdges V : Set (Sym2 V)) = Sym2.diagSetᶜ := by
  ext e
  induction e using Sym2.ind with
  | _ v w => simp [possibleEdges, Finset.pairs, Sym2.diagSet]

/-- The binomial random graph `G(V, p)` gives a set `S` of graphs the probability of any event `Q`
on sets of possible edges such that `fromEdgeSet A ∈ S ↔ Q A`. -/
theorem binomialRandom_real_eq_bernoulliProb (p : I) {S : Set (SimpleGraph V)}
    {Q : Finset (Sym2 V) → Prop} [DecidablePred Q]
    (hQ : ∀ A ⊆ possibleEdges V, fromEdgeSet (A : Set (Sym2 V)) ∈ S ↔ Q A) :
    G(V, p).real S = (possibleEdges V).bernoulliProb p Q := by
  rw [measureReal_def, binomialRandom_apply', ← measureReal_def, ← coe_possibleEdges]
  refine Finset.setBernoulli_real_eq_bernoulliProb _ p fun A hA =>
    ⟨fun ⟨G, hG, hGA⟩ => (hQ A hA).mp ?_, fun h => ⟨_, (hQ A hA).mpr h, ?_⟩⟩
  · rwa [← hGA, fromEdgeSet_edgeSet]
  · ext e
    have : e ∈ (A : Set (Sym2 V)) → ¬e.IsDiag := fun he => by
      simpa [Sym2.diagSet] using (coe_possibleEdges (V := V)).subset (hA he)
    rw [edgeSet_fromEdgeSet]
    exact ⟨And.left, fun he => ⟨he, by simpa [Sym2.diagSet] using this he⟩⟩

end Fintype

section Finite

variable [Finite V]

/-- A fixed set `s` is a clique of `G(V, p)` with probability `p ^ C(|s|, 2)`. -/
theorem binomialRandom_real_isClique (p : I) (s : Finset V) :
    G(V, p).real {G | G.IsClique (s : Set V)} = (p : ℝ) ^ (#s).choose 2 := by
  classical
  have := Fintype.ofFinite V
  exact (binomialRandom_real_eq_bernoulliProb p fun _ _ => isClique_fromEdgeSet_iff).trans
    (bernoulliProb_isClique s)

/-- A fixed set `s` is independent in `G(V, p)` with probability `(1 - p) ^ C(|s|, 2)`. -/
theorem binomialRandom_real_isClique_compl (p : I) (s : Finset V) :
    G(V, p).real {G | Gᶜ.IsClique (s : Set V)} = (1 - (p : ℝ)) ^ (#s).choose 2 := by
  classical
  have := Fintype.ofFinite V
  exact (binomialRandom_real_eq_bernoulliProb p fun _ _ =>
    isClique_compl_fromEdgeSet_iff.trans disjoint_comm).trans (bernoulliProb_isClique_compl s)

end Finite

end SimpleGraph
