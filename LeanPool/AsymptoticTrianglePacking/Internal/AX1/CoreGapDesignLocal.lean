/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the *local* sub-triple design and its bridge to a near-regular family

`Nibble.AX1.hasNearRegularFamily_of_subTripleDesign` (`Nibble.CoreGapDesign`) charges the
exceptional edges of the `i`-th sub-triple at the rate `(2·Bad_i/t)·|V|`.  For sub-triples living
inside sub-blocks of clusters, `Nibble.AX1.uniform_triple_member_local`
(`Nibble.CoreGapPruneLocal`) gives the much better rate `(2·Bad_i/t)·(|A_i| + |B_i| + |C_i|)`, in
which only the sub-triple appears.  This is what makes the exceptional-edge clause satisfiable at
all: with the global `|V|` the clause forces the regularity scale to beat the *number of clusters*,
which itself grows with the regularity scale.

* `Nibble.AX1.designSupport` — the size `|A| + |B| + |C|` of the support of a sub-triple.
* `Nibble.AX1.IsSubTripleDesignLocal` — the design, with the localised exceptional clause, phrased
  on top of `Nibble.AX1.IsSubTripleShape`.
* `Nibble.AX1.hasNearRegularFamily_of_subTripleDesignLocal` — **the bridge**.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapDesign
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapPruneLocal
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapTripleShape

/-! # CoreGapDesignLocal -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The support size `|A| + |B| + |C|` of a sub-triple: the localised replacement for `|V|` in the
exceptional-edge clause of a design. -/
noncomputable def designSupport (A B C : Finset V) : ℝ := (#A : ℝ) + (#B : ℝ) + (#C : ℝ)

/-- **A local sub-triple design.**  The shape of `Nibble.AX1.IsSubTripleShape` together with the
global clauses, the exceptional-edge clause now being charged against the *support* of the
sub-triple rather than against the whole vertex set. -/
def IsSubTripleDesignLocal (G : SimpleGraph V) [DecidableRel G.Adj] (ε μ η d₀ ε₂ μ₂ t : ℝ) (k : ℕ)
    (A B C : ℕ → Finset V) (d Elo : ℕ → ℝ) : Prop :=
  IsSubTripleShape G ε₂ μ₂ k A B C d ∧
  0 < ε₂ ∧ ε₂ ≤ 1 ∧ 0 < t ∧ 0 ≤ η ∧ μ₂ ≤ μ ∧
  (∀ i < k, d₀ ≤ d i) ∧ (∀ i < k, 0 ≤ d i) ∧
  (∀ i < k, 2 * t ≤ (μ - μ₂) * d i) ∧
  (∀ i < k, Elo i ≤ (#((tripleGraph G (A i) (B i) (C i)).cliqueFinset 2) : ℝ)) ∧
  (∀ i < k, (2 * designBad ε₂ (A i) (B i) (C i) / t) * designSupport (A i) (B i) (C i)
    ≤ η * (Elo i - designBad ε₂ (A i) (B i) (C i))) ∧
  nu3star G ≤ (∑ i ∈ Finset.range k,
    (Elo i - designBad ε₂ (A i) (B i) (C i)) / 3) + ε * (Fintype.card V : ℝ) ^ 2

/-- **The bridge from a local sub-triple design to a near-regular family.**  Identical to
`Nibble.AX1.hasNearRegularFamily_of_subTripleDesign` except that the exceptional edges of each
member are charged against the support of that member, via
`Nibble.AX1.uniform_triple_member_local`. -/
theorem hasNearRegularFamily_of_subTripleDesignLocal (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε μ η d₀ ε₂ μ₂ t : ℝ} {k : ℕ} {A B C : ℕ → Finset V} {d Elo : ℕ → ℝ}
    (h : IsSubTripleDesignLocal G ε μ η d₀ ε₂ μ₂ t k A B C d Elo) :
    HasNearRegularFamily G ε μ η d₀ := by
  classical
  obtain ⟨hshape, hε₂, hε₂1, ht, hη, hμ₂, hd₀, hdnn, hslack, hElo, hexc, hcover⟩ := h
  obtain ⟨hdAB, hdAC, hdBC, huAB, huAC, huBC, hρAB, hρAC, hρBC, hClo, hChi, hBlo, hBhi, hAlo,
    hAhi, hpair⟩ := hshape
  -- the member attached to the `i`-th sub-triple
  have hmem : ∀ i : ℕ, ∃ Bad : Finset (Finset V), i < k →
      (((#Bad : ℕ) : ℝ) ≤ designBad ε₂ (A i) (B i) (C i) ∧
        prune (tripleGraph G (A i) (B i) (C i)) Bad ≤ G ∧
        (∀ e ∈ (prune (tripleGraph G (A i) (B i) (C i)) Bad).cliqueFinset 2,
          (edgeTriangleDegree (prune (tripleGraph G (A i) (B i) (C i)) Bad) e : ℝ)
            ≤ (1 + μ₂) * d i) ∧
        (∃ Exc : Finset (Finset V),
          ((#Exc : ℕ) : ℝ) ≤ (2 * ((#Bad : ℕ) : ℝ) / t) * designSupport (A i) (B i) (C i) ∧
          ∀ e ∈ (prune (tripleGraph G (A i) (B i) (C i)) Bad).cliqueFinset 2, e ∉ Exc →
            (1 - μ₂) * d i - 2 * t
              ≤ (edgeTriangleDegree (prune (tripleGraph G (A i) (B i) (C i)) Bad) e : ℝ)) ∧
        ((#((tripleGraph G (A i) (B i) (C i)).cliqueFinset 2) : ℕ) : ℝ) - ((#Bad : ℕ) : ℝ)
          ≤ ((#((prune (tripleGraph G (A i) (B i) (C i)) Bad).cliqueFinset 2) : ℕ) : ℝ)) := by
    intro i
    by_cases hi : i < k
    · obtain ⟨Bad, h1, h2, h3, h4, h5⟩ :=
        uniform_triple_member_local G (hdAB i hi) (hdAC i hi) (hdBC i hi) hε₂ hε₂1 ht
          (huAB i hi) (huAC i hi) (huBC i hi) (hρAB i hi) (hρAC i hi) (hρBC i hi)
          (hClo i hi) (hChi i hi) (hBlo i hi) (hBhi i hi) (hAlo i hi) (hAhi i hi)
      exact ⟨Bad, fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨∅, fun h => absurd h hi⟩
  choose Bad hBad using hmem
  refine ⟨k, fun i => prune (tripleGraph G (A i) (B i) (C i)) (Bad i), d, ?_, ?_, hd₀, ?_, ?_, ?_⟩
  · exact fun i hi => (hBad i hi).2.1
  · intro i hi j hj hij x y hxi hxj
    exact hpair i hi j hj hij x y (prune_le _ _ hxi) (prune_le _ _ hxj)
  · intro i hi e he
    have h := (hBad i hi).2.2.1 e he
    have hle : (1 + μ₂) * d i ≤ (1 + μ) * d i := by
      have := hdnn i hi; nlinarith
    linarith
  · intro i hi
    obtain ⟨Exc, hExc, hlo⟩ := (hBad i hi).2.2.2.1
    refine ⟨Exc, ?_, ?_⟩
    · have hBadle : ((#(Bad i) : ℕ) : ℝ) ≤ designBad ε₂ (A i) (B i) (C i) := (hBad i hi).1
      have hsupp : 0 ≤ designSupport (A i) (B i) (C i) := by
        unfold designSupport; positivity
      have hmono : (2 * ((#(Bad i) : ℕ) : ℝ) / t) * designSupport (A i) (B i) (C i)
          ≤ (2 * designBad ε₂ (A i) (B i) (C i) / t) * designSupport (A i) (B i) (C i) := by
        have hd : 2 * ((#(Bad i) : ℕ) : ℝ) / t ≤ 2 * designBad ε₂ (A i) (B i) (C i) / t := by
          gcongr
        exact mul_le_mul_of_nonneg_right hd hsupp
      have hsurv : Elo i - designBad ε₂ (A i) (B i) (C i)
          ≤ ((#((prune (tripleGraph G (A i) (B i) (C i)) (Bad i)).cliqueFinset 2) : ℕ) : ℝ) := by
        have h5 := (hBad i hi).2.2.2.2
        have := hElo i hi
        linarith
      have hex := hexc i hi
      have hη' : η * (Elo i - designBad ε₂ (A i) (B i) (C i))
          ≤ η * ((#((prune (tripleGraph G (A i) (B i) (C i)) (Bad i)).cliqueFinset 2) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsurv hη
      linarith
    · intro e he hne
      have h := hlo e he hne
      have := hslack i hi
      linarith
  · refine le_trans hcover ?_
    have hterm : ∀ i ∈ Finset.range k,
        (Elo i - designBad ε₂ (A i) (B i) (C i)) / 3
          ≤ ((#((prune (tripleGraph G (A i) (B i) (C i)) (Bad i)).cliqueFinset 2) : ℕ) : ℝ) / 3 := by
      intro i hi
      rw [Finset.mem_range] at hi
      have h5 := (hBad i hi).2.2.2.2
      have h1 := (hBad i hi).1
      have := hElo i hi
      linarith
    have := Finset.sum_le_sum hterm
    linarith

end Nibble.AX1
