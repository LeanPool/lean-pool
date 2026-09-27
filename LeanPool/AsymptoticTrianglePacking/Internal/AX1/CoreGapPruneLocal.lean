/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the *local* form of the pruning bound

`Nibble.AX1.prune_near_regular` bounds the number of edges whose triangle degree is damaged by
pruning by `(2|Bad|/t)·|V|`: each deleted edge can, a priori, spoil every vertex of the graph.  For
a tripartite graph living on three *sub-blocks* this is far too generous — all the triangles of
`tripleGraph G U W X` use vertices of `U ∪ W ∪ X` only — and the extra factor `|V|/(|U|+|W|+|X|)`,
which is of the order of the number of clusters, makes the exceptional-edge clause of a design
unsatisfiable once the number of clusters grows with the regularity scale.

This file re-proves the pruning bound with `|V|` replaced by any bound `D` for the degrees of the
graph being pruned, and specialises it to a cluster triple, where `D = |U| + |W| + |X|`.

* `Nibble.AX1.card_edges_heavy_deleted_le_of_degree` — the counting bound, localised.
* `Nibble.AX1.prune_near_regular_local` — the pruning package, localised.
* `Nibble.AX1.tripleGraph_degree_le` — a tripartite graph of `(U, W, X)` has degrees at most
  `|U| + |W| + |X|`.
* `Nibble.AX1.uniform_triple_member_local` — one member of the family from one triple, with the
  localised exceptional bound.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapPrune

/-! # CoreGapPruneLocal -/

@[expose] public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Few edges have an endpoint at which many edges were deleted — localised version.**  The
number of vertices at which more than `t` edges were deleted is at most `2|Bad|/t`, and each of them
lies in at most `D` edges. -/
theorem card_edges_heavy_deleted_le_of_degree (T : SimpleGraph V) [DecidableRel T.Adj]
    (Bad : Finset (Finset V)) {t : ℝ} (ht : 0 < t) {D : ℕ}
    (hdeg : ∀ v : V, #{z ∈ (univ : Finset V) | T.Adj v z} ≤ D) :
    ((#{e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)} : ℕ) : ℝ)
      ≤ (2 * (#Bad : ℝ) / t) * (D : ℝ) := by
  classical
  set S : Finset V := {v ∈ (univ : Finset V) | t < (deletedDegree T Bad v : ℝ)} with hS
  have hsub : {e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)}
      ⊆ S.biUnion (fun v => {z ∈ (univ : Finset V) | T.Adj v z}.image
        (fun z => ({v, z} : Finset V))) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨hecl, hbad⟩ := he
    push Not at hbad
    obtain ⟨v, hve, hvt⟩ := hbad
    have hvS : v ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ v, hvt⟩
    have hcard : #e = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp hecl).card_eq
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have hadj : T.Adj a b := (pair_mem_cliqueFinset_two T hab).mp hecl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hve
    refine Finset.mem_biUnion.mpr ⟨v, hvS, ?_⟩
    rcases hve with rfl | rfl
    · exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hadj⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hadj.symm⟩,
        Finset.pair_comm v a⟩
  have hcard1 : #{e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)}
      ≤ ∑ _v ∈ S, D := by
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    exact Finset.sum_le_sum fun v _ => le_trans Finset.card_image_le (hdeg v)
  have hcard2 : ((#{e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)} : ℕ) : ℝ)
      ≤ (#S : ℝ) * (D : ℝ) := by
    have h := hcard1
    rw [Finset.sum_const, smul_eq_mul] at h
    exact_mod_cast h
  have hmark := card_vertices_deletedDegree_gt T Bad (t := t)
  have hSt : (#S : ℝ) ≤ 2 * (#Bad : ℝ) / t := by
    rw [le_div_iff₀ ht]
    exact hmark
  exact le_trans hcard2 (mul_le_mul_of_nonneg_right hSt (by positivity))

/-- **The pruned graph — localised.**  As `Nibble.AX1.prune_near_regular`, but the exceptional set
is bounded using a degree bound `D` for `T` instead of the number of vertices of the ambient
graph. -/
theorem prune_near_regular_local (T : SimpleGraph V) [DecidableRel T.Adj]
    (Bad : Finset (Finset V)) {μ d t : ℝ} (ht : 0 < t) {D : ℕ}
    (hdeg : ∀ v : V, #{z ∈ (univ : Finset V) | T.Adj v z} ≤ D)
    (hhi : ∀ e ∈ T.cliqueFinset 2, e ∉ Bad → (edgeTriangleDegree T e : ℝ) ≤ (1 + μ) * d)
    (hlo : ∀ e ∈ T.cliqueFinset 2, e ∉ Bad → (1 - μ) * d ≤ (edgeTriangleDegree T e : ℝ)) :
    (∀ e ∈ (prune T Bad).cliqueFinset 2,
        (edgeTriangleDegree (prune T Bad) e : ℝ) ≤ (1 + μ) * d) ∧
      ∃ Exc : Finset (Finset V), ((#Exc : ℕ) : ℝ) ≤ (2 * (#Bad : ℝ) / t) * (D : ℝ) ∧
        ∀ e ∈ (prune T Bad).cliqueFinset 2, e ∉ Exc →
          (1 - μ) * d - 2 * t ≤ (edgeTriangleDegree (prune T Bad) e : ℝ) := by
  classical
  refine ⟨(prune_near_regular T Bad ht hhi hlo).1, ?_⟩
  refine ⟨{e ∈ T.cliqueFinset 2 | ¬ (∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t)},
    card_edges_heavy_deleted_le_of_degree T Bad ht hdeg, ?_⟩
  intro e he hexc
  obtain ⟨heT, heB⟩ := mem_cliqueFinset_two_prune T Bad he
  have hdeg' : ∀ v ∈ e, (deletedDegree T Bad v : ℝ) ≤ t := by
    by_contra hc
    exact hexc (Finset.mem_filter.mpr ⟨heT, hc⟩)
  have hcard : #e = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp he).card_eq
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
  have hadj : (prune T Bad).Adj x y := (pair_mem_cliqueFinset_two _ hxy).mp he
  have hdrop := edgeTriangleDegree_prune_ge T Bad hadj
  have hdrop' : ((edgeTriangleDegree T {x, y} : ℕ) : ℝ)
      ≤ ((edgeTriangleDegree (prune T Bad) {x, y} : ℕ) : ℝ)
        + ((deletedDegree T Bad x : ℕ) : ℝ) + ((deletedDegree T Bad y : ℕ) : ℝ) := by
    exact_mod_cast hdrop
  have hx : ((deletedDegree T Bad x : ℕ) : ℝ) ≤ t := hdeg' x (by simp)
  have hy : ((deletedDegree T Bad y : ℕ) : ℝ) ≤ t := hdeg' y (by simp)
  have hlo' := hlo {x, y} heT heB
  linarith only [hdrop', hx, hy, hlo']

/-- **A tripartite graph has degrees at most `|U| + |W| + |X|`**: all its edges stay inside the
three parts. -/
theorem tripleGraph_degree_le (G : SimpleGraph V) [DecidableRel G.Adj] (U W X : Finset V) (v : V) :
    #{z ∈ (univ : Finset V) | (tripleGraph G U W X).Adj v z} ≤ #U + #W + #X := by
  classical
  have hsub : {z ∈ (univ : Finset V) | (tripleGraph G U W X).Adj v z} ⊆ U ∪ W ∪ X := by
    intro z hz
    rw [Finset.mem_filter] at hz
    have hcross := hz.2.2
    unfold crossAdj at hcross
    simp only [Finset.mem_union]
    tauto
  refine le_trans (Finset.card_le_card hsub) ?_
  exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)

/-- **A near-regular member of the family from one cluster triple — localised.**  As
`Nibble.AX1.uniform_triple_member`, but the exceptional edges are bounded by
`(2|Bad|/t)·(|U| + |W| + |X|)`, which involves only the triple and not the ambient graph. -/
theorem uniform_triple_member_local (G : SimpleGraph V) [DecidableRel G.Adj] {U W X : Finset V}
    (hUW : Disjoint U W) (hUX : Disjoint U X) (hWX : Disjoint W X) {ε μ d t : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t)
    (hUWu : G.IsUniform ε U W) (hUXu : G.IsUniform ε U X) (hWXu : G.IsUniform ε W X)
    (hdUW : 2 * ε ≤ (G.edgeDensity U W : ℝ)) (hdUX : 2 * ε ≤ (G.edgeDensity U X : ℝ))
    (hdWX : 2 * ε ≤ (G.edgeDensity W X : ℝ))
    (hXlo : (1 - μ) * d ≤ ((G.edgeDensity U X : ℝ) - ε) * ((G.edgeDensity W X : ℝ) - 2 * ε)
      * (#X : ℝ))
    (hXhi : ((G.edgeDensity U X : ℝ) + ε) * ((G.edgeDensity W X : ℝ) + 2 * ε) * (#X : ℝ)
      ≤ (1 + μ) * d)
    (hWlo : (1 - μ) * d ≤ ((G.edgeDensity U W : ℝ) - ε) * ((G.edgeDensity W X : ℝ) - 2 * ε)
      * (#W : ℝ))
    (hWhi : ((G.edgeDensity U W : ℝ) + ε) * ((G.edgeDensity W X : ℝ) + 2 * ε) * (#W : ℝ)
      ≤ (1 + μ) * d)
    (hUlo : (1 - μ) * d ≤ ((G.edgeDensity U W : ℝ) - ε) * ((G.edgeDensity U X : ℝ) - 2 * ε)
      * (#U : ℝ))
    (hUhi : ((G.edgeDensity U W : ℝ) + ε) * ((G.edgeDensity U X : ℝ) + 2 * ε) * (#U : ℝ)
      ≤ (1 + μ) * d) :
    ∃ Bad : Finset (Finset V),
      ((#Bad : ℕ) : ℝ) ≤ 4 * ε * ((#U : ℝ) * (#W : ℝ) + (#U : ℝ) * (#X : ℝ)
        + (#W : ℝ) * (#X : ℝ)) ∧
      prune (tripleGraph G U W X) Bad ≤ G ∧
      (∀ e ∈ (prune (tripleGraph G U W X) Bad).cliqueFinset 2,
        (edgeTriangleDegree (prune (tripleGraph G U W X) Bad) e : ℝ) ≤ (1 + μ) * d) ∧
      (∃ Exc : Finset (Finset V),
        ((#Exc : ℕ) : ℝ) ≤ (2 * ((#Bad : ℕ) : ℝ) / t) * ((#U : ℝ) + (#W : ℝ) + (#X : ℝ)) ∧
        ∀ e ∈ (prune (tripleGraph G U W X) Bad).cliqueFinset 2, e ∉ Exc →
          (1 - μ) * d - 2 * t
            ≤ (edgeTriangleDegree (prune (tripleGraph G U W X) Bad) e : ℝ)) ∧
      ((#((tripleGraph G U W X).cliqueFinset 2) : ℕ) : ℝ) - ((#Bad : ℕ) : ℝ)
        ≤ ((#((prune (tripleGraph G U W X) Bad).cliqueFinset 2) : ℕ) : ℝ) := by
  classical
  obtain ⟨Bad, hBadcard, hBad⟩ := tripleGraph_near_regular G hUW hUX hWX hε hε1 hUWu hUXu hWXu
    hdUW hdUX hdWX hXlo hXhi hWlo hWhi hUlo hUhi
  refine ⟨Bad, hBadcard, le_trans (prune_le _ _) (tripleGraph_le G U W X), ?_, ?_, ?_⟩
  · exact (prune_near_regular (tripleGraph G U W X) Bad ht
      (fun e he hnb => (hBad e he hnb).2) (fun e he hnb => (hBad e he hnb).1)).1
  · obtain ⟨Exc, hExc, hlo⟩ := (prune_near_regular_local (tripleGraph G U W X) Bad ht
      (D := #U + #W + #X) (tripleGraph_degree_le G U W X)
      (fun e he hnb => (hBad e he hnb).2) (fun e he hnb => (hBad e he hnb).1)).2
    refine ⟨Exc, ?_, hlo⟩
    refine le_trans hExc (le_of_eq ?_)
    push_cast
    ring
  · exact card_cliqueFinset_two_prune_ge (tripleGraph G U W X) Bad

end Nibble.AX1
