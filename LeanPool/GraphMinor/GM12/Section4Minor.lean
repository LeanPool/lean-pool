/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.Statement
import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Restricting a controlled minor model

The deletion step in Graph Minors XII, (4.2), page 249, retains the branch
subgraphs and joining edges for the vertices and edges that remain. The
control condition is preserved because the target has fewer vertices.
-/

public section

namespace GraphMinor.GM12

open Set Hypergraph

/-- The subgraph case of Graph Minors XII, (4.2), page 249. Delete the unused
branches and joining edges from the model. This lemma does not handle edge
contractions or isomorphisms of the target. -/
theorem theorem_4_2_subgraph {α β γ δ : Type*} {G : Hypergraph α β}
    {θ : ℕ} {T : Set (Hypergraph α β × Hypergraph α β)} {L L' : Graph γ δ}
    (hL : L ≤ L') (hfin : L'.vertexSet.Finite) (hc : ControlsMinor G θ T L') :
    ControlsMinor G θ T L := by
  obtain ⟨a, b, ha, hdisj, hlink, hloop, hinj, hcard, hcontrol⟩ := hc
  have hcardL : L.vertexSet.ncard ≤ L'.vertexSet.ncard :=
    Set.ncard_le_ncard hL.vertexSet_mono hfin
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_, hcardL.trans hcard, ?_⟩
  · intro v hv
    exact ha v (hL.vertexSet_mono hv)
  · intro u hu v hv huv
    exact hdisj u (hL.vertexSet_mono hu) v (hL.vertexSet_mono hv) huv
  · intro e u v he huv
    exact hlink e u v ((hL.isLink_iff he.edge_mem).mp he) huv
  · intro e v he
    exact hloop e v ((hL.isLink_iff he.edge_mem).mp he)
  · intro e he f hf hef
    exact hinj e (hL.edgeSet_mono he) f (hL.edgeSet_mono hf) hef
  · intro A B hm ho v hv
    exact hcontrol A B hm (lt_of_lt_of_le ho hcardL) v (hL.vertexSet_mono hv)

/-- The isomorphism step of Graph Minors XII, (4.2), page 249. Relabel the
branches and joining edges by the two bijections. A host edge label is needed
only to extend the edge map to unused target labels. -/
theorem controlsMinor_of_iso {α β γ δ γ' δ' : Type*} [Nonempty β]
    {G : Hypergraph α β} {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)}
    {L : Graph γ δ} {L' : Graph γ' δ'} (φ : Iso L L')
    (hc : ControlsMinor G θ T L') : ControlsMinor G θ T L := by
  classical
  obtain ⟨a, b, ha, hdisj, hlink, hloop, hinj, hcard, hcontrol⟩ := hc
  let a' : γ → Hypergraph α β := fun v =>
    if hv : v ∈ L.vertexSet then a (φ.vertexEquiv ⟨v, hv⟩) else G
  let b' : δ → β := fun e =>
    if he : e ∈ L.edgeSet then b (φ.edgeEquiv ⟨e, he⟩) else Classical.choice ‹Nonempty β›
  have hcardEq : L.vertexSet.ncard = L'.vertexSet.ncard := by
    simpa only [Nat.card_coe_set_eq] using Nat.card_congr φ.vertexEquiv
  refine ⟨a', b', ?_, ?_, ?_, ?_, ?_, hcardEq.symm ▸ hcard, ?_⟩
  · intro v hv
    simpa only [a', dite_eq_left hv] using ha _ (φ.vertexEquiv ⟨v, hv⟩).property
  · intro u hu v hv huv
    have hne : (φ.vertexEquiv ⟨u, hu⟩ : γ') ≠ φ.vertexEquiv ⟨v, hv⟩ := by
      intro h
      exact huv (congrArg Subtype.val (φ.vertexEquiv.injective (Subtype.ext h)))
    simpa only [a', dite_eq_left hu, dite_eq_left hv] using
      hdisj _ (φ.vertexEquiv ⟨u, hu⟩).property _ (φ.vertexEquiv ⟨v, hv⟩).property hne
  · intro e u v he huv
    have he' := (φ.isLink_iff ⟨e, he.edge_mem⟩ ⟨u, he.left_mem⟩ ⟨v, he.right_mem⟩).mp he
    have hne : (φ.vertexEquiv ⟨u, he.left_mem⟩ : γ') ≠ φ.vertexEquiv ⟨v, he.right_mem⟩ := by
      intro h
      exact huv (congrArg Subtype.val (φ.vertexEquiv.injective (Subtype.ext h)))
    simpa only [a', b', dite_eq_left he.edge_mem, dite_eq_left he.left_mem,
      dite_eq_left he.right_mem]
      using hlink _ _ _ he' hne
  · intro e v he
    have he' := (φ.isLink_iff ⟨e, he.edge_mem⟩ ⟨v, he.left_mem⟩ ⟨v, he.left_mem⟩).mp he
    simpa only [a', b', dite_eq_left he.edge_mem, dite_eq_left he.left_mem] using hloop _ _ he'
  · intro e he f hf hef
    have hne : (φ.edgeEquiv ⟨e, he⟩ : δ') ≠ φ.edgeEquiv ⟨f, hf⟩ := by
      intro h
      exact hef (congrArg Subtype.val (φ.edgeEquiv.injective (Subtype.ext h)))
    simpa only [b', dite_eq_left he, dite_eq_left hf] using
      hinj _ (φ.edgeEquiv ⟨e, he⟩).property _ (φ.edgeEquiv ⟨f, hf⟩).property hne
  · intro A B hm ho v hv
    have ho' : separationOrder A B < L'.vertexSet.ncard := hcardEq ▸ ho
    simpa only [a', dite_eq_left hv] using
      hcontrol A B hm ho' _ (φ.vertexEquiv ⟨v, hv⟩).property

end GraphMinor.GM12
