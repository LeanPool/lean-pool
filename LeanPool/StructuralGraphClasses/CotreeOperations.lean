/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.Cotree
public import Mathlib.Logic.Equiv.Set

/-!
# Operations on cotree representations

Complementation exchanges union and join. A partition with no cross edges
allows two cotree representations to be assembled into a representation of the
whole graph, using Mathlib's sum of graph isomorphisms.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Complementation transports graph isomorphisms. -/
def Iso.complement (f : G ≃g H) : Gᶜ ≃g Hᶜ where
  toEquiv := f.toEquiv
  map_rel_iff' := by
    intro a b
    change (f a ≠ f b ∧ ¬H.Adj (f a) (f b)) ↔ (a ≠ b ∧ ¬G.Adj a b)
    simp only [f.injective.ne_iff, f.map_rel_iff]

namespace Cotree

/-- Exchange union and join at every internal node. -/
def complement : Cotree → Cotree
  | empty => empty
  | leaf => leaf
  | union l r => join l.complement r.complement
  | join l r => union l.complement r.complement

/-- Exchanging union and join twice returns the original cotree. -/
@[simp] theorem complement_complement (t : Cotree) : t.complement.complement = t := by
  induction t <;> simp_all [complement]

/-- The complement cotree represents the complement graph. -/
noncomputable def complementIso (t : Cotree) : t.complement.graph ≃g t.graphᶜ := by
  induction t with
  | empty =>
    refine ⟨Equiv.refl _, ?_⟩
    intro a
    exact PEmpty.elim a
  | leaf =>
    change (⊥ : SimpleGraph Unit) ≃g (⊥ : SimpleGraph Unit)ᶜ
    refine ⟨Equiv.refl _, ?_⟩
    intro a b
    have he : a = b := Subsingleton.elim _ _
    subst b
    simp
  | union l r ihl ihr =>
    change (l.complement.graphᶜ ⊕g r.complement.graphᶜ)ᶜ ≃g (l.graph ⊕g r.graph)ᶜ
    simpa only [compl_compl] using
      (Iso.sumCongr ihl.complement ihr.complement).complement
  | join l r ihl ihr =>
    change (l.complement.graph ⊕g r.complement.graph) ≃g (l.graphᶜ ⊕g r.graphᶜ)ᶜᶜ
    rw [compl_compl]
    exact Iso.sumCongr ihl ihr

end Cotree

/-- A cotree representation can be complemented without reconstructing the graph. -/
noncomputable def CotreeRepresentation.compl (R : CotreeRepresentation G) :
    CotreeRepresentation Gᶜ where
  cotree := R.cotree.complement
  iso := R.cotree.complementIso.trans R.iso.complement

/-- Relabel a cotree representation along a graph isomorphism. -/
def CotreeRepresentation.mapIso (R : CotreeRepresentation G) (f : G ≃g H) :
    CotreeRepresentation H where
  cotree := R.cotree
  iso := R.iso.trans f

/-- An empty vertex type has the empty cotree representation. -/
def CotreeRepresentation.ofIsEmpty [IsEmpty V] (G : SimpleGraph V) :
    CotreeRepresentation G where
  cotree := .empty
  iso := by
    change (⊥ : SimpleGraph PEmpty) ≃g G
    exact ⟨Equiv.equivOfIsEmpty _ _, by intro a; exact PEmpty.elim a⟩

/-- A one-vertex graph has a one-leaf cotree representation. -/
noncomputable def CotreeRepresentation.ofSubsingleton [Subsingleton V] [Nonempty V]
    (G : SimpleGraph V) : CotreeRepresentation G := by
  let v : V := Classical.arbitrary V
  refine ⟨.leaf, ?_⟩
  change (⊥ : SimpleGraph Unit) ≃g G
  refine ⟨⟨fun _ => v, fun _ => (), ?_, ?_⟩, ?_⟩
  · intro a
    exact Subsingleton.elim _ _
  · intro a
    exact Subsingleton.elim _ _
  · intro a b
    change G.Adj v v ↔ False
    simp

/-- A vertex partition with no cross edges gives an isomorphism from the
disjoint union of its induced pieces to the original graph. -/
noncomputable def isoSumInduce (s : Set V)
    (hcross : ∀ u ∈ s, ∀ v ∉ s, ¬G.Adj u v) :
    (G.induce s ⊕g G.induce sᶜ) ≃g G := by
  classical
  refine ⟨Equiv.Set.sumCompl s, ?_⟩
  rintro (a | a) (b | b)
  · simp
  · simp only [Equiv.Set.sumCompl_apply_inl, Equiv.Set.sumCompl_apply_inr, sum_adj]
    exact iff_false_intro (hcross a.val a.property b.val b.property)
  · simp only [Equiv.Set.sumCompl_apply_inr, Equiv.Set.sumCompl_apply_inl, sum_adj]
    exact iff_false_intro (fun h => hcross b.val b.property a.val a.property h.symm)
  · simp

/-- Assemble representations of two separated induced pieces. -/
noncomputable def CotreeRepresentation.unionInduce (s : Set V)
    (hcross : ∀ u ∈ s, ∀ v ∉ s, ¬G.Adj u v)
    (L : CotreeRepresentation (G.induce s)) (R : CotreeRepresentation (G.induce sᶜ)) :
    CotreeRepresentation G where
  cotree := .union L.cotree R.cotree
  iso := (Iso.sumCongr L.iso R.iso).trans (isoSumInduce s hcross)

end SimpleGraph
