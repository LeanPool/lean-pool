/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.ThresholdSteps

/-!
# Creation sequences for finite threshold graphs

A creation sequence starts with the empty graph and adds isolated or universal
vertices. A representation includes an isomorphism to the actual graph.
Existence is proved by deletion and induction, not by a recognition algorithm.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Relabel the old vertices of an isolated creation step. -/
def Iso.addIsolated (f : G ≃g H) : SimpleGraph.addIsolated G ≃g SimpleGraph.addIsolated H :=
  Iso.sumCongr (Iso.refl : (⊥ : SimpleGraph Unit) ≃g ⊥) f

/-- Relabel the old vertices of a universal creation step. -/
def Iso.addUniversal (f : G ≃g H) : SimpleGraph.addUniversal G ≃g SimpleGraph.addUniversal H :=
  f.complement.addIsolated.complement

/-- Reinsert a deleted vertex, with the left summand representing that vertex. -/
noncomputable def vertexDeletionEquiv (v : V) : Unit ⊕ {x : V // x ≠ v} ≃ V := by
  classical
  refine ⟨(fun x => match x with | Sum.inl _ => v | Sum.inr a => a.val),
    (fun x => if h : x = v then Sum.inl () else Sum.inr ⟨x, h⟩), ?_, ?_⟩
  · rintro (a | a)
    · cases a
      simp
    · simp [a.property]
  · intro x
    by_cases h : x = v <;> simp [h]

/-- Reinserting a deleted isolated vertex restores the graph. -/
noncomputable def isolatedDeletionIso (v : V) (h : ∀ u, ¬G.Adj v u) :
    addIsolated (G.induce {x | x ≠ v}) ≃g G where
  toEquiv := vertexDeletionEquiv v
  map_rel_iff' := by
    rintro (a | a) (b | b)
    · simp [vertexDeletionEquiv, addIsolated]
    · simpa [vertexDeletionEquiv, addIsolated] using iff_false_intro (h b.val)
    · simpa [vertexDeletionEquiv, addIsolated] using
        iff_false_intro (show ¬G.Adj a.val v from fun hb => h a.val hb.symm)
    · rfl

/-- Reinserting a deleted universal vertex restores the graph. -/
noncomputable def universalDeletionIso (v : V) (h : ∀ u, u ≠ v → G.Adj v u) :
    addUniversal (G.induce {x | x ≠ v}) ≃g G := by
  have hi : ∀ u, ¬Gᶜ.Adj v u := by
    intro u hu
    exact hu.2 (h u hu.1.symm)
  have he : Gᶜ.induce {x | x ≠ v} = (G.induce {x | x ≠ v})ᶜ := by
    ext a b
    simp only [induce_adj, compl_adj, Subtype.val_injective.ne_iff]
  have f := (isolatedDeletionIso (G := Gᶜ) v hi).complement
  change (addIsolated (Gᶜ.induce {x | x ≠ v}))ᶜ ≃g Gᶜᶜ at f
  rw [he, compl_compl] at f
  exact f

/-- A finite sequence of isolated and universal vertex additions. -/
inductive ThresholdSequence where
  /-- Start with the empty graph. -/
  | empty
  /-- Add an isolated vertex to the previous graph. -/
  | isolated (previous : ThresholdSequence)
  /-- Add a universal vertex to the previous graph. -/
  | universal (previous : ThresholdSequence)

namespace ThresholdSequence

/-- The vertices created by a sequence. -/
def Vertex : ThresholdSequence → Type
  | empty => PEmpty
  | isolated s => Unit ⊕ s.Vertex
  | universal s => Unit ⊕ s.Vertex

/-- A creation sequence has finitely many created vertices. -/
noncomputable instance vertexFintype (s : ThresholdSequence) : Fintype s.Vertex := by
  induction s with
  | empty => exact inferInstanceAs (Fintype PEmpty)
  | isolated s ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Unit ⊕ s.Vertex))
  | universal s ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Unit ⊕ s.Vertex))

/-- The graph created by a sequence. -/
def graph : (s : ThresholdSequence) → SimpleGraph s.Vertex
  | empty => ⊥
  | isolated s => addIsolated s.graph
  | universal s => addUniversal s.graph

/-- Every sequence carries an explicit threshold partition. -/
def partition : (s : ThresholdSequence) → ThresholdPartition s.graph
  | empty => {
      clique := ∅
      independent := Set.univ
      isClique := isClique_empty
      isIndepSet := by intro a; exact PEmpty.elim a
      disjoint := by simp
      cover := by simp
      nested := by intro a; exact PEmpty.elim a }
  | isolated s => s.partition.addIsolated
  | universal s => s.partition.addUniversal

/-- Interchange isolated and universal steps. -/
def complement : ThresholdSequence → ThresholdSequence
  | empty => empty
  | isolated s => universal s.complement
  | universal s => isolated s.complement

/-- Flipping creation steps twice restores the sequence. -/
@[simp] theorem complement_complement (s : ThresholdSequence) :
    s.complement.complement = s := by
  induction s <;> simp_all [complement]

/-- Flipping creation steps represents the complementary graph. -/
noncomputable def complementIso (s : ThresholdSequence) : s.complement.graph ≃g s.graphᶜ := by
  induction s with
  | empty =>
    refine ⟨Equiv.refl _, ?_⟩
    intro a
    exact PEmpty.elim a
  | isolated s ih =>
    change addUniversal s.complement.graph ≃g (addIsolated s.graph)ᶜ
    simpa only [addUniversal, compl_compl] using ih.addUniversal
  | universal s ih =>
    change addIsolated s.complement.graph ≃g (addIsolated s.graphᶜ)ᶜᶜ
    rw [compl_compl]
    exact ih.addIsolated

end ThresholdSequence

/-- A creation sequence with an isomorphism to the represented graph. -/
structure ThresholdCreationRepresentation (G : SimpleGraph V) where
  /-- The supplied creation sequence. -/
  sequence : ThresholdSequence
  /-- Its created vertices correspond exactly to the graph vertices. -/
  iso : sequence.graph ≃g G

namespace ThresholdCreationRepresentation

/-- A creation representation supplies an explicit threshold partition. -/
def partition (R : ThresholdCreationRepresentation G) : ThresholdPartition G :=
  R.sequence.partition.mapIso R.iso

/-- A creation representation certifies threshold membership. -/
theorem isThreshold (R : ThresholdCreationRepresentation G) : G.IsThreshold :=
  R.partition.isThreshold

/-- Relabel a creation representation without changing its sequence. -/
def mapIso (R : ThresholdCreationRepresentation G) (f : G ≃g H) :
    ThresholdCreationRepresentation H := ⟨R.sequence, R.iso.trans f⟩

/-- Append an isolated step to the supplied representation. -/
def addIsolated (R : ThresholdCreationRepresentation G) :
    ThresholdCreationRepresentation (SimpleGraph.addIsolated G) :=
  ⟨.isolated R.sequence, R.iso.addIsolated⟩

/-- Append a universal step to the supplied representation. -/
def addUniversal (R : ThresholdCreationRepresentation G) :
    ThresholdCreationRepresentation (SimpleGraph.addUniversal G) :=
  ⟨.universal R.sequence, R.iso.addUniversal⟩

/-- Complement a representation by interchanging its creation steps. -/
noncomputable def compl (R : ThresholdCreationRepresentation G) :
    ThresholdCreationRepresentation Gᶜ :=
  ⟨R.sequence.complement, R.sequence.complementIso.trans R.iso.complement⟩

/-- The empty graph has an empty creation sequence. -/
def ofIsEmpty [IsEmpty V] (G : SimpleGraph V) : ThresholdCreationRepresentation G where
  sequence := .empty
  iso := by
    change (⊥ : SimpleGraph PEmpty) ≃g G
    exact ⟨Equiv.equivOfIsEmpty _ _, by intro a; exact PEmpty.elim a⟩

end ThresholdCreationRepresentation

universe u

private theorem exists_creation_of_card_le (n : ℕ) :
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ n →
      G.IsThreshold → Nonempty (ThresholdCreationRepresentation G) := by
  classical
  induction n with
  | zero =>
    intro V _ G hn h
    let : IsEmpty V := Fintype.card_eq_zero_iff.mp (by omega)
    exact ⟨ThresholdCreationRepresentation.ofIsEmpty G⟩
  | succ n ih =>
    intro V _ G hn h
    by_cases he : Nonempty V
    · let := he
      obtain ⟨P⟩ := isThreshold_iff_nonempty_thresholdPartition.mp h
      obtain ⟨v, hv⟩ := P.exists_isolated_or_universal
      let s : Set V := {x | x ≠ v}
      have hsmall : Fintype.card s ≤ n := by
        have : Fintype.card s < Fintype.card V :=
          Fintype.card_lt_of_injective_of_notMem (f := fun x : s => x.val) (b := v)
            Subtype.val_injective (by rintro ⟨x, hx⟩; exact x.property hx)
        omega
      obtain ⟨R⟩ := ih s (G.induce s) hsmall (h.induce s)
      rcases hv with hv | hv
      · exact ⟨R.addIsolated.mapIso (isolatedDeletionIso v hv)⟩
      · exact ⟨R.addUniversal.mapIso (universalDeletionIso v hv)⟩
    · let : IsEmpty V := not_nonempty_iff.mp he
      exact ⟨ThresholdCreationRepresentation.ofIsEmpty G⟩

/-- Every finite threshold graph admits a creation sequence. -/
theorem IsThreshold.nonempty_creationRepresentation [Finite V] (h : G.IsThreshold) :
    Nonempty (ThresholdCreationRepresentation G) := by
  classical
  let := Fintype.ofFinite V
  exact exists_creation_of_card_le (Fintype.card V) V G le_rfl h

/-- Creation sequences characterize finite threshold graphs. -/
theorem isThreshold_iff_nonempty_creationRepresentation [Finite V] :
    G.IsThreshold ↔ Nonempty (ThresholdCreationRepresentation G) :=
  ⟨IsThreshold.nonempty_creationRepresentation, fun ⟨R⟩ => R.isThreshold⟩

end SimpleGraph
