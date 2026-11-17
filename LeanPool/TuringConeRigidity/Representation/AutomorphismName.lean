/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/AutomorphismName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.AutomorphismUnion
public import LeanPool.TuringConeRigidity.CohenForcing.CohenSymmetry
public import LeanPool.TuringConeRigidity.Representation.SourceEquationTail

/-!
# Automorphism Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AutomorphismName
open Set CountableForcing AutomorphismUnion
variable {P Q α : Type*} [Preorder P] [Preorder Q]

/-- A set-valued forcing name represented as a relation between conditions and possible
values. -/
abbrev SetName (P α : Type*) := Set (P × α)

/-- Interpret a set name by the values whose tagging conditions belong to the filter. -/
def interpret (N : SetName P α) (G : GenericFilter P) : Set α :=
  {x | ∃ p ∈ G.carrier, (p,x) ∈ N}

/-- Transport a set name along an order isomorphism of forcing posets. -/
def rename (e : P ≃o Q) (N : SetName P α) : SetName Q α :=
  {t | (e.symm t.1,t.2) ∈ N}

/-- Transport a condition filter along an order isomorphism. -/
def mapFilter (e : P ≃o Q) (G : GenericFilter P) : GenericFilter Q where
  carrier := {q | e.symm q ∈ G.carrier}
  nonempty := by
    obtain ⟨p,hp⟩ := G.nonempty
    exact ⟨e p,by simpa using hp⟩
  upper := fun hpq hp => G.upper (e.symm.monotone hpq) hp
  directed := by
    intro p q hp hq
    obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
    exact ⟨e r,by simpa using hr,by simpa using e.monotone hrp,by simpa using e.monotone hrq⟩

theorem interpret_rename (e : P ≃o Q) (N : SetName P α) (G : GenericFilter P) :
    interpret (rename e N) (mapFilter e G) = interpret N G := by
  ext x
  constructor
  · rintro ⟨q,hq,hN⟩
    exact ⟨e.symm q,hq,hN⟩
  · rintro ⟨p,hp,hN⟩
    exact ⟨e p,by simpa [mapFilter] using hp,by simpa [rename] using hN⟩

/-- The set name for the union of the graphs of the partial ideal automorphisms. -/
def graphName : SetName Approximation (Degree × Degree) :=
  {t | ∃ ha : t.2.1 ∈ t.1.ideal.carrier, (t.1.map ⟨t.2.1,ha⟩).val = t.2.2}

theorem interpret_graphName (G : GenericFilter Approximation) (a b : Degree) :
    (a,b) ∈ interpret graphName G ↔ Graph G a b := Iff.rfl

theorem graphName_represents (G : GenericFilter Approximation) (a : Domain G) (b : Degree) :
    (a.val,b) ∈ interpret graphName G ↔ (automorphism G a).val = b :=
  (automorphism_graph G a b).symm

/-- Lift a set name to a product poset by tagging it with top in the second factor. -/
def liftFirst [OrderTop Q] (N : SetName P α) : SetName (P × Q) α :=
  {t | t.1.2 = ⊤ ∧ (t.1.1,t.2) ∈ N}

theorem interpret_liftFirst [OrderTop Q] (N : SetName P α)
    (G : GenericFilter P) (H : GenericFilter Q) :
    interpret (liftFirst N) (SourceEquationTail.productFilter G H) = interpret N G := by
  ext x
  constructor
  · rintro ⟨⟨p,q⟩,⟨hp,hq⟩,he,hN⟩
    exact ⟨p,hp,hN⟩
  · rintro ⟨p,hp,hN⟩
    obtain ⟨q,hq⟩ := H.nonempty
    exact ⟨(p,⊤),⟨hp,H.upper le_top hq⟩,rfl,hN⟩

theorem liftFirst_tail_invariant {ι : Type*} (N : SetName P α) (m : ι → Bool) :
    rename (CohenSymmetry.tailIso m) (liftFirst N) = liftFirst N := by
  ext t
  change ((CohenSymmetry.flipIso m).symm t.1.2 = ⊤ ∧ (t.1.1,t.2) ∈ N) ↔
    (t.1.2 = ⊤ ∧ (t.1.1,t.2) ∈ N)
  apply and_congr _ Iff.rfl
  constructor
  · intro h
    have he := congrArg (CohenSymmetry.flipIso m) h
    simpa using he
  · intro h
    rw [h]
    exact (CohenSymmetry.flipIso m).symm.map_top

theorem invariant_automorphism_name {ι : Type*} :
    ∃ N : SetName (Approximation × CohenSymmetry.Condition ι) (Degree × Degree),
      (∀ m, rename (CohenSymmetry.tailIso m) N = N) ∧
      ∀ (G : GenericFilter Approximation) (H : GenericFilter (CohenSymmetry.Condition ι))
        (a : Domain G) (b : Degree),
        (a.val,b) ∈ interpret N (SourceEquationTail.productFilter G H) ↔
          (automorphism G a).val = b := by
  refine ⟨liftFirst graphName,fun m => liftFirst_tail_invariant graphName m,?_⟩
  intro G H a b
  rw [interpret_liftFirst]
  exact graphName_represents G a b

end TuringRigidity.AutomorphismName

end OAI
