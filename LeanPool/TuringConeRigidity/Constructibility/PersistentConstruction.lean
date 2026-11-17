/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/PersistentConstruction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.ConstructionDefinition
public import LeanPool.TuringConeRigidity.Constructibility.RelativePersistentExtension

/-!
# Persistent Construction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding PersistentRestrictions
universe u

theorem persistent_graph_construction (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT)
    (hρ : Persistent (modelIdeal M hM hT) ρ) :
    ∃ t : Construction.{u}, ∃ P : Oracle, P ∈ modelReals M ∧
      t.Indexed M ∧ t.Certified (groundReals M) P ∧
      t.value (groundReals M) P = automorphismSet ρ :=
  construction_of_relativeModel M hM hT _
    (persistent_modelIdeal_graph_mem_relativeModel M hM hT ρ hρ)

theorem persistent_extension_construction (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    ∃ σ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
      Extends hIM ρ σ ∧ Persistent (modelIdeal M hM hT) σ ∧
      ∃ t : Construction.{u}, ∃ P : Oracle, P ∈ modelReals M ∧
        t.Indexed M ∧ t.Certified (groundReals M) P ∧
        t.value (groundReals M) P = automorphismSet σ := by
  obtain ⟨σ,he,hσ,hm⟩ := persistent_extension_in_relativeModel M hM hT I ρ hρ hz hIM
  exact ⟨σ,he,hσ,construction_of_relativeModel M hM hT _ hm⟩

theorem persistent_graph_definition (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT)
    (hρ : Persistent (modelIdeal M hM hT) ρ) :
    ∃ (o : Ordinal.{u}) (n : ℕ) (p : SentenceForm)
      (c : Fin n → Construction.{u}) (P : Oracle),
      o.toZFSet ∈ M ∧ P ∈ modelReals M ∧
      (Construction.define o n p c).Indexed M ∧
      (Construction.define o n p c).Certified (groundReals M) P ∧
      satisfactionSet (level (groundReals M) o) ∈ M ∧
      ∀ z, z ∈ automorphismSet ρ ↔ z ∈ level (groundReals M) o ∧
        p.Sat (level (groundReals M) o : Set ZFSet)
          (cons z (tupleEnv (fun i => (c i).value (groundReals M) (realPart P i)))) :=
  construction_definition_of_relativeModel M hM hT _
    (persistent_modelIdeal_graph_mem_relativeModel M hM hT ρ hρ)

end TuringRigidity.RelativeConstructible

end OAI
