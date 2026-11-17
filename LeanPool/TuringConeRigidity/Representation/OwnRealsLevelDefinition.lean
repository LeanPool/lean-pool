/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/OwnRealsLevelDefinition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.OwnRealsConstruction
public import LeanPool.TuringConeRigidity.Constructibility.FiniteDefinitionTransfer
public import LeanPool.TuringConeRigidity.OrdinalCodes.LevelInlinedDefinition

/-!
# Own Reals Level Definition
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetDegreeDecoding PersistentRestrictions
universe u

theorem Construction.ownReals_at_level (t : Construction.{u}) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (P : Oracle)
    (hP : P ∈ modelReals M) (ht : t.Certified (groundReals M) P) (hi : t.Indexed M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
      t.value (groundReals M) P ∈ level (groundReals M) γ ∧
      (∀ i, t.ownRealsInputs (groundReals M) P i ∈ level (groundReals M) γ) ∧
      ∀ z ∈ level (groundReals M) γ,
        t.ownRealsMembership.Sat (level (groundReals M) γ : Set ZFSet)
          (cons z (t.ownRealsInputs (groundReals M) P)) ↔ z ∈ t.value (groundReals M) P := by
  obtain ⟨γ,hγ,hv,he,_⟩ := t.inlined_at_level M hM hT P hP ht hi
  have hR := groundReals_mem M hM hT
  have hsame := groundReals_between M (level (groundReals M) γ)
    (level_transitive _ γ) (level_subset_model M _ hM hT hR γ hγ) (he 0)
  exact ⟨γ,hγ,hv,t.ownRealsInputs_mem _ _ P he,
    t.ownRealsMembership_spec _ _ (level_transitive _ γ) hsame P ht he hv⟩

theorem Construction.ownReals_subset_at_level (t : Construction.{u}) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (P : Oracle)
    (hP : P ∈ modelReals M) (ht : t.Certified (groundReals M) P) (hi : t.Indexed M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
      (∀ i, t.ownRealsInputs (groundReals M) P i ∈ level (groundReals M) γ) ∧
      t.value (groundReals M) P = definedSubset (level (groundReals M) γ) t.ownRealsMembership
        (fun i : Fin t.ownRealsMembership.bound => t.ownRealsInputs (groundReals M) P i) := by
  obtain ⟨γ,hγ,hv,he,hf⟩ := t.ownReals_at_level M hM hT P hP ht hi
  exact ⟨γ,hγ,he,definedSubset_of_membership _ _ (level_transitive _ γ) hv
    t.ownRealsMembership (t.ownRealsInputs (groundReals M) P) hf⟩

theorem persistent_extension_ownReals_subset (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    ∃ σ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
      Extends hIM ρ σ ∧ Persistent (modelIdeal M hM hT) σ ∧
      ∃ (t : Construction.{u}) (P : Oracle) (γ : Ordinal.{u}),
        P ∈ modelReals M ∧ t.Indexed M ∧ t.Certified (groundReals M) P ∧ γ.toZFSet ∈ M ∧
        (∀ i, t.ownRealsInputs (groundReals M) P i ∈ level (groundReals M) γ) ∧
        automorphismSet σ = definedSubset (level (groundReals M) γ) t.ownRealsMembership
          (fun i : Fin t.ownRealsMembership.bound => t.ownRealsInputs (groundReals M) P i) := by
  obtain ⟨σ,he,hσ,t,P,hP,hi,ht,hval⟩ := persistent_extension_construction M hM hT I ρ hρ hz hIM
  obtain ⟨γ,hγ,hin,hdef⟩ := t.ownReals_subset_at_level M hM hT P hP ht hi
  exact ⟨σ,he,hσ,t,P,γ,hP,hi,ht,hγ,hin,hval ▸ hdef⟩

end TuringRigidity.RelativeConstructible

end OAI
