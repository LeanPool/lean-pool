/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativePersistentExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativePersistentDescent

/-!
# Relative Persistent Extension
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions
universe u

theorem persistent_extension_in_relativeModel (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    ∃ σ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
      Extends hIM ρ σ ∧ Persistent (modelIdeal M hM hT) σ ∧
      automorphismSet σ ∈ relativeModel M (groundReals M) := by
  obtain ⟨σ,he,hσ⟩ := PersistentExtension.source_4_1_10 I (modelIdeal M hM hT) ρ hρ hz hIM
    (modelIdeal_jump M hM hT)
  exact ⟨σ,he,hσ,persistent_modelIdeal_graph_mem_relativeModel M hM hT σ hσ⟩

theorem persistent_extension_in_model (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    ∃ σ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
      Extends hIM ρ σ ∧ Persistent (modelIdeal M hM hT) σ ∧ automorphismSet σ ∈ M := by
  obtain ⟨σ,he,hσ,hmem⟩ := persistent_extension_in_relativeModel M hM hT I ρ hρ hz hIM
  exact ⟨σ,he,hσ,relativeModel_subset M _ hmem⟩

end TuringRigidity.RelativeConstructible

end OAI
