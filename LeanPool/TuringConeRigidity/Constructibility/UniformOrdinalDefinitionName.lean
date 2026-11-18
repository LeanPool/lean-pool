/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformOrdinalDefinitionName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformOrdinalStageName
public import LeanPool.TuringConeRigidity.Constructibility.UniformDefinedSubsetName

/-!
# Uniform Ordinal Definition Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
open AtomicForcing BoundedForcing
universe u

theorem uniform_ordinal_definition_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (δ : Ordinal.{u}) (hδ : δ.toZFSet ∈ M) (X : ZFSet.{u}) (hX : X ∈ M) (φ : SentenceForm) :
    ∃ f : Name (Conditions c), f.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        f.val G.carrier = definedSubset
          (level (groundReals (genericExtensionSet M c G.carrier)) δ)
            φ (fun _ : Fin φ.bound => X) := by
  obtain ⟨A,hA,hAv⟩ := uniform_ordinal_level_name M hM hT hc hoM ho δ hδ
  obtain ⟨f,hf,hfv⟩ := uniform_checked_definition_name M hM hT hc hoM ho A hA X hX φ
  exact ⟨f,hf,fun G hG ht => by rw [hfv G hG ht,hAv G hG ht]⟩

end TuringRigidity.RelativeConstructible

end OAI
