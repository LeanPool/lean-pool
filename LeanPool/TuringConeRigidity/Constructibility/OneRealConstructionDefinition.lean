/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/OneRealConstructionDefinition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.DecodedConstructionSyntax

/-!
# One Real Construction Definition
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel OrdinalCoding
universe u
attribute [local irreducible] Construction.ownRealsMembership SentenceForm.bound

theorem Construction.cofinal_one_real_definition (t : Construction.{u}) :
    ∃ p : SentenceForm, p.bound ≤ 2 ∧
      ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∀ P : Oracle, P ∈ modelReals M → t.Certified (groundReals M) P → t.Indexed M →
      ∀ θ : Ordinal.{u}, θ.toZFSet ∈ M →
      ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧ θ < β ∧ realSeedOffset < β ∧
        (heightDomainIndex (paddedCode t.ordinalVector β)).toZFSet ∈ M ∧
        (realCode P ∈ level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β))) ∧
        t.value (groundReals M) P = definedSubset
          (level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β))) p
          (fun _ : Fin p.bound => realCode P) := by
  obtain ⟨q,hq⟩ := t.largest_domain_definition
  refine ⟨t.decodedOrdinalBody q,t.decodedOrdinalBody_bound q,?_⟩
  intro M hM hT P hP ht hi θ hθ
  obtain ⟨γ,hγ,hbody⟩ := hq M hM hT P hP ht hi
  have hv := t.ordinalVector_internal M hM hT hi
  obtain ⟨β,hβ,hmaxβ,hoff,hidx,hcert⟩ := cofinal_padded_code_certificates M hM hT
    t.ordinalVector hv (max θ γ) (internal_ordinal_max M hθ hγ)
  have hθβ : θ < β := (le_max_left _ _).trans_lt hmaxβ
  have hγcode : γ ≤ paddedCode t.ordinalVector β :=
    ((le_max_right _ _).trans hmaxβ.le).trans (padding_lt_paddedCode t.ordinalVector β).le
  have hcode := paddedCode_internal M hM hT t.ordinalVector β hv hβ
  obtain ⟨_,hvalue,henv,_,hmem⟩ := hbody (paddedCode t.ordinalVector β) hcode hγcode
  rw [ground_seed_offset M hM hT] at hvalue henv hmem
  refine ⟨β,hβ,hθβ,hoff,hidx,henv 0,?_⟩
  apply definedSubset_of_membership _ _ (level_transitive _ _) hvalue (t.decodedOrdinalBody q)
    (fun _ => realCode P)
  intro z hz
  exact (t.decodedOrdinalBody_spec q M hM hT P β hoff.le hcert henv z).trans (hmem z hz)

end TuringRigidity.RelativeConstructible

end OAI
