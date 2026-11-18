/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/ConstructionHeightDomains.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.InternalHeightDomains
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalConstruction

/-!
# Construction Height Domains
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u
attribute [local irreducible] Construction.ownRealsMembership SentenceForm.bound

theorem Construction.largest_domain_definition (t : Construction.{u}) :
    ∃ q : SentenceForm, ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∀ P : Oracle, P ∈ modelReals M → t.Certified (groundReals M) P → t.Indexed M →
        ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧
          ∀ a : Ordinal.{u}, a.toZFSet ∈ M → β ≤ a →
            let R := groundReals M
            let δ := a - ordinalHeight (seed R) + 1
            δ.toZFSet ∈ M ∧ t.value R P ∈ level R δ ∧
            (∀ i, t.ordinalInputs P i ∈ level R δ) ∧
            (∀ e : ℕ → ZFSet.{u}, e 0 ∈ level R δ →
              (largestOrdinalSentence.Sat (level R δ : Set ZFSet) e ↔ e 0 = a.toZFSet)) ∧
            ∀ z ∈ level R δ,
              q.Sat (level R δ : Set ZFSet) (cons z (t.ordinalInputs P)) ↔ z ∈ t.value R P := by
  obtain ⟨q,hq⟩ := t.ordinal_definition
  refine ⟨q,?_⟩
  intro M hM hT P hP ht hi
  obtain ⟨γ,hγ,hγspec⟩ := hq M hM hT P hP ht hi
  obtain ⟨β,hβ,hβspec⟩ := internal_domains_with_largest_ordinal M (groundReals M) hM hT
    (groundReals_mem M hM hT) γ hγ
  refine ⟨β,hβ,?_⟩
  intro a ha hle
  obtain ⟨hδ,hγδ,_,hmax⟩ := hβspec a ha hle
  obtain ⟨hv,he,hq⟩ := hγspec _ hδ hγδ
  exact ⟨hδ,hv,he,hmax,hq⟩

end TuringRigidity.RelativeConstructible

end OAI
