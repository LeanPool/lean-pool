/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/CollectionHierarchySyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.HierarchySyntax

/-!
# Collection Hierarchy Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u
theorem hierarchyGraph_sigmaDefinable_collection {M : ZFSet.{u}} (C : Context M) (hRep :
  SigmaReplacement M) (hColl : SigmaCollection M) (s d r f : ℕ) :
    SigmaDefinable M (fun e => HierarchyGraph M (e s) (e d) (e r) (e f)) := by
  exact hierarchyGraph_sigmaDefinable_context C hRep hColl s d r f

theorem uniform_hierarchy_certificate_collection (M R d q : ZFSet.{u}) (C : Context M) (hRep :
  SigmaReplacement M) (hColl : SigmaCollection M) (hs : seed R ∈ M) (hdM : d ∈ M) (hqM : q ∈ M)
    (hd : Transitive d) (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) :
    ∃ p : SigmaFormula, ∃ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ M) ∧
      ∀ x ∈ d, ∀ f ∈ M, p.Realize M (cons f (cons x a)) ↔
        ∃ r ∈ M, HierarchyGraph M (seed R) (hull d q x) r f := by
  exact uniform_hierarchy_certificate_context M R d q C hRep hColl hs hdM hqM hd hq

end TuringRigidity.RelativeConstructible

end OAI
