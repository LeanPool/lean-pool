/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/FinitePresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.TrimmedPresentation

/-!
# Finite Presentation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible
universe u

theorem presentation_graph_at_successor_of_pairs (R : ZFSet.{u}) (γ : Ordinal.{u})
    (d r : ZFSet.{u}) (o : Ordinal.{u})
    (j : ZFSet.{u} → ZFSet.{u})
    (hpairs : ∀ x ∈ d, ZFSet.pair x (j x) ∈ level R γ)
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y)
    (p : SentenceForm) (e : ℕ → ZFSet.{u}) (henv : ∀ i, e i ∈ level R γ)
    (hp : ∀ z ∈ level R γ, p.Sat (level R γ : Set ZFSet) (cons z e) ↔
      ∃ x ∈ d, z = ZFSet.pair x (j x)) :
    ∃ f ∈ level R (γ+1), OrderTypeCertificate d r o.toZFSet f := by
  exact presentation_graph_mem_successor_of_pairs
    R γ d r o j hpairs hj hs he p e henv hp

end TuringRigidity.RelationCollapse

end OAI
