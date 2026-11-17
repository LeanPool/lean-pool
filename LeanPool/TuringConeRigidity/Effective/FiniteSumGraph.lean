/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteSumGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.TrimmedSumGraph

/-!
# Finite Sum Graph
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalCoding
universe u

theorem sum_graph_spec_with_internal_nodes (A : ZFSet.{u}) (hA : Transitive A) (a b : Ordinal.{u})
  (hω : ZFSet.omega.{u} ∈ A)
    (ha : a.toZFSet ∈ A) (hb : b.toZFSet ∈ A)
    (h0 : (∅ : ZFSet.{u}) ∈ A) (h1 : ({∅} : ZFSet.{u}) ∈ A)
    (hlocal : ∀ t < b, (a + t).toZFSet ∈ A ∧ SumCertificates (A) a t)
    (hnodes : sumDomain a.toZFSet b.toZFSet ⊆ A)
    (z : ZFSet.{u}) (hz : z ∈ A) :
    trimmedSumGraphSentence.Sat (A : Set ZFSet)
      (cons z (cons a.toZFSet (cons b.toZFSet (cons ∅ (fun _ => {∅}))))) ↔
        ∃ x ∈ sumDomain a.toZFSet b.toZFSet, z = ZFSet.pair x (sumValue a x) := by
  exact trimmedSumGraphSentence_spec_of_internal_nodes
    A hA a b hω ha hb h0 h1 hlocal hnodes z hz

end TuringRigidity.OrdinalArithmetic

end OAI
