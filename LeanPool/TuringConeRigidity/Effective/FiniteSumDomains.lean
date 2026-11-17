/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteSumDomains.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.TrimmedSumDomains

/-!
# Finite Sum Domains
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem sum_domain_at_successor_of_subset (R : ZFSet.{u}) (γ : Ordinal.{u})
    {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ)
    (h0 : (∅ : ZFSet.{u}) ∈ level R γ) (h1 : ({∅} : ZFSet.{u}) ∈ level R γ)
    (hd : sumDomain a b ⊆ level R γ) :
    sumDomain a b ∈ level R (γ+1) := by
  exact sum_domain_mem_successor_of_subset R γ ha hb h0 h1 hd

theorem sum_relation_at_successor_of_subset (R : ZFSet.{u}) (γ : Ordinal.{u})
    {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ)
    (h0 : (∅ : ZFSet.{u}) ∈ level R γ) (h1 : ({∅} : ZFSet.{u}) ∈ level R γ)
    (hd : sumDomain a b ⊆ level R γ)
    (hsub : sumRelation a b ⊆ level R γ) :
    sumRelation a b ∈ level R (γ+1) := by
  exact sum_relation_mem_successor_of_subset R γ ha hb h0 h1 hd hsub

end TuringRigidity.OrdinalArithmetic

end OAI
