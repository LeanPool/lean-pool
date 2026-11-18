/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaCertificateCollection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeOmegaCertificates
public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaRecursionSchemas

/-!
# Omega Certificate Collection
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem omega_bundle_sigma (M : ZFSet.{u}) (C : Context M)
    (hRep : SigmaReplacement M) (hColl : SigmaCollection M) :
    ∃ p : SigmaFormula, ∃ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ M) ∧
      ∀ x ∈ M, ∀ B ∈ M, p.Realize M (cons B (cons x e)) ↔
        ∃ f ∈ M, ∃ r ∈ M, f ∈ B ∧ r ∈ B ∧ OmegaGraph M x r f := by
  have hm := ((member_definable C 1 2).and (member_definable C 0 2)).toSigma C.transitive
  have hg := omegaGraph_sigmaDefinable_schemas M C hRep hColl 3 0 1
  have h := (hm.and hg).existsSet.existsSet
  apply sigma_binary_relation _ (h.congr ?_)
  intro e _
  simp only [cons_zero,cons_succ]
  apply exists_congr; intro f
  apply and_congr_right; intro _
  apply exists_congr; intro r
  apply and_congr_right; intro _
  exact and_assoc

theorem omega_graph_collection (M : ZFSet.{u}) (C : Context M)
    (hRep : SigmaReplacement M) (hColl : SigmaCollection M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) :
    ∃ U ∈ M, ∀ c ≤ a, ∃ f ∈ U, ∃ r ∈ U, OmegaGraph M c.toZFSet r f := by
  obtain ⟨p,e,he,hp⟩ := omega_bundle_sigma M C hRep hColl
  have hs : (a+1).toZFSet ∈ M := by
    rw [Ordinal.toZFSet_add_one]
    exact insert_self_mem M C.transitive C.pairing C.union ha
  obtain ⟨W,hW,hcover⟩ := hColl p e he (a+1).toZFSet hs (by
    intro x hx
    have hxM := C.transitive _ hs _ hx
    obtain ⟨f,hf,hg⟩ := internal_omegaGraph_below_schemas M C hRep hColl x hxM
      ((ZFSet.isOrdinal_toZFSet (a+1)).mem hx)
    have hr := iterUnion_mem M C.transitive C.union hf 2
    have hB := pair_mem M C.transitive C.pairing hf hr
    refine ⟨{f,iterUnion 2 f},hB,(hp x hxM _ hB).mpr ?_⟩
    exact ⟨f,hf,_,hr,ZFSet.mem_pair.mpr (Or.inl rfl),ZFSet.mem_pair.mpr (Or.inr rfl),hg⟩)
  refine ⟨ZFSet.sUnion W,union_mem M C.transitive C.union hW,?_⟩
  intro c hc
  have hcs : c.toZFSet ∈ (a+1).toZFSet :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr (hc.trans_lt (lt_add_one a))
  obtain ⟨B,hB,h⟩ := hcover c.toZFSet hcs
  obtain ⟨f,_,r,_,hf,hr,hg⟩ := (hp c.toZFSet (C.transitive _ hs _ hcs)
    B (C.transitive _ hW _ hB)).mp h
  exact ⟨f,ZFSet.mem_sUnion.mpr ⟨B,hB,hf⟩,r,ZFSet.mem_sUnion.mpr ⟨B,hB,hr⟩,hg⟩

end TuringRigidity.OrdinalArithmetic

end OAI
