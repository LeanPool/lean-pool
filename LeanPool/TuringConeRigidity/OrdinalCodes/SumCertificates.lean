/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/SumCertificates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalSumClosure

/-!
# Sum Certificates
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions
universe u

/-- Model-membership and order-type certificates for the tagged presentation of an ordinal
sum. -/
def SumCertificates (M : ZFSet.{u}) (a b : Ordinal.{u}) : Prop :=
  sumDomain a.toZFSet b.toZFSet ∈ M ∧ sumRelation a.toZFSet b.toZFSet ∈ M ∧
    ∃ f ∈ M, OrderTypeCertificate (sumDomain a.toZFSet b.toZFSet)
      (sumRelation a.toZFSet b.toZFSet) (a+b).toZFSet f

theorem SumCertificates.context (M : ZFSet.{u}) (C : Context M)
    (hRep : SigmaReplacement M) (a b : Ordinal.{u})
    (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) : SumCertificates M a b := by
  have h0 := C.transitive _ C.omega_mem _ ZFSet.omega_zero
  obtain ⟨_,f,hf,hc⟩ := ordinal_add_internal_schemas M C.transitive C.pairing C.union
    C.power C.separation hRep h0 a b ha hb
  exact ⟨sumDomain_mem M _ _ C.transitive C.pairing C.union C.power C.separation h0 ha hb,
    sumRelation_mem M _ _ C.transitive C.pairing C.union C.power C.separation h0 ha hb,
    f,hf,hc⟩

theorem SumCertificates.mono {M N : ZFSet.{u}} {a b : Ordinal.{u}}
    (h : SumCertificates M a b) (hMN : M ⊆ N) : SumCertificates N a b :=
  ⟨hMN h.1,hMN h.2.1,let ⟨f,hf,hc⟩ := h.2.2; ⟨f,hMN hf,hc⟩⟩

theorem sumSentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a b : Ordinal.{u}) (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet)
    (hc : SumCertificates M a b) (hy : e 0 = (a + b).toZFSet) :
    sumSentence.Sat (M : Set ZFSet) e := by
  have h1 : ({∅} : ZFSet.{u}) ∈ M := by
    have h := hM _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
    simpa [natSet] using h
  exact (sumSentence_spec_of_certificate M hM e he a b ha hb
    (hM _ hω _ ZFSet.omega_zero) h1 hc.1 hc.2.1 hc.2.2).mpr hy

end TuringRigidity.OrdinalArithmetic

end OAI
