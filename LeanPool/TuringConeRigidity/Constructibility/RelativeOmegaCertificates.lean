/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeOmegaCertificates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RestrictedOmegaRecursion
public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaPowerCertificates
public import LeanPool.TuringConeRigidity.Constructibility.RelativeDefCertificates
public import LeanPool.TuringConeRigidity.Constructibility.RelativeModelOrdinals

/-!
# Relative Omega Certificates
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem internal_omegaGraph_below_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement
  M) (hColl : SigmaCollection M)
    (x : ZFSet.{u}) (hx : x ∈ M) (ho : x.IsOrdinal) :
    ∃ f ∈ M, OmegaGraph M x (iterUnion 2 f) f := by
  obtain ⟨f,hf,hg⟩ := internal_omegaGraph_schemas M C hRep hColl x hx ho
  let p : Formula := .existsMem 1 (.existsMem 3 (.orderedPair 2 1 0))
  let e : ℕ → ZFSet.{u} := cons x (fun _ => iterUnion 2 f)
  let g := ZFSet.sep (fun z => p.Eval (cons z e)) f
  have hgM : g ∈ M := sep_mem M C.transitive C.separation p e
    (by
      intro i
      cases i
      · exact hx
      · exact iterUnion_mem M C.transitive C.union hf 2) hf
  have hm (z : ZFSet.{u}) : z ∈ g ↔ ∃ t ∈ x, z = ZFSet.pair t (omegaNext t) := by
    change z ∈ ZFSet.sep _ f ↔ _
    simp only [ZFSet.mem_sep,p,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ]
    change (z ∈ f ∧ ∃ t ∈ x, ∃ v ∈ iterUnion 2 f, z = ZFSet.pair t v) ↔ _
    constructor
    · rintro ⟨hz,t,ht,v,hv,rfl⟩
      exact ⟨t,ht,by rw [hg.correct t (ZFSet.mem_insert_of_mem x ht) v hv hz]⟩
    · rintro ⟨t,ht,rfl⟩
      have hp := (hg.mem_iff _).mpr ⟨t,ZFSet.mem_insert_of_mem x ht,rfl⟩
      exact ⟨hp,t,ht,_,second_mem_doubleUnion hp,rfl⟩
  exact ⟨g,hgM,omegaGraph_of_mem_iff_context M x g C hx hgM ho hm⟩

theorem ProductCertificates.context (M : ZFSet.{u}) (C : Context M)
    (hRep : SigmaReplacement M) (a b : Ordinal.{u})
    (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) : ProductCertificates M a b := by
  obtain ⟨_,f,hf,hc⟩ := ordinal_mul_internal_schemas M C.transitive C.pairing C.union
    C.power C.separation hRep a b ha hb
  exact ⟨product_mem M C.transitive C.pairing C.union C.power C.separation hb ha,
    productRelation_mem M _ _ C.transitive C.pairing C.union C.power C.separation ha hb,
    f,hf,hc⟩

theorem OmegaPowerCertificates.schemas (M : ZFSet.{u}) (C : Context M)
    (hRep : SigmaReplacement M) (hColl : SigmaCollection M)
    (x : ZFSet.{u}) (hx : x ∈ M) (ho : x.IsOrdinal) : OmegaPowerCertificates M x := by
  obtain ⟨f,hf,hg⟩ := internal_omegaGraph_below_schemas M C hRep hColl x hx ho
  refine ⟨hx,f,hf,_,iterUnion_mem M C.transitive C.union hf 2,hg,?_⟩
  intro t ht
  have htM := C.transitive _ hx t ht
  exact ProductCertificates.context M C hRep _ _
    (ordinal_omega_opow_schemas M C hRep hColl t.rank
      ((hg.1.mem ht).toZFSet_rank_eq.symm ▸ htM)) (toZFSet_omega.symm ▸ C.omega_mem)

theorem relative_omega_power_certificates (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) :
    OmegaPowerCertificates (relativeModel M (groundReals M)) a.toZFSet :=
  OmegaPowerCertificates.schemas _ (ground_relative_context M hM hT)
    (relativeModel_sigma_replacement M _ hM hT (groundReals_mem M hM hT))
    (relativeModel_sigma_collection M _ hM hT (groundReals_mem M hM hT))
    a.toZFSet ((ground_relativeModel_ordinal_iff M hM hT a).mpr ha) (ZFSet.isOrdinal_toZFSet a)

theorem relative_omega_power_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) :
    (Ordinal.omega0 ^ a).toZFSet ∈ relativeModel M (groundReals M) :=
  ordinal_omega_opow_schemas _ (ground_relative_context M hM hT)
    (relativeModel_sigma_replacement M _ hM hT (groundReals_mem M hM hT))
    (relativeModel_sigma_collection M _ hM hT (groundReals_mem M hM hT))
    a ((ground_relativeModel_ordinal_iff M hM hT a).mpr ha)

end TuringRigidity.OrdinalArithmetic

end OAI
