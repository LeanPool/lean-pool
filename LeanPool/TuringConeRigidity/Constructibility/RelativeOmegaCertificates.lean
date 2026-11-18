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
  exact omegaGraph_below_of_successor_graph M C x hx ho f hf hg

theorem ProductCertificates.context (M : ZFSet.{u}) (C : Context M)
    (hRep : SigmaReplacement M) (a b : Ordinal.{u})
    (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) : ProductCertificates M a b := by
  exact ProductCertificates.of_context M C hRep a b ha hb

theorem OmegaPowerCertificates.schemas (M : ZFSet.{u}) (C : Context M)
    (hRep : SigmaReplacement M) (hColl : SigmaCollection M)
    (x : ZFSet.{u}) (hx : x ∈ M) (ho : x.IsOrdinal) : OmegaPowerCertificates M x := by
  exact OmegaPowerCertificates.of_schemas M C hRep hColl x hx ho

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
