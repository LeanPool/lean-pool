/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaPowerCertificates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
The context certificate proofs are shared from upstream
Constructibility/RelativeOmegaCertificates.lean.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaPowerSyntax
public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaPowerDefinability

/-!
# Omega Power Certificates
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

/-- Model-membership and order-type certificates for the lexicographic presentation of an
ordinal product. -/
def ProductCertificates (M : ZFSet.{u}) (a b : Ordinal.{u}) : Prop :=
  ZFSet.prod b.toZFSet a.toZFSet ∈ M ∧ productRelation a.toZFSet b.toZFSet ∈ M ∧
    ∃ f ∈ M, OrderTypeCertificate (ZFSet.prod b.toZFSet a.toZFSet)
      (productRelation a.toZFSet b.toZFSet) (a*b).toZFSet f

/-- Ordinal product certificates require only the context and replacement schema. -/
theorem ProductCertificates.of_context (M : ZFSet.{u}) (C : SetModelFunctions.Context M)
    (hRep : SigmaReplacement M) (a b : Ordinal.{u})
    (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) : ProductCertificates M a b := by
  obtain ⟨_,f,hf,hc⟩ := ordinal_mul_internal_schemas M C.transitive C.pairing C.union
    C.power C.separation hRep a b ha hb
  exact ⟨product_mem M C.transitive C.pairing C.union C.power C.separation hb ha,
    productRelation_mem M _ _ C.transitive C.pairing C.union C.power C.separation ha hb,
    f,hf,hc⟩

theorem ProductCertificates.sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) : ProductCertificates M a b := by
  let C : SetModelFunctions.Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  exact ProductCertificates.of_context M C hT.replacement.finitePrefix a b ha hb

theorem ProductCertificates.mono {M N : ZFSet.{u}} {a b : Ordinal.{u}}
    (h : ProductCertificates M a b) (hMN : M ⊆ N) : ProductCertificates N a b :=
  ⟨hMN h.1,hMN h.2.1,let ⟨f,hf,hc⟩ := h.2.2; ⟨f,hMN hf,hc⟩⟩

theorem ordinalProductAt_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (v a b : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (α β : Ordinal.{u}) (ha : e a = α.toZFSet) (hb : e b = β.toZFSet)
    (hc : ProductCertificates M α β) (hv : e v = (α * β).toZFSet) :
    (ordinalProductAt v a b).Sat (M : Set ZFSet) e := by
  rw [ordinalProductAt,SentenceForm.sat_rename]
  exact (productSentence_spec_of_certificate M hM
    (fun i => e (if i = 0 then v else if i = 1 then a else b)) (fun i => he _) α β ha hb
    hc.1 hc.2.1 hc.2.2).mpr hv

/-- An omega-power hierarchy graph together with certificates for its intermediate ordinal
products. -/
def OmegaPowerCertificates (M x : ZFSet.{u}) : Prop :=
  x ∈ M ∧ ∃ f ∈ M, ∃ r ∈ M, OmegaGraph M (x) r f ∧
    ∀ t ∈ x, ProductCertificates M (Ordinal.omega0 ^ t.rank) Ordinal.omega0

/-- Omega-power certificates follow from the explicit recursion schemas. -/
theorem OmegaPowerCertificates.of_schemas (M : ZFSet.{u}) (C : SetModelFunctions.Context M)
    (hRep : SigmaReplacement M) (hColl : SigmaCollection M)
    (x : ZFSet.{u}) (hx : x ∈ M) (ho : x.IsOrdinal) : OmegaPowerCertificates M x := by
  obtain ⟨f',hf',hg'⟩ := internal_omegaGraph_of_schemas M C hRep hColl x hx ho
  obtain ⟨f,hf,hg⟩ := omegaGraph_below_of_successor_graph M C x hx ho f' hf' hg'
  refine ⟨hx,f,hf,_,iterUnion_mem M C.transitive C.union hf 2,hg,?_⟩
  intro t ht
  have htM := C.transitive _ hx t ht
  exact ProductCertificates.of_context M C hRep _ _
    (ordinal_omega_opow_of_schemas M C hRep hColl t.rank
      ((hg.1.mem ht).toZFSet_rank_eq.symm ▸ htM)) (toZFSet_omega.symm ▸ C.omega_mem)

theorem OmegaPowerCertificates.sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (x : ZFSet.{u}) (hx : x ∈ M) (ho : x.IsOrdinal) : OmegaPowerCertificates M x := by
  let C : SetModelFunctions.Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hColl := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
  exact OmegaPowerCertificates.of_schemas M C hT.replacement.finitePrefix hColl x hx ho

theorem OmegaPowerCertificates.mono {M N x : ZFSet.{u}}
    (h : OmegaPowerCertificates M x) (hMN : M ⊆ N) : OmegaPowerCertificates N x := by
  obtain ⟨hd,f,hf,r,hr,hg,hp⟩ := h
  refine ⟨hMN hd,f,hMN hf,r,hMN hr,⟨hg.1,hg.2.1,?_⟩,fun t ht => (hp t ht).mono hMN⟩
  intro t ht v hv hfv
  obtain ⟨A,hA,hs,ho,he⟩ := hg.2.2 t ht v hv hfv
  exact ⟨A,hMN hA,hs,ho,he⟩

theorem omegaGraphSentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hs : e 3 = (1 : Ordinal.{u}).toZFSet) (hw : e 4 = ZFSet.omega)
    (hg : OmegaGraph M (e 0) (e 1) (e 2))
    (hp : ∀ t ∈ e 0, ProductCertificates M (Ordinal.omega0 ^ t.rank) Ordinal.omega0) :
    (omegaGraphSentence 3 4 0 1 2).Sat (M : Set ZFSet) e := by
  apply (omegaGraphSentence_semantics M hM 3 4 0 1 2 e he).mpr
  refine ⟨hg.1,hg.2.1,?_⟩
  intro t ht v hv hfv
  obtain ⟨A,hA,hst,ho,hval⟩ := hg.2.2 t ht v hv hfv
  have hAe := omegaStageStep_exact hg ht hst
  refine ⟨A,hA,hs.symm ▸ hst,ho,?_⟩
  apply ordinalProductAt_of_certificates M hM 1 0 7 (cons A (cons v (cons t e)))
    (fun i => by
      rcases i with _|_|_|i
      · exact hA
      · exact hM _ (he 1) v hv
      · exact hM _ (he 0) t ht
      · exact he i)
    (Ordinal.omega0 ^ t.rank) Ordinal.omega0 hAe (by simpa using hw.trans toZFSet_omega.symm) (hp
      t ht)
  simpa only [cons_zero,cons_succ,hAe,Ordinal.rank_toZFSet] using hval

theorem omegaPowerSentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hc : OmegaPowerCertificates M (e 1))
    (hy : e 0 = (Ordinal.omega0 ^ (e 1).rank).toZFSet) :
    omegaPowerSentence.Sat (M : Set ZFSet) e := by
  obtain ⟨hd,f,hf,r,hr,hg,hp⟩ := hc
  have hs : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact hM _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
  have hst := omegaStageStep_domain M (e 1) r f hg
  apply (omegaPowerSentence_semantics M hM hω e he).mpr
  refine ⟨_,hω,_,hs,f,hf,r,hr,_,hd,rfl,rfl,rfl,?_,hy.symm ▸ hst⟩
  exact omegaGraphSentence_of_certificates M hM _ (by
    intro i; rcases i with _|_|_|_|_|i
    · exact hd
    · exact hr
    · exact hf
    · exact hs
    · exact hω
    · exact he i) rfl rfl hg hp

end TuringRigidity.OrdinalArithmetic

end OAI
