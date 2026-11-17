/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/ProductCertificateCollection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalProductClosure
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalProductSyntax

/-!
# Product Certificate Collection
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

/-- A sigma formula requesting an ordinal-product certificate with all auxiliary sets inside
the given bound. -/
def productBundleSigma : SigmaFormula :=
  .existsSet (.existsSet (.existsSet (.existsSet (.bounded
    (.conj (productMatrix 3 5 6 2 1 0)
      (.conj (.member 2 4) (.conj (.member 1 4)
        (.conj (.member 0 4) (.member 3 4)))))))))

theorem productBundleSigma_spec (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    productBundleSigma.Realize M e ↔
      ZFSet.prod b.toZFSet a.toZFSet ∈ e 0 ∧ productRelation a.toZFSet b.toZFSet ∈ e 0 ∧
        ∃ f ∈ e 0, OrderTypeCertificate (ZFSet.prod b.toZFSet a.toZFSet)
          (productRelation a.toZFSet b.toZFSet) (a*b).toZFSet f ∧ (a*b).toZFSet ∈ e 0 := by
  have sem (c d r f : ZFSet.{u}) (hc : c ∈ M) (hd : d ∈ M) (hr : r ∈ M) (hf : f ∈ M) :
      (Formula.conj (productMatrix 3 5 6 2 1 0)
        (.conj (.member 2 4) (.conj (.member 1 4) (.conj (.member 0 4) (.member 3 4))))).Realize M
          (cons f (cons r (cons d (cons c e)))) ↔
        (d = ZFSet.prod b.toZFSet a.toZFSet ∧ r = productRelation a.toZFSet b.toZFSet ∧
          OrderTypeCertificate d r c f) ∧ d ∈ e 0 ∧ r ∈ e 0 ∧ f ∈ e 0 ∧ c ∈ e 0 := by
    rw [Formula.absolute _ M hM _ (by
      intro i; rcases i with _|_|_|_|i
      · exact hf
      · exact hr
      · exact hd
      · exact hc
      · exact he i)]
    simp only [Formula.Eval,productMatrix_eval,cons_zero,cons_succ,ha,hb]
  change (∃ c ∈ M, ∃ d ∈ M, ∃ r ∈ M, ∃ f ∈ M, _) ↔ _
  constructor
  · rintro ⟨c,hc,d,hd,r,hr,f,hf,h⟩
    obtain ⟨⟨rfl,rfl,hcert⟩,hd0,hr0,hf0,hc0⟩ := (sem c d r f hc hd hr hf).mp h
    have eq := hcert.exact (productRelation_wellFounded a b) (productRelation_transitive a b)
    rw [product_orderType] at eq
    subst c
    exact ⟨hd0,hr0,f,hf0,hcert,hc0⟩
  · rintro ⟨hd,hr,f,hf,hcert,hc⟩
    exact ⟨_,hM _ (he 0) _ hc,_,hM _ (he 0) _ hd,_,hM _ (he 0) _ hr,
      f,hM _ (he 0) _ hf,(sem _ _ _ f (hM _ (he 0) _ hc) (hM _ (he 0) _ hd)
        (hM _ (he 0) _ hr) (hM _ (he 0) _ hf)).mpr ⟨⟨rfl,rfl,hcert⟩,hd,hr,hf,hc⟩⟩

theorem product_certificate_collection (M : ZFSet.{u}) (C : Context M)
    (hRep : SigmaReplacement M) (hColl : SigmaCollection M)
    (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) :
    ∃ U ∈ M, ∀ c < a,
      ZFSet.prod b.toZFSet c.toZFSet ∈ U ∧ productRelation c.toZFSet b.toZFSet ∈ U ∧
        ∃ f ∈ U, OrderTypeCertificate (ZFSet.prod b.toZFSet c.toZFSet)
          (productRelation c.toZFSet b.toZFSet) (c*b).toZFSet f ∧ (c*b).toZFSet ∈ U := by
  obtain ⟨W,hW,hcover⟩ := hColl productBundleSigma (fun _ => b.toZFSet) (fun _ => hb)
    a.toZFSet ha (by
      intro x hx
      obtain ⟨c,hca,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
      have hc := C.transitive _ ha _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hca)
      obtain ⟨hprod,f,hf,hcert⟩ := ordinal_mul_internal_schemas M C.transitive C.pairing
        C.union C.power C.separation hRep c b hc hb
      have hd := product_mem M C.transitive C.pairing C.union C.power C.separation hb hc
      have hr := productRelation_mem M _ _ C.transitive C.pairing C.union C.power C.separation hc hb
      let B := FiniteTuple.elements [ZFSet.prod b.toZFSet c.toZFSet,
        productRelation c.toZFSet b.toZFSet,f,(c*b).toZFSet]
      have hB : B ∈ M := FiniteTuple.elements_mem M C.transitive C.pairing C.union
        (C.transitive _ C.omega_mem _ ZFSet.omega_zero) _ (by
          intro y hy
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
          rcases hy with rfl|rfl|rfl|rfl <;> assumption)
      refine ⟨B,hB,(productBundleSigma_spec M C.transitive _ (by
        intro i
        rcases i with _ | _ | i
        · exact hB
        · exact hc
        · exact hb) c b rfl rfl).mpr ?_⟩
      have hm (y : ZFSet.{u}) : y ∈ B ↔ y ∈ [ZFSet.prod b.toZFSet c.toZFSet,
          productRelation c.toZFSet b.toZFSet,f,(c*b).toZFSet] := FiniteTuple.mem_elements _ _
      exact ⟨(hm _).mpr (by simp),(hm _).mpr (by simp),f,(hm _).mpr (by simp),hcert,
        (hm _).mpr (by simp)⟩)
  refine ⟨ZFSet.sUnion W,union_mem M C.transitive C.union hW,?_⟩
  intro c hc
  obtain ⟨B,hB,hcert⟩ := hcover c.toZFSet (Ordinal.toZFSet_mem_toZFSet_iff.mpr hc)
  obtain ⟨hd,hr,f,hf,hcert,hp⟩ := (productBundleSigma_spec M C.transitive _ (by
    intro i; rcases i with _|_|i
    · exact C.transitive _ hW _ hB
    · exact C.transitive _ ha _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hc)
    · exact hb) c b rfl rfl).mp hcert
  exact ⟨ZFSet.mem_sUnion.mpr ⟨B,hB,hd⟩,ZFSet.mem_sUnion.mpr ⟨B,hB,hr⟩,
    f,ZFSet.mem_sUnion.mpr ⟨B,hB,hf⟩,hcert,ZFSet.mem_sUnion.mpr ⟨B,hB,hp⟩⟩

end TuringRigidity.OrdinalArithmetic

end OAI
