/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalProductPresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalProductSets

/-!
# Ordinal Product Presentation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

noncomputable def productValue (a : Ordinal.{u}) (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃ s t, x = ZFSet.pair s t then
    (a * h.choose.rank + h.choose_spec.choose.rank).toZFSet else ∅

theorem productValue_pair (a : Ordinal.{u}) (s t : ZFSet.{u}) :
    productValue a (ZFSet.pair s t) = (a*s.rank+t.rank).toZFSet := by
  classical
  have h : ∃ v w, ZFSet.pair s t = ZFSet.pair v w := ⟨s,t,rfl⟩
  simp only [productValue,dite_eq_left h]
  obtain ⟨hs,ht⟩ := ZFSet.pair_inj.mp h.choose_spec.choose_spec
  exact congrArg Ordinal.toZFSet (congrArg₂ (fun c d : ZFSet.{u} => a*c.rank+d.rank) hs ht).symm

theorem productValue_mem (a b : Ordinal.{u}) (x : ZFSet.{u})
    (hx : x ∈ ZFSet.prod b.toZFSet a.toZFSet) : productValue a x ∈ (a*b).toZFSet := by
  obtain ⟨s,hs,t,ht,rfl⟩ := ZFSet.mem_prod.mp hx
  obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
  obtain ⟨d,hd,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
  rw [productValue_pair,Ordinal.rank_toZFSet,Ordinal.rank_toZFSet,Ordinal.toZFSet_mem_toZFSet_iff]
  exact Ordinal.lt_mul_iff.mpr ⟨c,hc,d,hd,rfl⟩

theorem productValue_surjective (a b : Ordinal.{u}) (z : ZFSet.{u})
    (hz : z ∈ (a * b).toZFSet) :
    ∃ x ∈ ZFSet.prod b.toZFSet a.toZFSet, productValue a x = z := by
  obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
  obtain ⟨q,hq,r,hr,rfl⟩ := Ordinal.lt_mul_iff.mp hc
  refine ⟨ZFSet.pair q.toZFSet r.toZFSet,ZFSet.mem_prod.mpr
    ⟨_,Ordinal.toZFSet_mem_toZFSet_iff.mpr hq,_,Ordinal.toZFSet_mem_toZFSet_iff.mpr hr,rfl⟩,?_⟩
  rw [productValue_pair,Ordinal.rank_toZFSet,Ordinal.rank_toZFSet]

theorem productValue_lt_iff (a s t v w : Ordinal.{u}) (ht : t < a) (hw : w < a) :
    a*s+t < a*v+w ↔ s < v ∨ (s = v ∧ t < w) := by
  have step (s t v w : Ordinal.{u}) (ht : t < a) (hsv : s < v) :
      a*s+t < a*v+w := by
    have h := (Ordinal.lt_mul_iff.mpr ⟨s,hsv,t,ht,rfl⟩ : a*s+t < a*v)
    exact h.trans_le le_self_add
  constructor
  · intro h
    rcases lt_trichotomy s v with hsv|rfl|hvs
    · exact Or.inl hsv
    · exact Or.inr ⟨rfl,(add_lt_add_iff_left _).mp h⟩
    · exact False.elim ((not_lt_of_gt (step v w s t hw hvs)) h)
  · rintro (hsv|⟨rfl,htw⟩)
    · exact step s t v w ht hsv
    · exact (add_lt_add_iff_left _).mpr htw

theorem productValue_relation (a b : Ordinal.{u}) (x : ZFSet.{u})
    (hx : x ∈ ZFSet.prod b.toZFSet a.toZFSet) (y : ZFSet.{u})
    (hy : y ∈ ZFSet.prod b.toZFSet a.toZFSet) :
    ZFSet.pair x y ∈ productRelation a.toZFSet b.toZFSet ↔
      productValue a x ∈ productValue a y := by
  rw [pair_mem_productRelation,and_iff_right hx,and_iff_right hy]
  obtain ⟨s,hs,t,ht,rfl⟩ := ZFSet.mem_prod.mp hx
  obtain ⟨v,hv,w,hw,rfl⟩ := ZFSet.mem_prod.mp hy
  rw [productLess_pair]
  simp only [hs,ht,hv,hw,true_and,productValue_pair]
  obtain ⟨s,hs,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
  obtain ⟨t,ht,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
  obtain ⟨v,hv,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hv
  obtain ⟨w,hw,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hw
  simp only [Ordinal.rank_toZFSet,Ordinal.toZFSet_mem_toZFSet_iff,Ordinal.toZFSet_injective.eq_iff]
  exact (productValue_lt_iff a s t v w (Ordinal.toZFSet_mem_toZFSet_iff.mp ht)
    (Ordinal.toZFSet_mem_toZFSet_iff.mp hw)).symm

theorem productRelation_wellFounded (a b : Ordinal.{u}) :
    WellFounded (Rel (ZFSet.prod b.toZFSet a.toZFSet) (productRelation a.toZFSet b.toZFSet)) := by
  apply (InvImage.wf (productValue a) ZFSet.mem_wf).mono
  intro x y h
  exact (productValue_relation a b x h.1 y (right_mem (productRelation_on _ _) h.2)).mp h.2

theorem productRelation_transitive (a b : Ordinal.{u}) :
    TransitiveOn (ZFSet.prod b.toZFSet a.toZFSet) (productRelation a.toZFSet b.toZFSet) := by
  intro x hx y hy z hz hxy hyz
  apply (productValue_relation a b x hx z hz).mpr
  exact ((ZFSet.isOrdinal_toZFSet (a*b)).mem (productValue_mem a b z hz)).subset_of_mem
    ((productValue_relation a b y hy z hz).mp hyz) ((productValue_relation a b x hx y hy).mp hxy)

theorem product_orderType (a b : Ordinal.{u}) :
    orderType (ZFSet.prod b.toZFSet a.toZFSet) (productRelation a.toZFSet b.toZFSet)
      (productRelation_wellFounded a b) = a*b :=
  orderType_of_ordinal_presentation _ _ _ _ (productValue a)
    (productValue_mem a b) (productValue_surjective a b) (productValue_relation a b)

theorem ordinal_mul_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) :
    (a*b).toZFSet ∈ M ∧ ∃ f ∈ M,
      Presents (ZFSet.prod b.toZFSet a.toZFSet) f (productValue a) ∧
      OrderTypeCertificate (ZFSet.prod b.toZFSet a.toZFSet)
        (productRelation a.toZFSet b.toZFSet) (a*b).toZFSet f :=
  ordinal_internal_of_presentation M _ _ _ hM hT
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hb ha)
    (productRelation_mem M _ _ hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded ha hb)
    (productRelation_on _ _) (productValue a) (productValue_mem a b)
    (productValue_surjective a b) (productValue_relation a b)

end TuringRigidity.OrdinalArithmetic

end OAI
