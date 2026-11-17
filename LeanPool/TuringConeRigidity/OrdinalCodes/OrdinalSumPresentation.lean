/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalSumPresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalSumSets

/-!
# Ordinal Sum Presentation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

theorem rightNode_ne_leftNode (x y : ZFSet.{u}) : rightNode x ≠ leftNode y :=
  (leftNode_ne_rightNode y x).symm

attribute [local simp] leftNode_inj rightNode_inj leftNode_ne_rightNode rightNode_ne_leftNode

theorem sumLess_left_left (a b s t : ZFSet.{u}) :
    SumLess a b (leftNode s) (leftNode t) ↔ s ∈ a ∧ t ∈ a ∧ s ∈ t := by
  simp [SumLess]

theorem sumLess_left_right (a b s t : ZFSet.{u}) :
    SumLess a b (leftNode s) (rightNode t) ↔ s ∈ a ∧ t ∈ b := by
  simp [SumLess]

theorem sumLess_right_left (a b s t : ZFSet.{u}) :
    ¬ SumLess a b (rightNode s) (leftNode t) := by
  simp [SumLess]

theorem sumLess_right_right (a b s t : ZFSet.{u}) :
    SumLess a b (rightNode s) (rightNode t) ↔ s ∈ b ∧ t ∈ b ∧ s ∈ t := by
  simp [SumLess]

noncomputable def sumValue (a : Ordinal.{u}) (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃ s, x = leftNode s then h.choose
    else if k : ∃ s, x = rightNode s then (a + k.choose.rank).toZFSet else ∅

theorem sumValue_left (a : Ordinal.{u}) (s : ZFSet.{u}) :
    sumValue a (leftNode s) = s := by
  classical
  have h : ∃ t, leftNode s = leftNode t := ⟨s,rfl⟩
  simp only [sumValue, dite_eq_left h]
  exact (leftNode_inj.mp h.choose_spec).symm

theorem sumValue_right (a : Ordinal.{u}) (s : ZFSet.{u}) :
    sumValue a (rightNode s) = (a+s.rank).toZFSet := by
  classical
  have h : ¬ ∃ t, rightNode s = leftNode t := by simp
  have k : ∃ t, rightNode s = rightNode t := ⟨s,rfl⟩
  simp only [sumValue, dite_eq_right h, dite_eq_left k]
  rw [← rightNode_inj.mp k.choose_spec]

theorem sumValue_mem (a b : Ordinal.{u}) (x : ZFSet.{u})
    (hx : x ∈ sumDomain a.toZFSet b.toZFSet) : sumValue a x ∈ (a+b).toZFSet := by
  rcases (mem_sumDomain _ _ _).mp hx with ⟨s,hs,rfl⟩|⟨s,hs,rfl⟩
  · rw [sumValue_left]
    exact Ordinal.toZFSet_monotone le_self_add hs
  · obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
    rw [sumValue_right,Ordinal.rank_toZFSet,Ordinal.toZFSet_mem_toZFSet_iff]
    exact (add_lt_add_iff_left a).mpr hc

theorem sumValue_surjective (a b : Ordinal.{u}) (z : ZFSet.{u})
    (hz : z ∈ (a + b).toZFSet) :
    ∃ x ∈ sumDomain a.toZFSet b.toZFSet, sumValue a x = z := by
  obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
  by_cases h : c < a
  · exact ⟨leftNode c.toZFSet,(mem_sumDomain _ _ _).mpr
      (Or.inl ⟨c.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr h,rfl⟩),sumValue_left _ _⟩
  · have hle := le_of_not_gt h
    have hb : c-a < b := (Ordinal.sub_lt_of_le hle).mpr hc
    refine ⟨rightNode (c-a).toZFSet,(mem_sumDomain _ _ _).mpr
      (Or.inr ⟨(c-a).toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hb,rfl⟩),?_⟩
    rw [sumValue_right,Ordinal.rank_toZFSet,Ordinal.add_sub_cancel_of_le hle]

theorem sumValue_relation (a b : Ordinal.{u}) (x : ZFSet.{u})
    (hx : x ∈ sumDomain a.toZFSet b.toZFSet) (y : ZFSet.{u})
    (hy : y ∈ sumDomain a.toZFSet b.toZFSet) :
    ZFSet.pair x y ∈ sumRelation a.toZFSet b.toZFSet ↔ sumValue a x ∈ sumValue a y := by
  rw [pair_mem_sumRelation, and_iff_right hx, and_iff_right hy]
  rcases (mem_sumDomain _ _ _).mp hx with ⟨s,hs,rfl⟩|⟨s,hs,rfl⟩ <;>
    rcases (mem_sumDomain _ _ _).mp hy with ⟨t,ht,rfl⟩|⟨t,ht,rfl⟩
  · simp only [sumLess_left_left,hs,ht,true_and,sumValue_left]
  · rw [sumLess_left_right,sumValue_left,sumValue_right]
    exact iff_of_true ⟨hs,ht⟩ (Ordinal.toZFSet_monotone le_self_add hs)
  · rw [iff_false_left (sumLess_right_left _ _ _ _),sumValue_right,sumValue_left]
    obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
    rw [Ordinal.toZFSet_mem_toZFSet_iff]
    exact not_lt_of_ge (hc.le.trans le_self_add)
  · rw [sumLess_right_right,sumValue_right,sumValue_right]
    obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
    obtain ⟨d,hd,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
    simp only [Ordinal.toZFSet_mem_toZFSet_iff,hc,hd,true_and,Ordinal.rank_toZFSet,
      add_lt_add_iff_left]

theorem sumRelation_wellFounded (a b : Ordinal.{u}) :
    WellFounded (Rel (sumDomain a.toZFSet b.toZFSet) (sumRelation a.toZFSet b.toZFSet)) := by
  apply (InvImage.wf (sumValue a) ZFSet.mem_wf).mono
  intro x y h
  exact (sumValue_relation a b x h.1 y (right_mem (sumRelation_on _ _) h.2)).mp h.2

theorem sumRelation_transitive (a b : Ordinal.{u}) :
    TransitiveOn (sumDomain a.toZFSet b.toZFSet) (sumRelation a.toZFSet b.toZFSet) := by
  intro x hx y hy z hz hxy hyz
  apply (sumValue_relation a b x hx z hz).mpr
  exact ((ZFSet.isOrdinal_toZFSet (a+b)).mem (sumValue_mem a b z hz)).subset_of_mem
    ((sumValue_relation a b y hy z hz).mp hyz) ((sumValue_relation a b x hx y hy).mp hxy)

theorem sum_orderType (a b : Ordinal.{u}) :
    orderType (sumDomain a.toZFSet b.toZFSet) (sumRelation a.toZFSet b.toZFSet)
      (sumRelation_wellFounded a b) = a+b :=
  orderType_of_ordinal_presentation _ _ _ _ (sumValue a)
    (sumValue_mem a b) (sumValue_surjective a b) (sumValue_relation a b)

theorem ordinal_add_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) :
    (a+b).toZFSet ∈ M ∧ ∃ f ∈ M,
      Presents (sumDomain a.toZFSet b.toZFSet) f (sumValue a) ∧
      OrderTypeCertificate (sumDomain a.toZFSet b.toZFSet)
        (sumRelation a.toZFSet b.toZFSet) (a+b).toZFSet f := by
  have h0 := hM _ (omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity) _ ZFSet.omega_zero
  exact ordinal_internal_of_presentation M _ _ _ hM hT
    (sumDomain_mem M _ _ hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded h0
      ha hb)
    (sumRelation_mem M _ _ hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      h0 ha hb)
    (sumRelation_on _ _) (sumValue a) (sumValue_mem a b)
    (sumValue_surjective a b) (sumValue_relation a b)

end TuringRigidity.OrdinalArithmetic

end OAI
