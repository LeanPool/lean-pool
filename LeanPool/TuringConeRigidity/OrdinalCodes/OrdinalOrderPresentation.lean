/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalOrderPresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalOrderTypeSyntax

/-!
# Ordinal Order Presentation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

theorem value_of_ordinal_presentation (d r : ZFSet.{u}) (o : Ordinal.{u})
    (wf : WellFounded (Rel d r)) (j : ZFSet.{u} → ZFSet.{u})
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y)
    (x : ZFSet.{u}) (hx : x ∈ d) : value d r wf x = j x := by
  induction x using wf.induction with
  | h x ih =>
    apply ZFSet.ext; intro z
    rw [mem_value]
    constructor
    · rintro ⟨y,hy,hyx,rfl⟩
      rw [ih y ⟨hy,hyx⟩ hy]
      exact (he y hy x hx).mp hyx
    · intro hz
      have hzo := (ZFSet.isOrdinal_toZFSet o).subset_of_mem (hj x hx) hz
      obtain ⟨y,hy,hyz⟩ := hs z hzo
      have hyx : ZFSet.pair y x ∈ r := (he y hy x hx).mpr (hyz ▸ hz)
      exact ⟨y,hy,hyx,hyz.symm.trans (ih y ⟨hy,hyx⟩ hy).symm⟩

theorem orderType_of_ordinal_presentation (d r : ZFSet.{u}) (o : Ordinal.{u})
    (wf : WellFounded (Rel d r)) (j : ZFSet.{u} → ZFSet.{u})
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y) :
    orderType d r wf = o := by
  have hr : ordinalRange d r wf = o.toZFSet := by
    apply ZFSet.ext; intro z
    rw [mem_ordinalRange]
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [value_of_ordinal_presentation d r o wf j hj hs he x hx]
      exact hj x hx
    · intro hz
      obtain ⟨x,hx,heq⟩ := hs z hz
      exact ⟨x,hx,heq.symm.trans (value_of_ordinal_presentation d r o wf j hj hs he x hx).symm⟩
  unfold orderType
  rw [hr,Ordinal.rank_toZFSet]

theorem ordinal_internal_of_presentation (M d r : ZFSet.{u}) (o : Ordinal.{u})
    (hM : Transitive M) (hT : SourceT M) (hd : d ∈ M) (hr : r ∈ M) (hon : On d r)
    (j : ZFSet.{u} → ZFSet.{u})
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y) :
    o.toZFSet ∈ M ∧ ∃ f ∈ M, Presents d f j ∧ OrderTypeCertificate d r o.toZFSet f := by
  have wf : WellFounded (Rel d r) := by
    apply (InvImage.wf j ZFSet.mem_wf).mono
    intro x y hxy
    exact (he x hxy.1 y (right_mem hon hxy.2)).mp hxy.2
  have ht : TransitiveOn d r := by
    intro x hx y hy z hz hxy hyz
    apply (he x hx z hz).mpr
    exact ((ZFSet.isOrdinal_toZFSet o).mem (hj z hz)).subset_of_mem
      ((he y hy z hz).mp hyz) ((he x hx y hy).mp hxy)
  have hval := value_of_ordinal_presentation d r o wf j hj hs he
  have heq := orderType_of_ordinal_presentation d r o wf j hj hs he
  obtain ⟨ha,f,hf,hc⟩ := orderTypeCertificate_exists M d r hM hT hd hr wf ht
  rw [heq] at ha hc
  refine ⟨ha,f,hf,?_,hc⟩
  intro z
  rw [hc.2.1.mem_iff wf]
  apply exists_congr; intro x
  apply and_congr_right; intro hx
  rw [hval x hx]

end TuringRigidity.RelationCollapse

end OAI
