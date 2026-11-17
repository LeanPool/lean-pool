/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalOrdinalSubset.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalOrderType
public import LeanPool.TuringConeRigidity.Representation.SourceTheory

/-!
# Internal Ordinal Subset
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalOrdinalSubset
open TransitiveNameModel BoundedSetTheory RelationCollapse

/-- The membership-order relation on the elements of `D`. -/
noncomputable def memberOrder (D : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod D D).sep (fun z => ∃ x ∈ D, ∃ y ∈ D, z = ZFSet.pair x y ∧ x ∈ y)

theorem pair_memberOrder (D x y : ZFSet.{0}) :
    ZFSet.pair x y ∈ memberOrder D ↔ x ∈ D ∧ y ∈ D ∧ x ∈ y := by
  simp only [memberOrder,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x',hx,y',hy,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hx,hy,h⟩
  · rintro ⟨hx,hy,h⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hx,hy⟩,x,hx,y,hy,rfl,h⟩

theorem memberOrder_mem (M D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hD : D ∈ M) : memberOrder D ∈ M := by
  simpa only [memberOrder,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0) (.member 1 0))))
      (fun _ => D) (fun _ => hD)
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hD hD)

theorem memberOrder_wf (D : ZFSet.{0}) : WellFounded (Rel D (memberOrder D)) :=
  ZFSet.mem_wf.mono (fun _ _ h => ((pair_memberOrder D _ _).mp h.2).2.2)

theorem memberOrder_transitive (K D : ZFSet.{0}) (hK : K.IsOrdinal) (hD : D ⊆ K) :
    TransitiveOn D (memberOrder D) := by
  intro x hx y _ z hz hxy hyz
  exact (pair_memberOrder D x z).mpr ⟨hx,hz,(hK.mem (hD hz)).mem_trans
    ((pair_memberOrder D x y).mp hxy).2.2 ((pair_memberOrder D y z).mp hyz).2.2⟩

theorem memberOrder_total (K D : ZFSet.{0}) (hK : K.IsOrdinal) (hD : D ⊆ K) :
    TotalOn D (memberOrder D) := by
  intro x hx y hy
  rcases (hK.mem (hD hx)).mem_trichotomous (hK.mem (hD hy)) with h|h|h
  · exact Or.inr (Or.inl ((pair_memberOrder D x y).mpr ⟨hx,hy,h⟩))
  · exact Or.inl h
  · exact Or.inr (Or.inr ((pair_memberOrder D y x).mpr ⟨hy,hx,h⟩))

theorem value_subset (K D x : ZFSet.{0}) (hK : K.IsOrdinal) (hD : D ⊆ K) (hx : x ∈ D) :
    value D (memberOrder D) (memberOrder_wf D) x ⊆ x := by
  induction x using (memberOrder_wf D).induction with
  | h x ih =>
    intro z hz
    obtain ⟨y,hy,hyx,rfl⟩ := (mem_value D _ _ x z).mp hz
    have hv := value_isOrdinal (memberOrder_wf D) (memberOrder_transitive K D hK hD) y hy
    have hs := (hv.subset_iff_eq_or_mem (hK.mem (hD hy))).mp (ih y ⟨hy,hyx⟩ hy)
    have hyx' := ((pair_memberOrder D y x).mp hyx).2.2
    exact hs.elim (fun h => h.symm ▸ hyx')
      (fun h => (hK.mem (hD hx)).mem_trans h hyx')

theorem range_subset (K D : ZFSet.{0}) (hK : K.IsOrdinal) (hD : D ⊆ K) :
    ordinalRange D (memberOrder D) (memberOrder_wf D) ⊆ K := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := (mem_ordinalRange D _ _ z).mp hz
  exact (value_isOrdinal (memberOrder_wf D) (memberOrder_transitive K D hK hD) x
    hx).mem_of_subset_of_mem
    hK (value_subset K D x hK hD hx) (hD hx)

theorem internal_subset_orderType (M K D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K.IsOrdinal) (hD : D ∈ M) (hDK : D ⊆ K) :
    ∃ J ∈ M, J.IsOrdinal ∧ J ⊆ K ∧ ∃ f ∈ M, FunctionGraph D J f ∧
      (∀ x ∈ D, ∀ x' ∈ D, ∀ y ∈ J, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x') ∧
      (∀ y ∈ J, ∃ x ∈ D, ZFSet.pair x y ∈ f) := by
  let wf := memberOrder_wf D
  have ht := memberOrder_transitive K D hK hDK
  obtain ⟨hJ,f,hf,hg,honto⟩ := orderType_internal M D (memberOrder D) hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hD
    (memberOrder_mem M D hM hT hD) wf ht
  refine ⟨(orderType D (memberOrder D) wf).toZFSet,hJ,ZFSet.isOrdinal_toZFSet _,?_,f,hf,?_,?_,honto⟩
  · rw [orderType_toZFSet wf ht]
    exact range_subset K D hK hDK
  · exact ⟨hg.2.2.1,hg.2.2.2.1⟩
  · intro x hx x' hx' y hy hxy hx'y
    apply value_injective wf (total_extensional wf (memberOrder_total K D hK hDK)) x hx x' hx'
    exact (hg.correct wf x hx y hy hxy).symm.trans (hg.correct wf x' hx' y hy hx'y)

end TuringRigidity.InternalOrdinalSubset

end OAI
