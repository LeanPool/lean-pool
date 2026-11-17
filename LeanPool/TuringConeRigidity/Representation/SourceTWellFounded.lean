/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SourceTWellFounded.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.SelectorOrdinalEnumeration

/-!
# Source TWell Founded
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace InternalWellOrder

theorem sourceT_internal_ordinal_ranking (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hw : InternallyWellFounded M d r) :
    ∃ δ ∈ M, δ.IsOrdinal ∧ ∃ F ∈ M, TransitiveNameModel.FunctionGraph δ d F ∧
      (∀ x ∈ d, ∃ i ∈ δ, ZFSet.pair i x ∈ F) ∧
      (∀ i ∈ δ, ∀ j ∈ δ, ∀ x y, ZFSet.pair i x ∈ F → ZFSet.pair j y ∈ F →
        ZFSet.pair y x ∈ r → j ∈ i) := by
  obtain ⟨q,hq,s,hsM,hs,hqdef,hmin⟩ := internal_minimal_selector M hM hT hd hr hw
  obtain ⟨δ,hδM,hδ,F,hFM,hF,honto,hinj,hchoice⟩ := internal_enumeration_from_selector M hM
    hT.pairing hT.union hT.powerSet hT.separation.finitePrefix hT.replacement.finitePrefix
    hT.infinity hd hq hsM hs hqdef
  refine ⟨δ,hδM,hδ,F,hFM,hF,honto,?_⟩
  intro i hi j hj x y hix hjy hyx
  have hx := hF.value_mem hix
  have hy := hF.value_mem hjy
  obtain ⟨a,_,hrem,hax⟩ := hchoice i hi x hx hix
  by_contra hji
  have hya : y ∈ a := (hrem.2 y hy).mpr (by
    rintro ⟨k,hki,hky⟩
    have hkj := hinj k (hδ.subset_of_mem hi hki) j hj y hky hjy
    exact hji (hkj ▸ hki))
  exact (hmin a x hax).2 y hya hyx

theorem sourceT_wellFounded (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hon : On d r)
    (hw : InternallyWellFounded M d r) : WellFounded (Rel d r) := by
  classical
  obtain ⟨δ,_,_,F,_,_,honto,hrank⟩ := sourceT_internal_ordinal_ranking M hM hT hd hr hw
  let index (x : ZFSet.{u}) : ZFSet.{u} := if hx : x ∈ d then (honto x hx).choose else ∅
  have hi (x : ZFSet.{u}) (hx : x ∈ d) : index x ∈ δ ∧ ZFSet.pair (index x) x ∈ F := by
    simp only [index,dite_eq_left hx]
    exact (honto x hx).choose_spec
  apply (show WellFounded (fun y x => index y ∈ index x) from InvImage.wf index ZFSet.mem_wf).mono
  intro y x hyx
  have hx : x ∈ d := by
    obtain ⟨y',_,x',hx,he⟩ := ZFSet.mem_prod.mp (hon hyx.2)
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact hx
  exact hrank _ (hi x hx).1 _ (hi y hyx.1).1 x y (hi x hx).2 (hi y hyx.1).2 hyx.2

theorem internallyWellFounded_of_wellFounded (M d r : ZFSet.{u})
    (hw : WellFounded (Rel d r)) : InternallyWellFounded M d r := by
  classical
  intro a _ had hne
  have find (x : ZFSet.{u}) : x ∈ a → ∃ y, MinimalIn r a y := by
    induction x using hw.induction with
    | h x ih =>
      intro hx
      by_cases he : ∃ y ∈ a, ZFSet.pair y x ∈ r
      · obtain ⟨y,hy,hyx⟩ := he
        exact ih y ⟨had hy,hyx⟩ hy
      · exact ⟨x,hx,fun y hy hyx => he ⟨y,hy,hyx⟩⟩
  obtain ⟨x,hx⟩ := hne
  exact find x hx

theorem sourceT_wellFounded_absolute (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hon : On d r) :
    InternallyWellFounded M d r ↔ WellFounded (Rel d r) :=
  ⟨sourceT_wellFounded M hM hT hd hr hon,internallyWellFounded_of_wellFounded M d r⟩

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
