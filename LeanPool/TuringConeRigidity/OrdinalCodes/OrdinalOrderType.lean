/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalOrderType.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.MostowskiCollapse
public import Mathlib.SetTheory.ZFC.Ordinal

/-!
# Ordinal Order Type
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

def TransitiveOn (d r : ZFSet.{u}) : Prop :=
  ∀ x ∈ d, ∀ y ∈ d, ∀ z ∈ d,
    ZFSet.pair x y ∈ r → ZFSet.pair y z ∈ r → ZFSet.pair x z ∈ r

def TotalOn (d r : ZFSet.{u}) : Prop :=
  ∀ x ∈ d, ∀ y ∈ d, x = y ∨ ZFSet.pair x y ∈ r ∨ ZFSet.pair y x ∈ r

theorem value_isOrdinal {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) (x : ZFSet.{u}) (hx : x ∈ d) :
    (value d r wf x).IsOrdinal := by
  induction x using wf.induction with
  | h x ih =>
    apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
    constructor
    · intro y hy z hz
      obtain ⟨b,hb,hbx,rfl⟩ := (mem_value d r wf x y).mp hy
      obtain ⟨a,ha,hab,rfl⟩ := (mem_value d r wf b z).mp hz
      exact (mem_value d r wf x _).mpr ⟨a,ha,ht a ha b hb x hx hab hbx,rfl⟩
    · intro y hy
      obtain ⟨a,ha,hax,rfl⟩ := (mem_value d r wf x y).mp hy
      exact ih a ⟨ha,hax⟩ ha

theorem total_extensional {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (ht : TotalOn d r) : Extensional d r := by
  intro x hx y hy he
  rcases ht x hx y hy with h|h|h
  · exact h
  · exact False.elim (wf.irrefl.irrefl x ⟨hx,(he x hx).mpr h⟩)
  · exact False.elim (wf.irrefl.irrefl y ⟨hy,(he y hy).mp h⟩)

noncomputable def ordinalRange (d r : ZFSet.{u}) (wf : WellFounded (Rel d r)) : ZFSet.{u} :=
  ZFSet.range (fun s : Conditions d => value d r wf (label d s))

theorem mem_ordinalRange (d r : ZFSet.{u}) (wf : WellFounded (Rel d r)) (z : ZFSet.{u}) :
    z ∈ ordinalRange d r wf ↔ ∃ x ∈ d, z = value d r wf x := by
  rw [ordinalRange,ZFSet.mem_range]
  constructor
  · rintro ⟨s,hs⟩; exact ⟨label d s,label_mem d s,hs.symm⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨s,rfl⟩ := label_surjective d hx
    exact ⟨s,rfl⟩

theorem ordinalRange_isOrdinal {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) : (ordinalRange d r wf).IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  constructor
  · intro x hx y hy
    obtain ⟨a,_,rfl⟩ := (mem_ordinalRange d r wf x).mp hx
    obtain ⟨b,hb,_,rfl⟩ := (mem_value d r wf a y).mp hy
    exact (mem_ordinalRange d r wf _).mpr ⟨b,hb,rfl⟩
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := (mem_ordinalRange d r wf x).mp hx
    exact value_isOrdinal wf ht a ha

noncomputable def orderType (d r : ZFSet.{u}) (wf : WellFounded (Rel d r)) : Ordinal.{u} :=
  (ordinalRange d r wf).rank

theorem orderType_toZFSet {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) : (orderType d r wf).toZFSet = ordinalRange d r wf :=
  (ordinalRange_isOrdinal wf ht).toZFSet_rank_eq

theorem orderType_value_lt {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (x : ZFSet.{u}) (hx : x ∈ d) :
    (value d r wf x).rank < orderType d r wf := by
  apply ZFSet.rank_lt_of_mem
  exact (mem_ordinalRange d r wf _).mpr ⟨x,hx,rfl⟩

theorem orderType_internal (M d r : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (hr : r ∈ M) (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) :
    (orderType d r wf).toZFSet ∈ M ∧
      ∃ f ∈ M, Graph d r d (orderType d r wf).toZFSet f ∧
        ∀ z ∈ (orderType d r wf).toZFSet, ∃ x ∈ d, ZFSet.pair x z ∈ f := by
  obtain ⟨f,hf,hg⟩ := internal_graph M d r hM hP hU hPow hS hR hd hr wf
  have heq : graphRange d f = ordinalRange d r wf := by
    apply ZFSet.ext; intro z
    exact (hg.range_iff wf z).trans (mem_ordinalRange d r wf z).symm
  have hm : ordinalRange d r wf ∈ M := heq ▸ graphRange_mem M hM hU hS hd hf
  rw [orderType_toZFSet wf ht]
  refine ⟨hm,f,hf,?_,?_⟩
  · refine ⟨(fun _ hx => hx),(fun _ _ _ hy _ => hy),?_,?_,?_⟩
    · intro z hz
      obtain ⟨x,hx,rfl⟩ := (hg.mem_iff wf z).mp hz
      exact ⟨x,hx,_,(mem_ordinalRange d r wf _).mpr ⟨x,hx,rfl⟩,rfl⟩
    · intro x hx
      refine ⟨value d r wf x,(mem_ordinalRange d r wf _).mpr ⟨x,hx,rfl⟩,
        (hg.mem_iff wf _).mpr ⟨x,hx,rfl⟩,?_⟩
      intro z _ hxz
      obtain ⟨y,_,he⟩ := (hg.mem_iff wf _).mp hxz
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      rfl
    · intro x hx z _ hxz
      obtain ⟨y,hy,he⟩ := (hg.mem_iff wf _).mp hxz
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      constructor
      · intro z hz
        obtain ⟨y,hy,hyx,rfl⟩ := (mem_value d r wf x z).mp hz
        exact ⟨y,hy,hyx,(hg.mem_iff wf _).mpr ⟨y,hy,rfl⟩⟩
      · intro y hy hyx z _ hyz
        obtain ⟨w,_,he⟩ := (hg.mem_iff wf _).mp hyz
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
        exact (mem_value d r wf x _).mpr ⟨y,hy,hyx,rfl⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (mem_ordinalRange d r wf z).mp hz
    exact ⟨x,hx,(hg.mem_iff wf _).mpr ⟨x,hx,rfl⟩⟩

end TuringRigidity.RelationCollapse

end OAI
