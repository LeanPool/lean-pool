/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/MostowskiCollapse.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.CollapseCoding

/-!
# Mostowski Collapse
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

/-- The relation's predecessor sets distinguish any two elements of the designated domain. -/
def Extensional (d r : ZFSet.{u}) : Prop :=
  ∀ x ∈ d, ∀ y ∈ d, (∀ z ∈ d, ZFSet.pair z x ∈ r ↔ ZFSet.pair z y ∈ r) → x = y

theorem value_injective {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (he : Extensional d r) (x : ZFSet.{u}) (hx : x ∈ d) (y : ZFSet.{u}) (hy : y ∈ d)
    (hxy : value d r wf x = value d r wf y) : x = y := by
  induction x using wf.induction generalizing y with
  | h x ih =>
    apply he x hx y hy
    intro z hz
    constructor
    · intro hzx
      have hm : value d r wf z ∈ value d r wf y := hxy ▸
        (mem_value d r wf x _).mpr ⟨z,hz,hzx,rfl⟩
      obtain ⟨w,hw,hwy,hzw⟩ := (mem_value d r wf y _).mp hm
      have hzw' := ih z ⟨hz,hzx⟩ hz w hw hzw
      exact hzw' ▸ hwy
    · intro hzy
      have hm : value d r wf z ∈ value d r wf x := hxy.symm ▸
        (mem_value d r wf y _).mpr ⟨z,hz,hzy,rfl⟩
      obtain ⟨w,hw,hwx,hzw⟩ := (mem_value d r wf x _).mp hm
      have hwz := ih w ⟨hw,hwx⟩ hw z hz hzw.symm
      exact hwz ▸ hwx

theorem value_mem_iff {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (he : Extensional d r) {x y : ZFSet.{u}} (hx : x ∈ d) :
    value d r wf x ∈ value d r wf y ↔ ZFSet.pair x y ∈ r := by
  rw [mem_value]
  constructor
  · rintro ⟨z,hz,hzy,hxz⟩
    have hxz := value_injective wf he x hx z hz hxz
    exact hxz ▸ hzy
  · intro hxy
    exact ⟨x,hx,hxy,rfl⟩

/-- The output values assigned by the graph `f` to inputs in `d`. -/
noncomputable def graphRange (d f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun v => ∃ x ∈ d, ZFSet.pair x v ∈ f) (iterUnion 2 f)

theorem mem_graphRange (d f v : ZFSet.{u}) :
    v ∈ graphRange d f ↔ ∃ x ∈ d, ZFSet.pair x v ∈ f := by
  rw [graphRange,ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨x,hx,hxv⟩
    exact ⟨second_mem_doubleUnion hxv,x,hx,hxv⟩

theorem graphRange_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hU : BoundedSetTheory.Union M) (hS : Separation M)
    {d f : ZFSet.{u}} (hd : d ∈ M) (hf : f ∈ M) : graphRange d f ∈ M := by
  simpa only [graphRange,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hS (.existsMem 1 (.pairMem 0 1 3)) (cons d (fun _ => f))
      (by intro i; cases i <;> assumption) (iterUnion_mem M hM hU hf 2)

theorem Graph.range_iff {d r b f : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (hf : Graph d r d b f) (v : ZFSet.{u}) :
    v ∈ graphRange d f ↔ ∃ x ∈ d, v = value d r wf x := by
  rw [mem_graphRange]
  constructor
  · rintro ⟨x,hx,hxv⟩
    obtain ⟨y,hy,heq⟩ := (hf.mem_iff wf _).mp hxv
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact ⟨x,hx,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,hx,(hf.mem_iff wf _).mpr ⟨x,hx,rfl⟩⟩

theorem Graph.range_transitive {d r b f : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (hf : Graph d r d b f) : Transitive (graphRange d f) := by
  intro v hv w hw
  obtain ⟨x,_,rfl⟩ := (hf.range_iff wf v).mp hv
  obtain ⟨y,hy,_,rfl⟩ := (mem_value d r wf x w).mp hw
  exact (hf.range_iff wf _).mpr ⟨y,hy,rfl⟩

theorem internal_mostowski (M d r : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (hr : r ∈ M) (wf : WellFounded (Rel d r)) (he : Extensional d r) :
    ∃ b ∈ M, ∃ f ∈ M,
      Presents d f (value d r wf) ∧ Transitive b ∧
      (∀ v, v ∈ b ↔ ∃ x ∈ d, v = value d r wf x) ∧
      (∀ x ∈ d, ∀ y ∈ d, value d r wf x = value d r wf y → x = y) ∧
      (∀ x ∈ d, ∀ y ∈ d, value d r wf x ∈ value d r wf y ↔ ZFSet.pair x y ∈ r) := by
  obtain ⟨f,hf,hfg⟩ := internal_graph M d r hM hP hU hPow hS hR hd hr wf
  exact ⟨graphRange d f,graphRange_mem M hM hU hS hd hf,f,hf,
    hfg.mem_iff wf,hfg.range_transitive wf,hfg.range_iff wf,
    value_injective wf he,fun _ hx _ _ => value_mem_iff wf he hx⟩

end TuringRigidity.RelationCollapse

end OAI
