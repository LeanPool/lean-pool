/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RelationCollapse.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RelationHull
public import LeanPool.TuringConeRigidity.Syntax.CheckGraphConstruction

/-!
# Relation Collapse
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory RelationHull
universe u

def Rel (d r : ZFSet.{u}) (y x : ZFSet.{u}) : Prop := y ∈ d ∧ ZFSet.pair y x ∈ r

noncomputable def value (d r : ZFSet.{u}) (wf : WellFounded (Rel d r)) : ZFSet.{u} → ZFSet.{u} :=
  wf.fix (fun x ih => ZFSet.range (fun y : Conditions (predecessors d r x) =>
    ih (label (predecessors d r x) y)
      ((mem_predecessors d r x _).mp (label_mem _ y))))

theorem mem_value (d r : ZFSet.{u}) (wf : WellFounded (Rel d r)) (x z : ZFSet.{u}) :
    z ∈ value d r wf x ↔ ∃ y ∈ d, ZFSet.pair y x ∈ r ∧ z = value d r wf y := by
  rw [value,WellFounded.fix_eq]
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨hyd,hyx⟩ := (mem_predecessors d r x _).mp (label_mem _ y)
    exact ⟨_,hyd,hyx,hy.symm⟩
  · rintro ⟨y,hyd,hyx,rfl⟩
    obtain ⟨s,rfl⟩ := label_surjective (predecessors d r x)
      ((mem_predecessors _ _ _ _).mpr ⟨hyd,hyx⟩)
    exact ⟨s,rfl⟩

def Step (d r f x v : ZFSet.{u}) : Prop :=
  (∀ z ∈ v, ∃ y ∈ d, ZFSet.pair y x ∈ r ∧ ZFSet.pair y z ∈ f) ∧
  (∀ y ∈ d, ZFSet.pair y x ∈ r → ∀ z, ZFSet.pair y z ∈ f → z ∈ v)

def Graph (d r a b f : ZFSet.{u}) : Prop :=
  a ⊆ d ∧ Closed d r a ∧
  (∀ z ∈ f, ∃ x ∈ a, ∃ y ∈ b, z = ZFSet.pair x y) ∧
  (∀ x ∈ a, ∃ y ∈ b, ZFSet.pair x y ∈ f ∧
    ∀ z ∈ b, ZFSet.pair x z ∈ f → z = y) ∧
  (∀ x ∈ a, ∀ v ∈ b, ZFSet.pair x v ∈ f →
    (∀ z ∈ v, ∃ y ∈ d, ZFSet.pair y x ∈ r ∧ ZFSet.pair y z ∈ f) ∧
    (∀ y ∈ d, ZFSet.pair y x ∈ r → ∀ z ∈ b, ZFSet.pair y z ∈ f → z ∈ v))

theorem Graph.correct {d r a b f : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (h : Graph d r a b f) (x : ZFSet.{u}) (hx : x ∈ a)
    (v : ZFSet.{u}) (hv : v ∈ b) (hfv : ZFSet.pair x v ∈ f) :
    v = value d r wf x := by
  induction x using wf.induction generalizing v with
  | h x ih =>
    have hs := h.2.2.2.2 x hx v hv hfv
    apply ZFSet.ext
    intro z
    rw [mem_value]
    constructor
    · intro hz
      obtain ⟨y,hyd,hyx,hyz⟩ := hs.1 z hz
      obtain ⟨w,hw,t,ht,heq⟩ := h.2.2.1 _ hyz
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
      exact ⟨y,hyd,hyx,ih y ⟨hyd,hyx⟩ (h.2.1 x hx y hyd hyx) z ht hyz⟩
    · rintro ⟨y,hyd,hyx,rfl⟩
      have hya := h.2.1 x hx y hyd hyx
      obtain ⟨w,hw,hyw,_⟩ := h.2.2.2.1 y hya
      rw [←ih y ⟨hyd,hyx⟩ hya w hw hyw]
      exact hs.2 y hyd hyx w hw hyw

theorem Graph.mem_iff {d r a b f : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (h : Graph d r a b f) (z : ZFSet.{u}) :
    z ∈ f ↔ ∃ x ∈ a, z = ZFSet.pair x (value d r wf x) := by
  constructor
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := h.2.2.1 z hz
    exact ⟨x,hx,congrArg (ZFSet.pair x) (h.correct wf x hx y hy hz)⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hxy,_⟩ := h.2.2.2.1 x hx
    rw [←h.correct wf x hx y hy hxy]
    exact hxy

theorem Graph.unique {d r a b b' f g : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (hf : Graph d r a b f) (hg : Graph d r a b' g) : f = g := by
  apply ZFSet.ext
  intro z
  exact (hf.mem_iff wf z).trans (hg.mem_iff wf z).symm

theorem graph_of_mem_iff (d r a f : ZFSet.{u}) (wf : WellFounded (Rel d r))
    (ha : a ⊆ d) (hc : Closed d r a)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ a, z = ZFSet.pair x (value d r wf x)) :
    Graph d r a (iterUnion 2 f) f := by
  have pair (x : ZFSet.{u}) (hx : x ∈ a) : ZFSet.pair x (value d r wf x) ∈ f :=
    (hf _).mpr ⟨x,hx,rfl⟩
  have valmem (x : ZFSet.{u}) (hx : x ∈ a) : value d r wf x ∈ iterUnion 2 f :=
    second_mem_doubleUnion (pair x hx)
  refine ⟨ha,hc,?_,?_,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (hf z).mp hz
    exact ⟨x,hx,_,valmem x hx,rfl⟩
  · intro x hx
    refine ⟨_,valmem x hx,pair x hx,?_⟩
    intro y _ hxy
    obtain ⟨w,_,heq⟩ := (hf _).mp hxy
    exact (ZFSet.pair_inj.mp heq).1 ▸ (ZFSet.pair_inj.mp heq).2
  · intro x hx v _ hxv
    obtain ⟨w,hw,heq⟩ := (hf _).mp hxv
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    constructor
    · intro z hz
      obtain ⟨y,hyd,hyx,rfl⟩ := (mem_value d r wf x z).mp hz
      exact ⟨y,hyd,hyx,pair y (hc x hx y hyd hyx)⟩
    · intro y hyd hyx z _ hyz
      obtain ⟨t,_,heq⟩ := (hf _).mp hyz
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
      exact (mem_value d r wf x _).mpr ⟨y,hyd,hyx,rfl⟩

namespace Code
open Formula

def step (d r b f x v : ℕ) : Formula :=
  .conj (allMem v (.existsMem (d+1)
    (.conj (pairMem 0 (x+2) (r+2)) (pairMem 0 1 (f+2)))))
    (allMem d (imp (pairMem 0 (x+1) (r+1))
      (allMem (b+1) (imp (pairMem 1 0 (f+2)) (.member 0 (v+2))))))

def graph (d r a b f : ℕ) : Formula :=
  .conj (subset a d) (.conj (RelationHull.Code.closed d r a)
    (.conj (functionGraph f a b)
      (allMem a (allMem (b+1) (imp (pairMem 1 0 (f+2))
        (step (d+2) (r+2) (b+2) (f+2) 1 0))))))

theorem eval_graph (d r a b f : ℕ) (e : ℕ → ZFSet.{u}) :
    (graph d r a b f).Eval e ↔ Graph (e d) (e r) (e a) (e b) (e f) := by
  simp only [graph,step,Graph,Formula.Eval,eval_subset,RelationHull.Code.eval_closed,
    eval_functionGraph,eval_allMem,eval_imp,eval_pairMem,cons_zero,cons_succ]
  exact and_congr_right (fun _ => and_congr_right (fun _ => and_assoc))
end Code

end TuringRigidity.RelationCollapse

end OAI
