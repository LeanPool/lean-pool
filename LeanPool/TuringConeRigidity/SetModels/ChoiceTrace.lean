/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ChoiceTrace.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalHartogs
public import LeanPool.TuringConeRigidity.SetModels.InternalChoice
public import LeanPool.TuringConeRigidity.Syntax.TermFunctionality

/-!
# Choice Trace
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace InternalWellOrder

def Remaining (a f i r : ZFSet.{u}) : Prop := r ⊆ a ∧
  ∀ x ∈ a, x ∈ r ↔ ¬ ∃ j ∈ i, ZFSet.pair j x ∈ f

structure Trace (α a q s f : ZFSet.{u}) : Prop where
  shape : ∀ z ∈ f, ∃ i ∈ α, ∃ x ∈ a, z = ZFSet.pair i x
  initial : ∀ i ∈ α, ∀ x ∈ a, ZFSet.pair i x ∈ f →
    ∀ j ∈ i, ∃ y ∈ a, ZFSet.pair j y ∈ f
  choice : ∀ i ∈ α, ∀ x ∈ a, ZFSet.pair i x ∈ f →
    ∃ r ∈ q, Remaining a f i r ∧ ZFSet.pair r x ∈ s

theorem Trace.pair_mem {α a q s f i x : ZFSet.{u}} (hf : Trace α a q s f)
    (hix : ZFSet.pair i x ∈ f) : i ∈ α ∧ x ∈ a := by
  obtain ⟨j,hj,y,hy,he⟩ := hf.shape _ hix
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact ⟨hj,hy⟩

theorem choice_value_mem {q s r x : ZFSet.{u}} (hs : ChoiceGraph q s)
    (hrx : ZFSet.pair r x ∈ s) : x ∈ r := by
  obtain ⟨r',_,x',hx,he⟩ := hs.1 _ hrx
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact hx

theorem Remaining.eq {a f g i r t : ZFSet.{u}} (hr : Remaining a f i r)
    (ht : Remaining a g i t)
    (hfg : ∀ j ∈ i, ∀ x ∈ a, ZFSet.pair j x ∈ f ↔ ZFSet.pair j x ∈ g) : r = t := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    have hxa := hr.1 hx
    apply (ht.2 x hxa).mpr
    rintro ⟨j,hji,hjx⟩
    exact (hr.2 x hxa).mp hx ⟨j,hji,(hfg j hji x hxa).mpr hjx⟩
  · intro hx
    have hxa := ht.1 hx
    apply (hr.2 x hxa).mpr
    rintro ⟨j,hji,hjx⟩
    exact (ht.2 x hxa).mp hx ⟨j,hji,(hfg j hji x hxa).mp hjx⟩

theorem Trace.compatible {α a q s f g : ZFSet.{u}} (_hα : Transitive α)
    (hs : ChoiceGraph q s) (hf : Trace α a q s f) (hg : Trace α a q s g)
    (i x y : ZFSet.{u}) (hix : ZFSet.pair i x ∈ f) (hiy : ZFSet.pair i y ∈ g) : x = y := by
  induction i using ZFSet.inductionOn generalizing x y with
  | h i ih =>
    have hi := (hf.pair_mem hix).1
    have hx := (hf.pair_mem hix).2
    have hy := (hg.pair_mem hiy).2
    obtain ⟨r,_,hr,hrx⟩ := hf.choice i hi x hx hix
    obtain ⟨t,_,ht,hty⟩ := hg.choice i hi y hy hiy
    have heq : r = t := hr.eq ht (by
      intro j hji z _
      constructor
      · intro hjz
        obtain ⟨w,_,hjw⟩ := hg.initial i hi y hy hiy j hji
        have hzw := ih j hji z w hjz hjw
        exact hzw.symm ▸ hjw
      · intro hjz
        obtain ⟨w,_,hjw⟩ := hf.initial i hi x hx hix j hji
        have hwz := ih j hji w z hjw hjz
        exact hwz ▸ hjw)
    rw [heq] at hrx
    exact hs.functional hrx hty

theorem Trace.functional {α a q s f : ZFSet.{u}} (hα : Transitive α)
    (hs : ChoiceGraph q s) (hf : Trace α a q s f) : FiniteTerm.Functional f :=
  fun i x y hx hy => hf.compatible hα hs hf i x y hx hy

theorem Trace.injective {α a q s f : ZFSet.{u}} (hα : α.IsOrdinal)
    (hs : ChoiceGraph q s) (hf : Trace α a q s f)
    (i j x : ZFSet.{u}) (hix : ZFSet.pair i x ∈ f) (hjx : ZFSet.pair j x ∈ f) : i = j := by
  have hi := (hf.pair_mem hix).1
  have hj := (hf.pair_mem hjx).1
  have hx := (hf.pair_mem hix).2
  rcases (hα.mem hi).mem_trichotomous (hα.mem hj) with hij|he|hji
  · obtain ⟨r,_,hr,hrx⟩ := hf.choice j hj x hx hjx
    exact False.elim ((hr.2 x hx).mp (choice_value_mem hs hrx) ⟨i,hij,hix⟩)
  · exact he
  · obtain ⟨r,_,hr,hrx⟩ := hf.choice i hi x hx hix
    exact False.elim ((hr.2 x hx).mp (choice_value_mem hs hrx) ⟨j,hji,hjx⟩)

theorem Trace.sUnion {α a q s C : ZFSet.{u}} (hα : Transitive α)
    (hs : ChoiceGraph q s) (hC : ∀ f ∈ C, Trace α a q s f) :
    Trace α a q s (ZFSet.sUnion C) := by
  have from_pair (i x : ZFSet.{u}) (hix : ZFSet.pair i x ∈ ZFSet.sUnion C) :
      ∃ f ∈ C, ZFSet.pair i x ∈ f := ZFSet.mem_sUnion.mp hix
  refine ⟨?_,?_,?_⟩
  · intro z hz
    obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
    exact (hC f hf).shape z hzf
  · intro i hi x hx hix j hji
    obtain ⟨f,hf,hif⟩ := from_pair i x hix
    obtain ⟨y,hy,hjy⟩ := (hC f hf).initial i hi x hx hif j hji
    exact ⟨y,hy,ZFSet.mem_sUnion.mpr ⟨f,hf,hjy⟩⟩
  · intro i hi x hx hix
    obtain ⟨f,hf,hif⟩ := from_pair i x hix
    obtain ⟨r,hr,hrdef,hrx⟩ := (hC f hf).choice i hi x hx hif
    refine ⟨r,hr,⟨hrdef.1,?_⟩,hrx⟩
    intro y hy
    rw [hrdef.2 y hy]
    apply not_congr
    constructor
    · rintro ⟨j,hji,hjy⟩
      exact ⟨j,hji,ZFSet.mem_sUnion.mpr ⟨f,hf,hjy⟩⟩
    · rintro ⟨j,hji,hjy⟩
      obtain ⟨g,hg,hjg⟩ := from_pair j y hjy
      obtain ⟨z,_,hjz⟩ := (hC f hf).initial i hi x hx hif j hji
      have hzy := (hC f hf).compatible hα hs (hC g hg) j z y hjz hjg
      exact ⟨j,hji,hzy ▸ hjz⟩

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
