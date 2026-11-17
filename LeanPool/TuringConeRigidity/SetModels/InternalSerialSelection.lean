/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalSerialSelection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTheory

/-!
# Internal Serial Selection
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationHull
universe u
namespace Formula

/-- Bounded formula defining the predecessor set of `x` inside `d` for relation `r`. -/
def predecessorSet (d r x a : ℕ) : Formula := .conj (.subset a d)
  (allMem d (iff (.member 0 (a+1)) (.pairMem 0 (x+1) (r+1))))

theorem eval_predecessorSet (d r x a : ℕ) (e : ℕ → ZFSet.{u}) :
    (predecessorSet d r x a).Eval e ↔ e a = predecessors (e d) (e r) (e x) := by
  simp only
    [predecessorSet,Formula.Eval,eval_subset,eval_allMem,eval_iff,eval_pairMem,cons_zero,cons_succ]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro y
    rw [mem_predecessors]
    exact ⟨fun hy => ⟨hsub hy,(h y (hsub hy)).mp hy⟩,fun hy => (h y hy.1).mpr hy.2⟩
  · intro he
    rw [he]
    exact ⟨fun _ h => (mem_predecessors _ _ _ _).mp h |>.1,
      fun y hy => (mem_predecessors _ _ _ _).trans (and_iff_right hy)⟩

/-- Bounded formula selecting a predecessor through the supplied choice relation on
predecessor sets. -/
def serialSelector (d r q s z : ℕ) : Formula := .existsMem d (.existsMem (d+1)
  (.conj (.orderedPair (z+2) 1 0) (.existsMem (q+2)
    (.conj (predecessorSet (d+3) (r+3) 2 0) (.pairMem 0 1 (s+3))))))
end Formula

theorem internal_serial_function (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M)
    (hser : ∀ x ∈ d, ∃ y ∈ d, ZFSet.pair y x ∈ r) :
    ∃ F ∈ M, TransitiveNameModel.FunctionGraph d d F ∧
      ∀ x y, ZFSet.pair x y ∈ F → ZFSet.pair y x ∈ r := by
  have hS := hT.separation.finitePrefix.bounded
  obtain ⟨q,hq,s,hsM,hs,hqdef⟩ := internal_selector M hM hT.powerSet hS hT.choice hd
  have hp (x : ZFSet.{u}) (hx : x ∈ d) : predecessors d r x ∈ q := by
    apply (hqdef _).mpr
    refine ⟨predecessors_mem M hM hS hd hr (hM _ hd _ hx),
      fun _ h => (mem_predecessors _ _ _ _).mp h |>.1,?_⟩
    obtain ⟨y,hy,hyx⟩ := hser x hx
    exact ⟨y,(mem_predecessors _ _ _ _).mpr ⟨hy,hyx⟩⟩
  let e := cons d (cons r (cons q (fun _ => s)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hd
    rcases i with _ | i
    · exact hr
    rcases i with _ | i
    · exact hq
    exact hsM
  let F := ZFSet.sep (fun z => (Formula.serialSelector 1 2 3 4 0).Eval (cons z e)) (ZFSet.prod d d)
  have hFM : F ∈ M := sep_mem M hM hS _ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hd hd)
  have hmem (z : ZFSet.{u}) : z ∈ F ↔
      ∃ x ∈ d, ∃ y ∈ d, z = ZFSet.pair x y ∧ ZFSet.pair (predecessors d r x) y ∈ s := by
    simp only [F,ZFSet.mem_sep,Formula.serialSelector,Formula.Eval,Formula.eval_orderedPair,
      Formula.eval_predecessorSet,Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,x,hx,y,hy,hz,a,_,rfl,hay⟩; exact ⟨x,hx,y,hy,hz,hay⟩
    · rintro ⟨x,hx,y,hy,rfl,hxy⟩
      exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,x,hx,y,hy,rfl,predecessors d r x,hp x hx,rfl,hxy⟩
  refine ⟨F,hFM,⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨x,hx,y,hy,hz,_⟩ := (hmem z).mp hz
    exact ⟨x,hx,y,hy,hz⟩
  · intro x hx
    obtain ⟨y,hy,hxy,_⟩ := hs.2 _ (hp x hx)
    have hyd := ((mem_predecessors _ _ _ _).mp hy).1
    refine ⟨y,hyd,(hmem _).mpr ⟨x,hx,y,hyd,rfl,hxy⟩,?_⟩
    intro z _ hxz
    obtain ⟨x',_,z',_,heq,hxz'⟩ := (hmem _).mp hxz
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact hs.functional hxz' hxy
  · intro x y hxy
    obtain ⟨x',_,y',_,heq,hsy⟩ := (hmem _).mp hxy
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact ((mem_predecessors _ _ _ _).mp (InternalWellOrder.choice_value_mem hs hsy)).2

end TuringRigidity.BoundedSetTheory

end OAI
