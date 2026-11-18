/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/CheckGraphConstruction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.CheckedCode
public import LeanPool.TuringConeRigidity.SetModels.NameUnionCode

/-!
# Check Graph Construction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open RecursiveNames BoundedSetTheory
universe u

theorem second_mem_doubleUnion {a b f : ZFSet.{u}} (h : ZFSet.pair a b ∈ f) :
    b ∈ iterUnion 2 f := by
  apply ZFSet.mem_sUnion.mpr
  refine ⟨({a,b} : ZFSet.{u}),?_,ZFSet.mem_pair.mpr (Or.inr rfl)⟩
  exact ZFSet.mem_sUnion.mpr ⟨_,h,ZFSet.mem_pair.mpr (Or.inr rfl)⟩

/-- Bounded formula describing the tagged image of a graph value. -/
def taggedImageFormula : Formula :=
  .existsMem 1 (.existsMem 4 (.conj (.pairMem 1 0 4) (.orderedPair 2 0 6)))

theorem eval_taggedImageFormula (z x f r t : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    taggedImageFormula.Eval (cons z (cons x (cons f (cons r (cons t e))))) ↔
      ∃ y ∈ x, ∃ w ∈ r, ZFSet.pair y w ∈ f ∧ z = ZFSet.pair w t := by
  simp only [taggedImageFormula,Formula.Eval,Formula.eval_pairMem,
    Formula.eval_orderedPair,cons_zero,cons_succ]

/-- The image values of `x` under `f`, each paired with the common condition tag `t`. -/
noncomputable def taggedImage (x f t : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ y ∈ x, ∃ w ∈ iterUnion 2 f,
    ZFSet.pair y w ∈ f ∧ z = ZFSet.pair w t)
    (ZFSet.prod (iterUnion 2 f) ({t} : ZFSet.{u}))

theorem mem_taggedImage (x f t z : ZFSet.{u}) :
    z ∈ taggedImage x f t ↔ ∃ y ∈ x, ∃ w, ZFSet.pair y w ∈ f ∧ z = ZFSet.pair w t := by
  rw [taggedImage,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,y,hy,w,_,hfw,hz⟩
    exact ⟨y,hy,w,hfw,hz⟩
  · rintro ⟨y,hy,w,hfw,rfl⟩
    have hw := second_mem_doubleUnion hfw
    exact ⟨ZFSet.mem_prod.mpr ⟨w,hw,t,ZFSet.mem_singleton.mpr rfl,rfl⟩,
      y,hy,w,hw,hfw,rfl⟩

theorem taggedImage_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {x f t : ZFSet.{u}} (hx : x ∈ M) (hf : f ∈ M) (ht : t ∈ M) :
    taggedImage x f t ∈ M := by
  have hr := iterUnion_mem M hM hU hf 2
  let e := cons x (cons f (cons (iterUnion 2 f) (cons t (fun _ => x))))
  have he : ∀ i, e i ∈ M := by
    intro i; cases i with
    | zero => exact hx
    | succ i => cases i with
      | zero => exact hf
      | succ i => cases i with
        | zero => exact hr
        | succ i => cases i <;> assumption
  have hs := sep_mem M hM hS taggedImageFormula e he
    (product_mem M hM hP hU hPow hS hr (singleton_mem M hM hP ht))
  have heq : ZFSet.sep (fun z => taggedImageFormula.Eval (cons z e))
      (ZFSet.prod (iterUnion 2 f) ({t} : ZFSet.{u})) = taggedImage x f t := by
    apply ZFSet.ext
    intro z
    simp only [taggedImage,ZFSet.mem_sep]
    exact and_congr_right (fun _ => eval_taggedImageFormula z x f _ t _)
  exact heq ▸ hs

theorem CheckGraph.mem_iff {d r f t : ZFSet.{u}} (h : CheckGraph d r f t)
    (z : ZFSet.{u}) :
    z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (checkedCode t x) := by
  constructor
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := h.2.1 z hz
    exact ⟨x,hx,by rw [h.correct x hx y hy hz]⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hfy,_⟩ := h.2.2.1 x hx
    rw [←h.correct x hx y hy hfy]
    exact hfy

theorem checkGraph_of_mem_iff (d f t : ZFSet.{u}) (hd : Transitive d)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (checkedCode t x)) :
    CheckGraph d (iterUnion 2 f) f t := by
  have hpair (x v : ZFSet.{u}) : ZFSet.pair x v ∈ f ↔ x ∈ d ∧ v = checkedCode t x := by
    rw [hf]
    constructor
    · rintro ⟨y,hy,he⟩
      obtain ⟨rfl,hv⟩ := ZFSet.pair_inj.mp he
      exact ⟨hy,hv⟩
    · rintro ⟨hx,rfl⟩
      exact ⟨x,hx,rfl⟩
  refine ⟨hd,?_,?_,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (hf z).mp hz
    exact ⟨x,hx,checkedCode t x,second_mem_doubleUnion hz,rfl⟩
  · intro x hx
    have hp := (hpair x _).mpr ⟨hx,rfl⟩
    exact ⟨_,second_mem_doubleUnion hp,hp,fun v _ hv => (hpair x v).mp hv |>.2⟩
  · intro x hx v _ hv
    have he := (hpair x v).mp hv |>.2
    subst v
    constructor
    · intro z hz
      obtain ⟨y,hy,rfl⟩ := (mem_checkedCode t x z).mp hz
      have hp := (hpair y _).mpr ⟨hd x hx y hy,rfl⟩
      exact ⟨y,hy,_,second_mem_doubleUnion hp,hp,rfl⟩
    · intro y hy w _ hw
      rw [(hpair y w).mp hw |>.2]
      exact (mem_checkedCode t x _).mpr ⟨y,hy,rfl⟩

end TuringRigidity.TransitiveNameModel

end OAI
