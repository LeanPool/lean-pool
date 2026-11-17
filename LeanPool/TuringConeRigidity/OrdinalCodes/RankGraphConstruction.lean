/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/RankGraphConstruction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.RankRecursion
public import LeanPool.TuringConeRigidity.Syntax.CheckGraphConstruction

/-!
# Rank Graph Construction
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.InternalRank
open TransitiveNameModel BoundedSetTheory
universe u

noncomputable def rankImage (x f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ y ∈ x, ∃ w ∈ iterUnion 2 f,
    ZFSet.pair y w ∈ f ∧ (z = w ∨ z ∈ w))
    (iterUnion 2 f ∪ ZFSet.sUnion (iterUnion 2 f))

theorem mem_rankImage (x f z : ZFSet.{u}) :
    z ∈ rankImage x f ↔ ∃ y ∈ x, ∃ w, ZFSet.pair y w ∈ f ∧ (z = w ∨ z ∈ w) := by
  rw [rankImage,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,y,hy,w,_,hfw,hz⟩; exact ⟨y,hy,w,hfw,hz⟩
  · rintro ⟨y,hy,w,hfw,hz⟩
    have hw := second_mem_doubleUnion hfw
    refine ⟨?_,y,hy,w,hw,hfw,hz⟩
    apply ZFSet.mem_union.mpr
    exact hz.elim (fun h => Or.inl (h ▸ hw))
      (fun h => Or.inr (ZFSet.mem_sUnion.mpr ⟨w,hw,h⟩))

def imageFormula : Formula :=
  .existsMem 1 (.existsMem 4 (.conj (.pairMem 1 0 4)
    (.disj (.equal 2 0) (.member 2 0))))

theorem eval_imageFormula (z x f r : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    imageFormula.Eval (cons z (cons x (cons f (cons r e)))) ↔
      ∃ y ∈ x, ∃ w ∈ r, ZFSet.pair y w ∈ f ∧ (z = w ∨ z ∈ w) := by
  simp only [imageFormula,Formula.Eval,Formula.eval_pairMem,Formula.eval_disj,cons_zero,cons_succ]

theorem rankImage_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hS : Separation M)
    {x f : ZFSet.{u}} (hx : x ∈ M) (hf : f ∈ M) : rankImage x f ∈ M := by
  have hr := iterUnion_mem M hM hU hf 2
  let e := cons x (cons f (cons (iterUnion 2 f) (fun _ => x)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hx
    rcases i with _ | i
    · exact hf
    rcases i with _ | i
    · exact hr
    exact hx
  have hs := sep_mem M hM hS imageFormula e he
    (binary_union_mem M hM hP hU hr (union_mem M hM hU hr))
  have heq : ZFSet.sep (fun z => imageFormula.Eval (cons z e))
      (iterUnion 2 f ∪ ZFSet.sUnion (iterUnion 2 f)) = rankImage x f := by
    apply ZFSet.ext
    intro z
    simp only [rankImage,ZFSet.mem_sep]
    exact and_congr_right (fun _ => eval_imageFormula z x f _ _)
  exact heq ▸ hs

theorem Graph.mem_iff {d r f : ZFSet.{u}} (h : Graph d r f) (z : ZFSet.{u}) :
    z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (rankSet x) := by
  constructor
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := h.2.1 z hz
    exact ⟨x,hx,by rw [h.correct x hx y hy hz]⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hfy,_⟩ := h.2.2.1 x hx
    rw [←h.correct x hx y hy hfy]
    exact hfy

theorem graph_of_mem_iff (d f : ZFSet.{u}) (hd : Transitive d)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (rankSet x)) :
    Graph d (iterUnion 2 f) f := by
  have hpair (x v : ZFSet.{u}) : ZFSet.pair x v ∈ f ↔ x ∈ d ∧ v = rankSet x := by
    rw [hf]
    constructor
    · rintro ⟨y,hy,he⟩
      obtain ⟨rfl,hv⟩ := ZFSet.pair_inj.mp he
      exact ⟨hy,hv⟩
    · rintro ⟨hx,rfl⟩; exact ⟨x,hx,rfl⟩
  refine ⟨hd,?_,?_,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (hf z).mp hz
    exact ⟨x,hx,rankSet x,second_mem_doubleUnion hz,rfl⟩
  · intro x hx
    have hp := (hpair x _).mpr ⟨hx,rfl⟩
    exact ⟨_,second_mem_doubleUnion hp,hp,fun v _ hv => (hpair x v).mp hv |>.2⟩
  · intro x hx v _ hv
    have he := (hpair x v).mp hv |>.2
    subst v
    constructor
    · intro z hz
      obtain ⟨y,hy,hz⟩ := (mem_rankSet x z).mp hz
      have hp := (hpair y _).mpr ⟨hd x hx y hy,rfl⟩
      exact ⟨y,hy,_,second_mem_doubleUnion hp,hp,hz⟩
    · intro y hy w _ hw
      rw [(hpair y w).mp hw |>.2]
      exact ⟨(mem_rankSet x _).mpr ⟨y,hy,Or.inl rfl⟩,
        fun z hz => (mem_rankSet x z).mpr ⟨y,hy,Or.inr hz⟩⟩

end TuringRigidity.InternalRank

end OAI
