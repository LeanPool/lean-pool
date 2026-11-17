/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/CheckedCode.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedRelations

/-!
# Checked Code
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open RecursiveNames BoundedSetTheory
universe u

noncomputable def checkedCode (t x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun y : Shrink x =>
    ZFSet.pair (checkedCode t ((equivShrink x).symm y).val) t)
termination_by x
decreasing_by exact ((equivShrink x).symm y).property

theorem mem_checkedCode (t x z : ZFSet.{u}) :
    z ∈ checkedCode t x ↔ ∃ y ∈ x, z = ZFSet.pair (checkedCode t y) t := by
  rw [checkedCode, ZFSet.mem_range]
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨_,((equivShrink x).symm y).property,hy.symm⟩
  · rintro ⟨y,hy,hz⟩
    refine ⟨equivShrink x ⟨y,hy⟩,?_⟩
    simpa using hz.symm

theorem encode_checkPSet {P : Type u} [Top P] (l : P → ZFSet.{u}) (x : PSet.{u}) :
    (Name.checkPSet x : Name P).encode l = checkedCode (l ⊤) (ZFSet.mk x) := by
  induction x with
  | mk ι child ih =>
    apply ZFSet.ext
    intro z
    change z ∈ ZFSet.range _ ↔ _
    rw [ZFSet.mem_range,mem_checkedCode]
    constructor
    · rintro ⟨i,hi⟩
      refine ⟨ZFSet.mk (child i),?_,by simpa only [ih] using hi.symm⟩
      change ∃ j, PSet.Equiv (child i) (child j)
      exact ⟨i,PSet.Equiv.refl _⟩
    · rintro ⟨y,hy,hz⟩
      induction y using Quotient.inductionOn with
      | h y =>
        change ∃ i, PSet.Equiv y (child i) at hy
        obtain ⟨i,hi⟩ := hy
        have he : ZFSet.mk y = ZFSet.mk (child i) := Quotient.sound hi
        change z = ZFSet.pair (checkedCode (l ⊤) (ZFSet.mk y)) (l ⊤) at hz
        rw [he] at hz
        exact ⟨i,by simpa only [ih] using hz.symm⟩

theorem encode_check {P : Type u} [Top P] (l : P → ZFSet.{u}) (x : ZFSet.{u}) :
    (Name.check x : Name P).encode l = checkedCode (l ⊤) x := by
  rw [Name.check,encode_checkPSet,ZFSet.mk_out]

def RecursionStep (f r t x v : ZFSet.{u}) : Prop :=
  (∀ z ∈ v, ∃ y ∈ x, ∃ w ∈ r, ZFSet.pair y w ∈ f ∧ z = ZFSet.pair w t) ∧
  (∀ y ∈ x, ∀ w ∈ r, ZFSet.pair y w ∈ f → ZFSet.pair w t ∈ v)

def CheckGraph (d r f t : ZFSet.{u}) : Prop :=
  Transitive d ∧
  (∀ z ∈ f, ∃ x ∈ d, ∃ y ∈ r, z = ZFSet.pair x y) ∧
  (∀ x ∈ d, ∃ y ∈ r, ZFSet.pair x y ∈ f ∧
    ∀ z ∈ r, ZFSet.pair x z ∈ f → z = y) ∧
  (∀ x ∈ d, ∀ y ∈ r, ZFSet.pair x y ∈ f → RecursionStep f r t x y)

theorem CheckGraph.correct {d r f t : ZFSet.{u}} (h : CheckGraph d r f t)
    (x : ZFSet.{u}) (hx : x ∈ d) (v : ZFSet.{u}) (hv : v ∈ r)
    (hfv : ZFSet.pair x v ∈ f) : v = checkedCode t x := by
  induction x using ZFSet.inductionOn generalizing v with
  | h x ih =>
    have hs := h.2.2.2 x hx v hv hfv
    apply ZFSet.ext
    intro z
    rw [mem_checkedCode]
    constructor
    · intro hz
      obtain ⟨y,hy,w,hw,hfw,rfl⟩ := hs.1 z hz
      exact ⟨y,hy,by rw [ih y hy (h.1 x hx y hy) w hw hfw]⟩
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨w,hw,hfw,_⟩ := h.2.2.1 y (h.1 x hx y hy)
      rw [←ih y hy (h.1 x hx y hy) w hw hfw]
      exact hs.2 y hy w hw hfw

theorem CheckGraph.unique {d r s f g t : ZFSet.{u}}
    (hf : CheckGraph d r f t) (hg : CheckGraph d s g t) : f = g := by
  apply ZFSet.ext
  intro z
  have forward {r s f g : ZFSet.{u}} (hf : CheckGraph d r f t)
      (hg : CheckGraph d s g t) (hz : z ∈ f) : z ∈ g := by
    obtain ⟨x,hx,y,hy,rfl⟩ := hf.2.1 z hz
    obtain ⟨v,hv,hgv,_⟩ := hg.2.2.1 x hx
    have he := (hf.correct x hx y hy hz).trans (hg.correct x hx v hv hgv).symm
    exact he ▸ hgv
  exact ⟨forward hf hg,forward hg hf⟩

namespace CheckFormula
open BoundedSetTheory.Formula

def step (f r t x v : ℕ) : Formula :=
  .conj (allMem v (.existsMem (x+1) (.existsMem (r+2)
    (.conj (pairMem 1 0 (f+3)) (orderedPair 2 0 (t+3))))))
    (allMem x (allMem (r+1) (imp (pairMem 1 0 (f+2))
      (.existsMem (v+2) (orderedPair 0 1 (t+3))))))

theorem eval_step (f r t x v : ℕ) (e : ℕ → ZFSet.{u}) :
    (step f r t x v).Eval e ↔ RecursionStep (e f) (e r) (e t) (e x) (e v) := by
  simp only [step, Formula.Eval, eval_allMem, eval_pairMem, eval_orderedPair,
    eval_imp, cons_zero, cons_succ, RecursionStep]
  simp only [exists_eq_right]

def graph (d r f t : ℕ) : Formula :=
  .conj (transitive d) (.conj (functionGraph f d r)
    (allMem d (allMem (r+1) (imp (pairMem 1 0 (f+2)) (step (f+2) (r+2) (t+2) 1 0)))))

theorem eval_graph (d r f t : ℕ) (e : ℕ → ZFSet.{u}) :
    (graph d r f t).Eval e ↔ CheckGraph (e d) (e r) (e f) (e t) := by
  simp only [graph, Formula.Eval, eval_transitive, eval_functionGraph,
    eval_allMem, eval_imp, eval_pairMem, eval_step, cons_zero, cons_succ, CheckGraph]
  exact and_congr_right (fun _ => and_assoc)
end CheckFormula

end TuringRigidity.TransitiveNameModel

end OAI
