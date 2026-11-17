/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/AtomicFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalFixedPoint

/-!
# Atomic Formula
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open TransitiveNameModel BoundedSetTheory
universe u

def Triple (k f a b q : ZFSet.{u}) : Prop :=
  ∃ v ∈ k, v = ZFSet.pair a b ∧ ZFSet.pair v q ∈ f

def Match (flip : Bool) (d c k o f a y q : ZFSet.{u}) : Prop :=
  ∃ r ∈ c, ZFSet.pair r q ∈ o ∧ ∃ b ∈ d, ∃ t ∈ c,
    ZFSet.pair b t ∈ y ∧ ZFSet.pair r t ∈ o ∧
      Triple k f (if flip then b else a) (if flip then a else b) r

def Side (flip : Bool) (d c k o f x y p : ZFSet.{u}) : Prop :=
  ∀ a ∈ d, ∀ s ∈ c, ZFSet.pair a s ∈ x →
    ∀ q ∈ c, ZFSet.pair q p ∈ o → ZFSet.pair q s ∈ o → Match flip d c k o f a y q

def Step (d c k o f x y p : ZFSet.{u}) : Prop :=
  Side false d c k o f x y p ∧ Side true d c k o f y x p

def Vertex (d c k o f z : ZFSet.{u}) : Prop :=
  ∃ x ∈ d, ∃ y ∈ d, ∃ q ∈ c, ∃ v ∈ k,
    v = ZFSet.pair x y ∧ z = ZFSet.pair v q ∧ Step d c k o f x y q

namespace AtomicFormula
open Formula

def triple (k f a b q : ℕ) : Formula :=
  .existsMem k (.conj (orderedPair 0 (a+1) (b+1)) (pairMem 0 (q+1) (f+1)))

theorem eval_triple (k f a b q : ℕ) (e : ℕ → ZFSet.{u}) :
    (triple k f a b q).Eval e ↔ Triple (e k) (e f) (e a) (e b) (e q) := by
  simp only [triple,Formula.Eval,eval_orderedPair,eval_pairMem,cons_zero,cons_succ,Triple]

def matchF (flip : Bool) (d c k o f a y q : ℕ) : Formula :=
  .existsMem c (.conj (pairMem 0 (q+1) (o+1))
    (.existsMem (d+1) (.existsMem (c+2)
      (.conj (pairMem 1 0 (y+3)) (.conj (pairMem 2 0 (o+3))
        (triple (k+3) (f+3) (if flip then 1 else a+3) (if flip then a+3 else 1) 2))))))

theorem eval_matchF (flip : Bool) (d c k o f a y q : ℕ) (e : ℕ → ZFSet.{u}) :
    (matchF flip d c k o f a y q).Eval e ↔
      Match flip (e d) (e c) (e k) (e o) (e f) (e a) (e y) (e q) := by
  cases flip <;> simp only [matchF,Formula.Eval,eval_pairMem,eval_triple,
    cons_zero,cons_succ,Match,Bool.false_eq_true,ite_false,ite_true]

def side (flip : Bool) (d c k o f x y p : ℕ) : Formula :=
  allMem d (allMem (c+1) (imp (pairMem 1 0 (x+2))
    (allMem (c+2) (imp (.conj (pairMem 0 (p+3) (o+3)) (pairMem 0 1 (o+3)))
      (matchF flip (d+3) (c+3) (k+3) (o+3) (f+3) 2 (y+3) 0)))))

theorem eval_side (flip : Bool) (d c k o f x y p : ℕ) (e : ℕ → ZFSet.{u}) :
    (side flip d c k o f x y p).Eval e ↔
      Side flip (e d) (e c) (e k) (e o) (e f) (e x) (e y) (e p) := by
  simp only [side,eval_allMem,eval_imp,Formula.Eval,eval_pairMem,eval_matchF,
    cons_zero,cons_succ,Side,and_imp]

def step (d c k o f x y p : ℕ) : Formula :=
  .conj (side false d c k o f x y p) (side true d c k o f y x p)

theorem eval_step (d c k o f x y p : ℕ) (e : ℕ → ZFSet.{u}) :
    (step d c k o f x y p).Eval e ↔
      Step (e d) (e c) (e k) (e o) (e f) (e x) (e y) (e p) := by
  simp only [step,Formula.Eval,eval_side,Step]

def vertex (d c k o f z : ℕ) : Formula :=
  .existsMem d (.existsMem (d+1) (.existsMem (c+2) (.existsMem (k+3)
    (.conj (orderedPair 0 3 2) (.conj (orderedPair (z+4) 0 1)
      (step (d+4) (c+4) (k+4) (o+4) (f+4) 3 2 1))))))

theorem eval_vertex (d c k o f z : ℕ) (e : ℕ → ZFSet.{u}) :
    (vertex d c k o f z).Eval e ↔ Vertex (e d) (e c) (e k) (e o) (e f) (e z) := by
  simp only [vertex,Formula.Eval,eval_orderedPair,eval_step,cons_zero,cons_succ,Vertex]
end AtomicFormula

theorem match_mono (flip : Bool) (d c k o f g a y q : ZFSet.{u})
    (hfg : f ⊆ g) (h : Match flip d c k o f a y q) : Match flip d c k o g a y q := by
  obtain ⟨r,hr,hrq,b,hb,t,ht,hbt,hrt,v,hv,hve,hvf⟩ := h
  exact ⟨r,hr,hrq,b,hb,t,ht,hbt,hrt,v,hv,hve,hfg hvf⟩

theorem step_mono (d c k o f g x y p : ZFSet.{u}) (hfg : f ⊆ g)
    (h : Step d c k o f x y p) : Step d c k o g x y p := by
  exact ⟨fun a ha s hs hax q hq hqp hqs =>
      match_mono _ _ _ _ _ _ _ _ _ _ hfg (h.1 a ha s hs hax q hq hqp hqs),
    fun a ha s hs hay q hq hqp hqs =>
      match_mono _ _ _ _ _ _ _ _ _ _ hfg (h.2 a ha s hs hay q hq hqp hqs)⟩

theorem vertex_mono (d c k o f g z : ZFSet.{u}) (hfg : f ⊆ g)
    (h : Vertex d c k o f z) : Vertex d c k o g z := by
  obtain ⟨x,hx,y,hy,q,hq,v,hv,hve,hze,hs⟩ := h
  exact ⟨x,hx,y,hy,q,hq,v,hv,hve,hze,step_mono _ _ _ _ _ _ _ _ _ hfg hs⟩

end TuringRigidity.AtomicForcing

end OAI
