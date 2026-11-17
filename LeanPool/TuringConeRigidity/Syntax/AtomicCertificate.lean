/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/AtomicCertificate.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalAtomicTruth

/-!
# Atomic Certificate
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

namespace AtomicFormula
open Formula

def product (d k : ℕ) : Formula :=
  .conj (allMem k (.existsMem (d+1) (.existsMem (d+2) (orderedPair 2 1 0))))
    (allMem d (allMem (d+1) (.existsMem (k+2) (orderedPair 0 2 1))))

theorem eval_product (d k : ℕ) (e : ℕ → ZFSet.{u}) :
    (product d k).Eval e ↔ e k = ZFSet.prod (e d) (e d) := by
  simp only [product,Formula.Eval,eval_allMem,eval_orderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨h₁,h₂⟩
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨x,hx,y,hy,hz⟩ := h₁ z hz
      exact ZFSet.mem_prod.mpr ⟨x,hx,y,hy,hz⟩
    · intro hz
      obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp hz
      obtain ⟨v,hv,rfl⟩ := h₂ x hx y hy
      exact hv
  · intro hk
    constructor
    · intro z hz
      rw [hk] at hz
      exact ZFSet.mem_prod.mp hz
    · intro x hx y hy
      exact ⟨_,hk ▸ ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,rfl⟩

def graph (d c k o f : ℕ) : Formula :=
  .conj (allMem f (.existsMem (k+1) (.existsMem (c+2) (orderedPair 2 1 0))))
    (allMem d (allMem (d+1) (allMem (c+2)
      (iff (triple (k+3) (f+3) 2 1 0) (step (d+3) (c+3) (k+3) (o+3) (f+3) 2 1 0)))))

theorem eval_graph (d c k o f : ℕ) (e : ℕ → ZFSet.{u})
    (hk : e k = ZFSet.prod (e d) (e d)) :
    (graph d c k o f).Eval e ↔ Graph (e d) (e c) (e o) (e f) := by
  simp only [graph,Formula.Eval,eval_allMem,eval_orderedPair,eval_iff,eval_triple,eval_step,
    cons_zero,cons_succ,hk,Graph]
  constructor
  · rintro ⟨h₁,h₂⟩
    refine ⟨fun z hz => ZFSet.mem_prod.mpr (h₁ z hz),?_⟩
    intro x hx y hy q hq
    exact (triple_pair hx hy).symm.trans (h₂ x hx y hy q hq)
  · rintro ⟨h₁,h₂⟩
    refine ⟨fun z hz => ZFSet.mem_prod.mp (h₁ hz),?_⟩
    intro x hx y hy q hq
    exact (triple_pair hx hy).trans (h₂ x hx y hy q hq)

def membership (d c k o f x y p : ℕ) : Formula :=
  allMem c (imp (pairMem 0 (p+1) (o+1))
    (matchF false (d+1) (c+1) (k+1) (o+1) (f+1) (x+1) (y+1) 0))

def query (isMem : Bool) (d c k o f x y p : ℕ) : Formula :=
  if isMem then membership d c k o f x y p else triple k f x y p

def matrix (isMem : Bool) : Formula :=
  .conj (transitive 2) (.conj (.member 4 2) (.conj (.member 5 2)
    (.conj (product 2 1) (.conj (graph 2 6 1 7 0) (query isMem 2 6 1 7 0 4 5 3)))))

def certificate (isMem : Bool) : SigmaFormula :=
  .existsSet (.existsSet (.existsSet (.bounded (matrix isMem))))
end AtomicFormula

variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem eval_membership {d o f : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (hf : Graph d c o f) (a b : Name (Conditions c))
    (ha : a.encode (label c) ∈ d) (hb : b.encode (label c) ∈ d) (p : Conditions c)
    (e : ℕ → ZFSet.{u}) (di ci ki oi fi xi yi pi : ℕ)
    (he : e di = d ∧ e ci = c ∧ e ki = ZFSet.prod d d ∧ e oi = o ∧ e fi = f ∧
      e xi = a.encode (label c) ∧ e yi = b.encode (label c) ∧ e pi = label c p) :
    (AtomicFormula.membership di ci ki oi fi xi yi pi).Eval e ↔ MemForces a b p := by
  rcases he with ⟨hd',hc',hk',ho',hf',hx',hy',hp'⟩
  simp only [AtomicFormula.membership,Formula.eval_allMem,Formula.eval_imp,
    Formula.eval_pairMem,AtomicFormula.eval_matchF,cons_zero,cons_succ,
    hd',hc',hk',ho',hf',hx',hy',hp']
  have step (q : Conditions c) :
      Match false d c (ZFSet.prod d d) o f (a.encode (label c)) (b.encode (label c)) (label c q) ↔
        ∃ r, r ≤ q ∧ Witness a b r := by
    rw [match_encode false hd ho b hb q]
    simp only [Bool.false_eq_true,ite_false]
    cases b with
    | mk κ b t =>
      have hchild (j) : (b j).encode (label c) ∈ d := names_childClosed d c hd (.mk κ b t) hb (b
        j) ⟨j,rfl⟩
      have hrel (j) (r : Conditions c) := (triple_pair ha (hchild j)).trans
        (hf.correct hd ho a (b j) ha (hchild j) r)
      simp only [Name.arity,Name.child,Name.tag,hrel,Witness]
  cases b with
  | mk κ b t =>
    constructor
    · intro h q hq
      exact (step q).mp (h _ (label_mem c q) ((ho q p).mpr hq))
    · intro h q hq hqp
      obtain ⟨r,rfl⟩ := label_surjective c hq
      exact (step r).mpr (h r ((ho r p).mp hqp))

end TuringRigidity.AtomicForcing

end OAI
