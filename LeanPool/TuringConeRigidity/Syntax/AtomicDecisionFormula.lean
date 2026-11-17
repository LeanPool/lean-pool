/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/AtomicDecisionFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.AtomicGraphCorrect
public import LeanPool.TuringConeRigidity.Syntax.AtomicRequirements

/-!
# Atomic Decision Formula
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

/-- A child of `y` has a compatible tag and its pair with `x` occurs in the coded equality
graph. -/
def CodeWitness (d c k o f x y p : ZFSet.{u}) : Prop :=
  ∃ b ∈ d, ∃ t ∈ c, ZFSet.pair b t ∈ y ∧ ZFSet.pair p t ∈ o ∧ Triple k f x b p

/-- No extension of `p` has a coded child witness for membership of `x` in `y`. -/
def CodeNeg (d c k o f x y p : ZFSet.{u}) : Prop :=
  ∀ q ∈ c, ZFSet.pair q p ∈ o → ¬ CodeWitness d c k o f x y q

/-- A child of `x` tagged above `p` has coded nonmembership in `y` below `p`. -/
def CodeRefute (d c k o f x y p : ZFSet.{u}) : Prop :=
  ∃ a ∈ d, ∃ s ∈ c, ZFSet.pair a s ∈ x ∧ ZFSet.pair p s ∈ o ∧ CodeNeg d c k o f a y p

namespace AtomicFormula
open Formula

/-- Bounded formula expressing the coded child witness for atomic membership forcing. -/
def witness (d c k o f x y p : ℕ) : Formula :=
  .existsMem d (.existsMem (c+1)
    (.conj (pairMem 1 0 (y+2)) (.conj (pairMem (p+2) 0 (o+2))
      (triple (k+2) (f+2) (x+2) 1 (p+2)))))

theorem eval_witness (d c k o f x y p : ℕ) (e : ℕ → ZFSet.{u}) :
    (witness d c k o f x y p).Eval e ↔
      CodeWitness (e d) (e c) (e k) (e o) (e f) (e x) (e y) (e p) := by
  simp only [witness,Formula.Eval,eval_pairMem,eval_triple,cons_zero,cons_succ,CodeWitness]

/-- Bounded formula expressing absence of a coded membership witness below every extension. -/
def negMem (d c k o f x y p : ℕ) : Formula :=
  allMem c (imp (pairMem 0 (p+1) (o+1))
    (.neg (witness (d+1) (c+1) (k+1) (o+1) (f+1) (x+1) (y+1) 0)))

theorem eval_negMem (d c k o f x y p : ℕ) (e : ℕ → ZFSet.{u}) :
    (negMem d c k o f x y p).Eval e ↔
      CodeNeg (e d) (e c) (e k) (e o) (e f) (e x) (e y) (e p) := by
  simp only [negMem,eval_allMem,eval_imp,Formula.Eval,eval_pairMem,eval_witness,
    cons_zero,cons_succ,CodeNeg]

/-- Bounded formula expressing a child witness refuting coded equality. -/
def refute (d c k o f x y p : ℕ) : Formula :=
  .existsMem d (.existsMem (c+1)
    (.conj (pairMem 1 0 (x+2)) (.conj (pairMem (p+2) 0 (o+2))
      (negMem (d+2) (c+2) (k+2) (o+2) (f+2) 1 (y+2) (p+2)))))

theorem eval_refute (d c k o f x y p : ℕ) (e : ℕ → ZFSet.{u}) :
    (refute d c k o f x y p).Eval e ↔
      CodeRefute (e d) (e c) (e k) (e o) (e f) (e x) (e y) (e p) := by
  simp only [refute,Formula.Eval,eval_pairMem,eval_negMem,cons_zero,cons_succ,CodeRefute]

/-- Bounded formula deciding between a coded membership witness and coded nonmembership. -/
def memTest (d c k o f x y p : ℕ) : Formula :=
  disj (witness d c k o f x y p) (negMem d c k o f x y p)

/-- Bounded formula deciding between coded equality and a child refutation in either
direction. -/
def eqTest (d c k o f x y p : ℕ) : Formula :=
  disj (triple k f x y p) (disj (refute d c k o f x y p) (refute d c k o f y x p))
end AtomicFormula

variable {c : ZFSet.{u}} [Preorder (Conditions c)]

omit [Preorder (Conditions c)] in
private theorem child_mem {d : ZFSet.{u}} (hd : Transitive d)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ d) (i : a.arity) :
    (a.child i).encode (label c) ∈ d := by
  apply names_childClosed d c hd a ha
  cases a
  exact ⟨i,rfl⟩

theorem codeWitness_iff {d o f : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (hf : Graph d c o f) (a b : Name (Conditions c))
    (ha : a.encode (label c) ∈ d) (hb : b.encode (label c) ∈ d) (p : Conditions c) :
    CodeWitness d c (ZFSet.prod d d) o f (a.encode (label c)) (b.encode (label c)) (label c p) ↔
      Witness a b p := by
  have hrel (j) := (triple_pair ha (child_mem hd b hb j)).trans
    (hf.correct hd ho a (b.child j) ha (child_mem hd b hb j) p)
  cases b with
  | mk κ b t =>
    constructor
    · rintro ⟨x,hx,s,hs,hxs,hps,he⟩
      obtain ⟨j,hj,hjs⟩ := (pair_mem_encode _ _ _ _).mp hxs
      subst x
      subst s
      exact ⟨j,(ho p (t j)).mp hps,(hrel j).mp he⟩
    · rintro ⟨j,hj,he⟩
      exact ⟨_,child_mem hd _ hb j,_,label_mem c (t j),
        (pair_mem_encode _ _ _ _).mpr ⟨j,rfl,rfl⟩,(ho p (t j)).mpr hj,(hrel j).mpr he⟩

theorem negMem_iff_no_witness (a b : Name (Conditions c)) (p : Conditions c) :
    NegMem a b p ↔ ∀ q, q ≤ p → ¬ Witness a b q := by
  constructor
  · intro h q hq hw
    exact h q hq (witness_mem a b q hw)
  · intro h q hq hm
    cases b with
    | mk κ b t =>
      obtain ⟨r,hr,hw⟩ := hm q le_rfl
      exact h r (hr.trans hq) hw

theorem codeNeg_iff {d o f : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (hf : Graph d c o f) (a b : Name (Conditions c))
    (ha : a.encode (label c) ∈ d) (hb : b.encode (label c) ∈ d) (p : Conditions c) :
    CodeNeg d c (ZFSet.prod d d) o f (a.encode (label c)) (b.encode (label c)) (label c p) ↔
      NegMem a b p := by
  rw [negMem_iff_no_witness]
  constructor
  · intro h q hq hw
    exact h _ (label_mem c q) ((ho q p).mpr hq) ((codeWitness_iff hd ho hf a b ha hb q).mpr hw)
  · intro h q hq hqp hw
    obtain ⟨r,rfl⟩ := label_surjective c hq
    exact h r ((ho r p).mp hqp) ((codeWitness_iff hd ho hf a b ha hb r).mp hw)

theorem codeRefute_iff {d o f : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (hf : Graph d c o f) (a b : Name (Conditions c))
    (ha : a.encode (label c) ∈ d) (hb : b.encode (label c) ∈ d) (p : Conditions c) :
    CodeRefute d c (ZFSet.prod d d) o f (a.encode (label c)) (b.encode (label c)) (label c p) ↔
      ∃ i, p ≤ a.tag i ∧ NegMem (a.child i) b p := by
  constructor
  · rintro ⟨x,hx,s,hs,hxs,hps,hn⟩
    obtain ⟨i,hi,his⟩ := (pair_mem_encode _ _ _ _).mp hxs
    subst x
    subst s
    exact ⟨i,(ho p (a.tag i)).mp hps,
      (codeNeg_iff hd ho hf _ b (child_mem hd a ha i) hb p).mp hn⟩
  · rintro ⟨i,hi,hn⟩
    exact ⟨_,child_mem hd a ha i,_,label_mem c (a.tag i),
      (pair_mem_encode _ _ _ _).mpr ⟨i,rfl,rfl⟩,(ho p (a.tag i)).mpr hi,
      (codeNeg_iff hd ho hf _ b (child_mem hd a ha i) hb p).mpr hn⟩

end TuringRigidity.AtomicForcing

end OAI
