/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/AtomicGraphCorrect.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.AtomicGraph
public import LeanPool.TuringConeRigidity.Syntax.AtomicEncoding
public import LeanPool.TuringConeRigidity.SetModels.NameUnionCode

/-!
# Atomic Graph Correct
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem triple_pair {d f x y q : ZFSet.{u}} (hx : x ∈ d) (hy : y ∈ d) :
    Triple (ZFSet.prod d d) f x y q ↔ ZFSet.pair (ZFSet.pair x y) q ∈ f := by
  constructor
  · rintro ⟨v,_,rfl,h⟩; exact h
  · intro h
    exact ⟨_,ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,rfl,h⟩

omit [Preorder (Conditions c)] in
private theorem child_code_mem {d : ZFSet.{u}} (hd : Transitive d)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ d) (i : a.arity) :
    (a.child i).encode (label c) ∈ d := by
  apply names_childClosed d c hd a ha
  cases a
  exact ⟨i,rfl⟩

theorem match_encode (flip : Bool) {d k o f a : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (b : Name (Conditions c)) (hb : b.encode (label c) ∈ d) (q : Conditions c) :
    Match flip d c k o f a (b.encode (label c)) (label c q) ↔
      ∃ r, r ≤ q ∧ ∃ j, r ≤ b.tag j ∧
        Triple k f (if flip then (b.child j).encode (label c) else a)
          (if flip then a else (b.child j).encode (label c)) (label c r) := by
  constructor
  · rintro ⟨r,hr,hrq,x,hx,t,ht,hxt,hrt,hf⟩
    obtain ⟨s,rfl⟩ := label_surjective c hr
    obtain ⟨j,hj,hjt⟩ := (pair_mem_encode (label c) b x t).mp hxt
    subst x
    subst t
    exact ⟨s,(ho s q).mp hrq,j,(ho s (b.tag j)).mp hrt,hf⟩
  · rintro ⟨r,hrq,j,hrj,hf⟩
    exact ⟨label c r,label_mem c r,(ho r q).mpr hrq,
      _,child_code_mem hd b hb j,_,label_mem c (b.tag j),
      (pair_mem_encode _ _ _ _).mpr ⟨j,rfl,rfl⟩,(ho r (b.tag j)).mpr hrj,hf⟩

theorem side_encode (flip : Bool) {d k o f : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (a b : Name (Conditions c)) (ha : a.encode (label c) ∈ d)
    (hb : b.encode (label c) ∈ d) (p : Conditions c) :
    Side flip d c k o f (a.encode (label c)) (b.encode (label c)) (label c p) ↔
      ∀ i, Below p (a.tag i) (fun r => ∃ j, r ≤ b.tag j ∧
        Triple k f (if flip then (b.child j).encode (label c) else (a.child i).encode (label c))
          (if flip then (a.child i).encode (label c) else (b.child j).encode (label c)) (label c
            r)) := by
  constructor
  · intro h i q hqp hqi
    have hm := h _ (child_code_mem hd a ha i) _ (label_mem c (a.tag i))
      ((pair_mem_encode _ _ _ _).mpr ⟨i,rfl,rfl⟩) _ (label_mem c q)
      ((ho q p).mpr hqp) ((ho q (a.tag i)).mpr hqi)
    exact (match_encode flip hd ho b hb q).mp hm
  · intro h x hx s hs hxs q hq hqp hqs
    obtain ⟨i,hi,his⟩ := (pair_mem_encode (label c) a x s).mp hxs
    subst x
    subst s
    obtain ⟨r,rfl⟩ := label_surjective c hq
    exact (match_encode flip hd ho b hb r).mpr
      (h i r ((ho r p).mp hqp) ((ho r (a.tag i)).mp hqs))

theorem Graph.correct {d o f : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (hf : Graph d c o f) (a b : Name (Conditions c))
    (ha : a.encode (label c) ∈ d) (hb : b.encode (label c) ∈ d) (p : Conditions c) :
    ZFSet.pair (ZFSet.pair (a.encode (label c)) (b.encode (label c))) (label c p) ∈ f ↔
      EqForces a b p := by
  induction a generalizing b p with
  | mk ι a s ih =>
    cases b with
    | mk κ b t =>
      have hai (i) : (a i).encode (label c) ∈ d := child_code_mem hd _ ha i
      have hbj (j) : (b j).encode (label c) ∈ d := child_code_mem hd _ hb j
      have hrel (i j) (q : Conditions c) :
          Triple (ZFSet.prod d d) f ((a i).encode (label c)) ((b j).encode (label c)) (label c q) ↔
            EqForces (a i) (b j) q :=
        (triple_pair (hai i) (hbj j)).trans (ih i (b j) (hai i) (hbj j) q)
      rw [hf.2 _ ha _ hb _ (label_mem c p)]
      change (Side false _ _ _ _ _ _ _ _ ∧ Side true _ _ _ _ _ _ _ _) ↔ _
      rw [side_encode false hd ho _ _ ha hb p, side_encode true hd ho _ _ hb ha p]
      simp only [Bool.false_eq_true,ite_false,ite_true,Name.arity,Name.child,Name.tag]
      simp only [Below,hrel,EqForces]

end TuringRigidity.AtomicForcing

end OAI
