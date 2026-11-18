/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/TermFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.FiniteTerm

/-!
# Term Formula
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace Formula

/-- Bounded formula recognizing the nested ordered pair `(a, (b, c))`. -/
def rightPair (s a b c : ℕ) : Formula := .existsMem s (.existsMem 0
  (.conj (.orderedPair (s+2) (a+2) 0) (.orderedPair 0 (b+2) (c+2))))

/-- Bounded formula recognizing the nested ordered pair `((a, b), c)`. -/
def leftPair (s a b c : ℕ) : Formula := .existsMem s (.existsMem 0
  (.conj (.orderedPair (s+2) 0 (c+2)) (.orderedPair 0 (a+2) (b+2))))

theorem eval_rightPair (s a b c : ℕ) (e : ℕ → ZFSet.{u}) :
    (rightPair s a b c).Eval e ↔ e s = ZFSet.pair (e a) (ZFSet.pair (e b) (e c)) := by
  simp only [rightPair,Eval,eval_orderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨p,_,q,_,h,rfl⟩; exact h
  · intro h
    refine ⟨{e a,ZFSet.pair (e b) (e c)},?_,ZFSet.pair (e b) (e c),?_,h,rfl⟩
    · rw [h]; exact ZFSet.mem_pair.mpr (Or.inr rfl)
    · exact ZFSet.mem_pair.mpr (Or.inr rfl)

theorem eval_leftPair (s a b c : ℕ) (e : ℕ → ZFSet.{u}) :
    (leftPair s a b c).Eval e ↔ e s = ZFSet.pair (ZFSet.pair (e a) (e b)) (e c) := by
  simp only [leftPair,Eval,eval_orderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨p,_,q,_,h,rfl⟩; exact h
  · intro h
    refine ⟨{ZFSet.pair (e a) (e b),e c},?_,ZFSet.pair (e a) (e b),?_,h,rfl⟩
    · rw [h]; exact ZFSet.mem_pair.mpr (Or.inr rfl)
    · exact ZFSet.mem_pair.mpr (Or.inl rfl)

/-- Bounded formula asserting that the pair input `(a,b)` has output `c` in `f`. -/
def appMem (a b c f : ℕ) : Formula := .existsMem f (leftPair 0 (a+1) (b+1) (c+1))

theorem eval_appMem (a b c f : ℕ) (e : ℕ → ZFSet.{u}) :
    (appMem a b c f).Eval e ↔ ZFSet.pair (ZFSet.pair (e a) (e b)) (e c) ∈ e f := by
  simp only [appMem,Eval,eval_leftPair,cons_zero,cons_succ]
  exact ⟨fun ⟨x,hx,he⟩ => he ▸ hx,fun h => ⟨_,h,rfl⟩⟩
end Formula
namespace FiniteTerm
open Formula

/-- Bounded formula describing the leaf, application, and pair cases of a finite-term
evaluation step. -/
def stepFormula (c v A B L O K D f z o t : ℕ) : Formula :=
  .disj (.existsMem A (.conj (.orderedPair (c+1) (z+1) 0) (.pairMem 0 (v+1) (L+1))))
    (.disj
      (.existsMem B (.existsMem (K+1) (.existsMem (D+2)
        (.conj (.rightPair (c+3) (o+3) 2 1)
          (.conj (.pairMem 1 0 (f+3)) (.appMem 2 0 (v+3) (O+3)))))))
      (.existsMem K (.existsMem (K+1) (.existsMem (D+2) (.existsMem (D+3)
        (.conj (.rightPair (c+4) (t+4) 3 2)
          (.conj (.pairMem 3 1 (f+4))
            (.conj (.pairMem 2 0 (f+4)) (.orderedPair (v+4) 1 0)))))))))

theorem eval_stepFormula (c v A B L O K D f z o t : ℕ) (e : ℕ → ZFSet.{u})
    (hz : e z = natSet 0) (ho : e o = natSet 1) (ht : e t = natSet 2) :
    (stepFormula c v A B L O K D f z o t).Eval e ↔
      Step (e A) (e B) (e L) (e O) (e K) (e D) (e f) (e c) (e v) := by
  simp only [stepFormula,Formula.Eval,eval_disj,eval_orderedPair,eval_rightPair,eval_pairMem,
    eval_appMem,cons_zero,cons_succ,hz,ho,ht,Step,tag]

/-- Bounded formula asserting that every graph entry satisfies the finite-term evaluation
certificate. -/
def certificateFormula (A B L O K D f z o t : ℕ) : Formula :=
  .allMem f (.existsMem (K+1) (.existsMem (D+2) (.conj (.orderedPair 2 1 0)
    (stepFormula 1 0 (A+3) (B+3) (L+3) (O+3) (K+3) (D+3) (f+3) (z+3) (o+3) (t+3)))))

theorem eval_certificateFormula (A B L O K D f z o t : ℕ) (e : ℕ → ZFSet.{u})
    (hz : e z = natSet 0) (ho : e o = natSet 1) (ht : e t = natSet 2) :
    (certificateFormula A B L O K D f z o t).Eval e ↔
      Certificate (e A) (e B) (e L) (e O) (e K) (e D) (e f) := by
  simp only [certificateFormula,eval_allMem,Formula.Eval,eval_orderedPair,cons_zero,cons_succ]
  apply forall_congr'; intro w
  apply forall_congr'; intro _
  apply exists_congr; intro c
  apply and_congr_right; intro _
  apply exists_congr; intro v
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  exact eval_stepFormula 1 0 (A+3) (B+3) (L+3) (O+3) (K+3) (D+3) (f+3)
    (z+3) (o+3) (t+3) (cons v (cons c (cons w e))) hz ho ht

end FiniteTerm
end TuringRigidity.BoundedSetTheory

end OAI
