/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NaturalMultiplicationFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NaturalIterationFormula

/-!
# Natural Multiplication Formula
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

theorem nat_iteration_add (a n : ℕ) : Nat.rec 0 (fun _ v => v+a) n = a*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    change Nat.rec 0 (fun _ v => v+a) n + a = a*(n+1)
    rw [ih,Nat.mul_succ]

namespace Formula
def multiplication (o Q x n y : ℕ) : Formula := .existsMem o
  (.conj (.empty 0) (iteration (o+1) (Q+1) (n+1) 0 (y+1)
    (addition (o+4) (Q+4) 1 (x+4) 0)))

theorem multiplication_spec (o Q x n y : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (a b : ℕ) (ha : e x = natSet a) (hb : e n = natSet b) :
    (multiplication o Q x n y).Eval e ↔ e y = natSet (a*b) := by
  have hθ (i v : ℕ) (w : ZFSet.{u}) :
      (addition (o+4) (Q+4) 1 (x+4) 0).Eval
        (cons w (cons (natSet v) (cons (natSet i) (cons ∅ e)))) ↔ w = natSet (v+a) := by
    apply addition_spec (o+4) (Q+4) 1 (x+4) 0
      (cons w (cons (natSet v) (cons (natSet i) (cons ∅ e))))
      (by simpa only [cons_succ] using ho)
      (by intro f k; simpa only [cons_succ] using hQ f k) v a rfl
    simpa only [cons_succ] using ha
  have hi := iteration_spec (o+1) (Q+1) (n+1) 0 (y+1)
    (addition (o+4) (Q+4) 1 (x+4) 0) (cons ∅ e)
    (by simpa only [cons_succ] using ho)
    (by intro f k; simpa only [cons_succ] using hQ f k) b 0
    (by simpa only [cons_succ] using hb) rfl (fun _ v => v+a) hθ
  simp only [cons_succ,nat_iteration_add] at hi
  simp only [multiplication,Formula.Eval,eval_empty,cons_zero]
  constructor
  · rintro ⟨z,_,rfl,h⟩
    exact hi.mp h
  · intro h
    exact ⟨∅,ho.symm ▸ ZFSet.omega_zero,rfl,hi.mpr h⟩

end Formula
end TuringRigidity.BoundedSetTheory

end OAI
