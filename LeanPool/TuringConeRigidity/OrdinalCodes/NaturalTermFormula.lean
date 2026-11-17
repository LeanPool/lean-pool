/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NaturalTermFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NaturalMultiplicationFormula

/-!
# Natural Term Formula
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

inductive NaturalTerm where
  | var (i : ℕ)
  | binary (mul : Bool) (a b : NaturalTerm)

namespace NaturalTerm
def eval (v : ℕ → ℕ) : NaturalTerm → ℕ
  | .var i => v i
  | .binary m a b => if m then eval v a * eval v b else eval v a + eval v b

def operation (m : Bool) (o Q a b y : ℕ) : Formula :=
  if m then .multiplication o Q a b y else .addition o Q a b y

theorem operation_spec (m : Bool) (o Q x n y : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (a b : ℕ) (ha : e x = natSet a) (hb : e n = natSet b) :
    (operation m o Q x n y).Eval e ↔ e y = natSet (if m then a*b else a+b) := by
  cases m with
  | false => exact Formula.addition_spec o Q x n y e ho hQ a b ha hb
  | true => exact Formula.multiplication_spec o Q x n y e ho hQ a b ha hb

def graph (o Q y : ℕ) (v : ℕ → ℕ) : NaturalTerm → Formula
  | .var i => .equal y (v i)
  | .binary m a b => .existsMem o (.existsMem (o+1)
      (.conj (graph (o+2) (Q+2) 1 (fun i => v i+2) a)
        (.conj (graph (o+2) (Q+2) 0 (fun i => v i+2) b) (operation m (o+2) (Q+2) 1 0 (y+2)))))

theorem graph_spec (t : NaturalTerm) (o Q y : ℕ) (v : ℕ → ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (a : ℕ → ℕ) (ha : ∀ i, e (v i) = natSet (a i)) :
    (graph o Q y v t).Eval e ↔ e y = natSet (t.eval a) := by
  induction t generalizing o Q y v e with
  | var i => exact congrArg (fun z => e y = z) (ha i) |>.to_iff
  | binary m t s iht ihs =>
    have hωmem (k : ℕ) : natSet.{u} k ∈ e o := by
      rw [ho]; exact (mem_omega _).mpr ⟨k,rfl⟩
    have ht (w z : ZFSet.{u}) :
        (graph (o+2) (Q+2) 1 (fun i => v i+2) t).Eval (cons z (cons w e)) ↔ w = natSet (t.eval a) :=
      iht (o+2) (Q+2) 1 (fun i => v i+2) (cons z (cons w e)) ho hQ ha
    have hs (w z : ZFSet.{u}) :
        (graph (o+2) (Q+2) 0 (fun i => v i+2) s).Eval (cons z (cons w e)) ↔ z = natSet (s.eval a) :=
      ihs (o+2) (Q+2) 0 (fun i => v i+2) (cons z (cons w e)) ho hQ ha
    have hop := operation_spec m (o+2) (Q+2) 1 0 (y+2)
      (cons (natSet (s.eval a)) (cons (natSet (t.eval a)) e)) ho hQ (t.eval a) (s.eval a) rfl rfl
    simp only [graph,Formula.Eval]
    constructor
    · rintro ⟨w,_,z,_,hw,hz,h⟩
      obtain rfl := (ht w z).mp hw
      obtain rfl := (hs _ z).mp hz
      exact hop.mp h
    · intro h
      refine ⟨natSet (t.eval a),hωmem (t.eval a),
        natSet (s.eval a),hωmem (s.eval a),
        (ht _ _).mpr rfl,(hs _ _).mpr rfl,hop.mpr h⟩

end NaturalTerm
end TuringRigidity.BoundedSetTheory

end OAI
