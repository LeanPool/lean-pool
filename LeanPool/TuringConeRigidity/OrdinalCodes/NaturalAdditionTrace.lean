/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NaturalAdditionTrace.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteNaturalGraph
public import LeanPool.TuringConeRigidity.SetModels.ModelIterationFormula

/-!
# Natural Addition Trace
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

/-- A finite function graph starting at `x` and following successor for `n` steps. -/
def AdditionTrace (o z k n x f : ZFSet.{u}) : Prop :=
  ModelIterationTrace o o z k n x f (fun _ v w => w = insert v v)

theorem additionTrace_exists (a n : ℕ) :
    AdditionTrace ZFSet.omega (natSet 0) (natSet (n+1)) (natSet n) (natSet a)
      (finiteNaturalGraph.{u} (fun i => a+i) n) := by
  apply modelIterationTrace_exists ZFSet.omega (fun i => natSet (a+i))
    (fun i => (mem_omega _).mpr ⟨a+i, rfl⟩)
  intro i
  rw [Nat.add_succ]
  rfl

theorem AdditionTrace.correct {z k f : ZFSet.{u}} (a n : ℕ)
    (hf : AdditionTrace ZFSet.omega z k (natSet n) (natSet a) f)
    {y : ZFSet.{u}} (hy : ZFSet.pair (natSet n) y ∈ f) : y = natSet (a+n) := by
  apply ModelIterationTrace.correct (R := ZFSet.omega) (z := z) (k := k) (f := f)
    (fun i => natSet (a+i)) (fun i => (mem_omega _).mpr ⟨a+i, rfl⟩) n
    (fun _ v w => w = insert v v)
  · intro i w _ hw
    rw [Nat.add_succ]
    exact hw
  · exact hf
  · exact hy

namespace Formula
/-- Bounded formula expressing the finite successor trace for addition. -/
def additionTrace (o z k n x f : ℕ) : Formula :=
  modelIterationTrace o o z k n x f (.successor 0 1)

theorem eval_additionTrace (o z k n x f : ℕ) (e : ℕ → ZFSet.{u}) :
    (additionTrace o z k n x f).Eval e ↔ AdditionTrace (e o) (e z) (e k) (e n) (e x) (e f) := by
  simp only [additionTrace, eval_modelIterationTrace, eval_successor, cons_zero, cons_succ,
    AdditionTrace]

/-- Bounded formula computing addition by selecting the endpoint of a successor trace. -/
def addition (o Q x n y : ℕ) : Formula :=
  modelIteration o o Q n x y (.successor 0 1)

theorem eval_addition (o Q x n y : ℕ) (e : ℕ → ZFSet.{u}) :
    (addition o Q x n y).Eval e ↔ ∃ k ∈ e o, ∃ z ∈ e o, ∃ f ∈ e Q,
      AdditionTrace (e o) z k (e n) (e x) f ∧ ZFSet.pair (e n) (e y) ∈ f := by
  simp only [addition, eval_modelIteration, eval_successor, cons_zero, cons_succ, AdditionTrace]

end Formula

theorem additionFormula_correct (Q : ZFSet.{u})
    (hQ : ∀ f : ℕ → ℕ, ∀ n, finiteNaturalGraph f n ∈ Q) (a n : ℕ) (y : ZFSet.{u}) :
    (Formula.addition 3 4 1 2 0).Eval (cons y (cons (natSet a) (cons (natSet n)
      (cons ZFSet.omega (fun _ => Q))))) ↔ y = natSet (a+n) := by
  let e := cons y (cons (natSet a) (cons (natSet n) (cons ZFSet.omega (fun _ => Q))))
  apply Formula.modelIteration_spec_of_graph_mem 3 3 4 2 1 0 (.successor 0 1) e rfl n rfl
    (fun i => natSet (a+i))
  · intro i
    exact (mem_omega _).mpr ⟨a+i, rfl⟩
  · rfl
  · exact hQ (fun i => a+i) n
  · intro i w _
    simp only [Formula.eval_successor, cons_zero, cons_succ]
    rw [Nat.add_succ]
    rfl

end TuringRigidity.BoundedSetTheory

end OAI
