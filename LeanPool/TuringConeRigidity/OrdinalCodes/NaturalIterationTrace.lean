/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NaturalIterationTrace.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteNaturalGraph
public import LeanPool.TuringConeRigidity.SetModels.ModelIterationTrace

/-!
# Natural Iteration Trace
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

/-- A finite function graph starting at `b` and obeying the indexed step relation `S`. -/
def IterationTrace (o z k n b f : ZFSet.{u}) (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : Prop
  := ModelIterationTrace o o z k n b f S

theorem iterationTrace_exists (b : ℕ) (g : ℕ → ℕ → ℕ)
    (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : ∀ i v, S (natSet i) (natSet v) (natSet (g i v))) (n : ℕ) :
    IterationTrace ZFSet.omega (natSet 0) (natSet (n+1)) (natSet n) (natSet b)
      (finiteNaturalGraph (fun i => Nat.rec b g i) n) S := by
  exact modelIterationTrace_exists ZFSet.omega (fun i => natSet (Nat.rec b g i))
    (fun i => (mem_omega _).mpr ⟨Nat.rec b g i, rfl⟩) S
    (fun i => hS i (Nat.rec b g i)) n

theorem IterationTrace.correct {z k f : ZFSet.{u}} (b n : ℕ) (g : ℕ → ℕ → ℕ)
    (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : ∀ i v w, S (natSet i) (natSet v) w → w = natSet (g i v))
    (hf : IterationTrace ZFSet.omega z k (natSet n) (natSet b) f S)
    {y : ZFSet.{u}} (hy : ZFSet.pair (natSet n) y ∈ f) : y = natSet (Nat.rec b g n) := by
  apply ModelIterationTrace.correct (R := ZFSet.omega) (z := z) (k := k) (f := f)
    (fun i => natSet (Nat.rec b g i))
    (fun i => (mem_omega _).mpr ⟨Nat.rec b g i, rfl⟩) n S
  · intro i w _ hs
    exact hS i (Nat.rec b g i) w hs
  · exact hf
  · exact hy

namespace Formula
/-- Variable renaming supplying the step index and adjacent values inside an iteration trace. -/
def iterationVars : ℕ → ℕ := modelIterationVars

/-- The output variable in an iteration step retains index zero. -/
theorem iterationVars_zero : iterationVars 0 = 0 := rfl

/-- The preceding value in an iteration step retains index one. -/
theorem iterationVars_one : iterationVars 1 = 1 := rfl

/-- The step index skips the intervening successor variable. -/
theorem iterationVars_two : iterationVars 2 = 3 := rfl

/-- Variables beyond the three step parameters shift past the extra successor binder. -/
theorem iterationVars_add_three (i : ℕ) : iterationVars (i+3) = i+4 := rfl

/-- Bounded formula expressing the initial value and every adjacent iteration step. -/
def iterationTrace (o z k n b f : ℕ) (θ : Formula) : Formula :=
  modelIterationTrace o o z k n b f θ

theorem eval_iterationTrace (o z k n b f : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u}) :
    (iterationTrace o z k n b f θ).Eval e ↔ IterationTrace (e o) (e z) (e k) (e n) (e b) (e f)
      (fun i v w => θ.Eval (cons w (cons v (cons i e)))) := by
  exact eval_modelIterationTrace o o z k n b f θ e

end Formula

end TuringRigidity.BoundedSetTheory

end OAI
