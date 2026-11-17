/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NaturalIterationFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NaturalIterationTrace
public import LeanPool.TuringConeRigidity.OrdinalCodes.NaturalAdditionTrace

/-!
# Natural Iteration Formula
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace Formula

theorem addition_spec (o Q x n y : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (a b : ℕ) (ha : e x = natSet a) (hb : e n = natSet b) :
    (addition o Q x n y).Eval e ↔ e y = natSet (a+b) := by
  have h := additionFormula_correct (e Q) hQ a b (e y)
  rw [eval_addition] at h
  simp only [cons_zero,cons_succ] at h
  rw [eval_addition,ho,ha,hb]
  exact h

/-- Shift outer parameters to reserve the auxiliary slots used by a finite iteration trace. -/
def iterationOuterVars : ℕ → ℕ := modelIterationOuterVars

/-- The first step parameter retains index zero. -/
theorem iterationOuterVars_zero : iterationOuterVars 0 = 0 := rfl

/-- The second step parameter retains index one. -/
theorem iterationOuterVars_one : iterationOuterVars 1 = 1 := rfl

/-- The third step parameter retains index two. -/
theorem iterationOuterVars_two : iterationOuterVars 2 = 2 := rfl

/-- Other parameters shift past the three existential trace witnesses. -/
theorem iterationOuterVars_add_three (i : ℕ) : iterationOuterVars (i+3) = i+6 := rfl

/-- Bounded formula selecting the endpoint of a finite iteration with step formula `θ`. -/
def iteration (o Q n b y : ℕ) (θ : Formula) : Formula :=
  modelIteration o o Q n b y θ

theorem eval_iteration (o Q n b y : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u}) :
    (iteration o Q n b y θ).Eval e ↔ ∃ k ∈ e o, ∃ z ∈ e o, ∃ f ∈ e Q,
      IterationTrace (e o) z k (e n) (e b) f
        (fun i v w => θ.Eval (cons w (cons v (cons i e)))) ∧ ZFSet.pair (e n) (e y) ∈ f := by
  exact eval_modelIteration o o Q n b y θ e

theorem iteration_spec (o Q n b y : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (N B : ℕ) (hn : e n = natSet N) (hb : e b = natSet B) (g : ℕ → ℕ → ℕ)
    (hθ : ∀ i v w, θ.Eval (cons w (cons (natSet v) (cons (natSet i) e))) ↔ w = natSet (g i v)) :
    (iteration o Q n b y θ).Eval e ↔ e y = natSet (Nat.rec B g N) := by
  let a (i : ℕ) : ZFSet.{u} := natSet (Nat.rec B g i)
  apply modelIteration_spec_of_graph_mem o o Q n b y θ e ho N hn a
  · intro i
    rw [ho]
    exact (mem_omega _).mpr ⟨Nat.rec B g i, rfl⟩
  · exact hb
  · exact hQ (fun i => Nat.rec B g i) N
  · intro i w _
    exact hθ i (Nat.rec B g i) w

end Formula
end TuringRigidity.BoundedSetTheory

end OAI
