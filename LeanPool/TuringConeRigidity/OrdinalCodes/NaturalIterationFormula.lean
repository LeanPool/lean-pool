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
def iterationOuterVars : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | i+3 => i+6

/-- Bounded formula selecting the endpoint of a finite iteration with step formula `θ`. -/
def iteration (o Q n b y : ℕ) (θ : Formula) : Formula :=
  .existsMem o (.existsMem (o+1) (.existsMem (Q+2)
    (.conj (iterationTrace (o+3) 1 2 (n+3) (b+3) 0 (θ.rename iterationOuterVars))
      (.pairMem (n+3) (y+3) 0))))

theorem eval_iteration (o Q n b y : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u}) :
    (iteration o Q n b y θ).Eval e ↔ ∃ k ∈ e o, ∃ z ∈ e o, ∃ f ∈ e Q,
      IterationTrace (e o) z k (e n) (e b) f
        (fun i v w => θ.Eval (cons w (cons v (cons i e)))) ∧ ZFSet.pair (e n) (e y) ∈ f := by
  simp only
    [iteration,Formula.Eval,eval_iterationTrace,eval_pairMem,eval_rename,cons_zero,cons_succ]
  have eq (k z f i v w : ZFSet.{u}) :
      (fun n => cons w (cons v (cons i (cons f (cons z (cons k e))))) (iterationOuterVars n)) =
        cons w (cons v (cons i e)) := by
    funext n
    rcases n with _ | n
    · rfl
    rcases n with _ | n
    · rfl
    rcases n with _|n <;> rfl
  simp only [eq]

theorem iteration_spec (o Q n b y : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (N B : ℕ) (hn : e n = natSet N) (hb : e b = natSet B) (g : ℕ → ℕ → ℕ)
    (hθ : ∀ i v w, θ.Eval (cons w (cons (natSet v) (cons (natSet i) e))) ↔ w = natSet (g i v)) :
    (iteration o Q n b y θ).Eval e ↔ e y = natSet (Nat.rec B g N) := by
  rw [eval_iteration,ho,hn,hb]
  constructor
  · rintro ⟨k,_,z,_,f,_,hf,hy⟩
    exact hf.correct B N g _ (fun i v w h => (hθ i v w).mp h) hy
  · intro hy
    refine ⟨natSet (N+1),(mem_omega _).mpr ⟨N+1,rfl⟩,natSet 0,(mem_omega _).mpr ⟨0,rfl⟩,
      finiteNaturalGraph (fun i => Nat.rec B g i) N,hQ _ _,?_,?_⟩
    · exact iterationTrace_exists B g _ (fun i v => (hθ i v _).mpr rfl) N
    · exact (finiteNaturalGraph_pair _ N N _).mpr ⟨le_rfl,hy⟩

end Formula
end TuringRigidity.BoundedSetTheory

end OAI
