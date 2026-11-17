/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelIterationFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelIterationTrace

/-!
# Model Iteration Formula
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace Formula

def modelIterationOuterVars : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | i+3 => i+6

def modelIteration (o R Q n b y : ℕ) (θ : Formula) : Formula :=
  .existsMem o (.existsMem (o+1) (.existsMem (Q+2)
    (.conj (modelIterationTrace (o+3) (R+3) 1 2 (n+3) (b+3) 0 (θ.rename modelIterationOuterVars))
      (.pairMem (n+3) (y+3) 0))))

theorem eval_modelIteration (o R Q n b y : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u}) :
    (modelIteration o R Q n b y θ).Eval e ↔ ∃ k ∈ e o, ∃ z ∈ e o, ∃ f ∈ e Q,
      ModelIterationTrace (e o) (e R) z k (e n) (e b) f
        (fun i v w => θ.Eval (cons w (cons v (cons i e)))) ∧ ZFSet.pair (e n) (e y) ∈ f := by
  simp only
    [modelIteration, Formula.Eval, eval_modelIterationTrace, eval_pairMem, eval_rename, cons_zero,
      cons_succ]
  have eq (k z f i v w : ZFSet.{u}) :
      (fun n => cons w (cons v (cons i (cons f (cons z (cons k e))))) (modelIterationOuterVars n)) =
        cons w (cons v (cons i e)) := by
    funext n
    rcases n with _ | n
    · rfl
    rcases n with _ | n
    · rfl
    rcases n with _|n <;> rfl
  simp only [eq]

theorem modelIteration_spec (o R Q n b y : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega)
    (hQ : ∀ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ e R) → ∀ k, finiteModelGraph a k ∈ e Q)
    (N : ℕ) (hn : e n = natSet N) (a : ℕ → ZFSet.{u}) (ha : ∀ i, a i ∈ e R)
    (hb : e b = a 0)
    (hθ : ∀ i w, w ∈ e R →
      (θ.Eval (cons w (cons (a i) (cons (natSet i) e))) ↔ w = a (i+1))) :
    (modelIteration o R Q n b y θ).Eval e ↔ e y = a N := by
  rw [eval_modelIteration,ho,hn,hb]
  constructor
  · rintro ⟨k,_,z,_,f,_,hf,hy⟩
    exact hf.correct a ha N _ (fun i w hw h => (hθ i w hw).mp h) hy
  · intro hy
    refine ⟨natSet (N+1),(mem_omega _).mpr ⟨N+1,rfl⟩,natSet 0,(mem_omega _).mpr ⟨0,rfl⟩,
      finiteModelGraph a N,hQ a ha N,?_,?_⟩
    · exact modelIterationTrace_exists (e R) a ha _ (fun i => (hθ i _ (ha (i+1))).mpr rfl) N
    · exact (finiteModelGraph_pair a N N _).mpr ⟨le_rfl,hy⟩

end Formula
end TuringRigidity.BoundedSetTheory

end OAI
