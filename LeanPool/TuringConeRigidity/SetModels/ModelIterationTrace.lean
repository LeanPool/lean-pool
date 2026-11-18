/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelIterationTrace.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.FiniteModelGraph
public import LeanPool.TuringConeRigidity.Effective.FiniteTuple

/-!
# Model Iteration Trace
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

/-- A graph into `R` with domain `insert n n`, starting at `b` at the empty index and obeying
indexed transitions. -/
def ModelIterationTrace (o R z k n b f : ZFSet.{u}) (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
  : Prop :=
  TransitiveNameModel.FunctionGraph k R f ∧ k = insert n n ∧ z = ∅ ∧ ZFSet.pair z b ∈ f ∧
    ∀ i ∈ n, ∀ j ∈ o, j = insert i i → ∀ v ∈ R, ∀ w ∈ R,
      ZFSet.pair i v ∈ f → ZFSet.pair j w ∈ f → S i v w

theorem modelIterationTrace_exists (R : ZFSet.{u}) (a : ℕ → ZFSet.{u})
    (ha : ∀ i, a i ∈ R) (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : ∀ i, S (natSet i) (a i) (a (i + 1))) (n : ℕ) :
    ModelIterationTrace ZFSet.omega R (natSet 0) (natSet (n+1)) (natSet n) (a 0)
      (finiteModelGraph a n) S := by
  refine ⟨finiteModelGraph_function R a ha n,rfl,rfl,?_,?_⟩
  · exact (finiteModelGraph_pair a n 0 _).mpr ⟨Nat.zero_le _,rfl⟩
  · intro i hi j _ hj v _ w _ hiv hjw
    obtain ⟨i,_,rfl⟩ := (mem_natSet n i).mp hi
    have hj' : j = natSet (i+1) := hj
    subst j
    rw [((finiteModelGraph_pair a n i v).mp hiv).2,
      ((finiteModelGraph_pair a n (i+1) w).mp hjw).2]
    exact hS i

theorem ModelIterationTrace.correct {R z k f : ZFSet.{u}} (a : ℕ → ZFSet.{u})
    (ha : ∀ i, a i ∈ R) (n : ℕ)
    (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : ∀ i w, w ∈ R → S (natSet i) (a i) w → w = a (i + 1))
    (hf : ModelIterationTrace ZFSet.omega R z k (natSet n) (a 0) f S)
    {y : ZFSet.{u}} (hy : ZFSet.pair (natSet n) y ∈ f) : y = a n := by
  obtain ⟨hfun,hk,rfl,hzero,hstep⟩ := hf
  have hk' : k = natSet (n+1) := hk
  subst k
  have computes (i : ℕ) (hi : i ≤ n) : ZFSet.pair (natSet i) (a i) ∈ f := by
    induction i with
    | zero => exact hzero
    | succ i ih =>
      have hin : i ≤ n := by omega
      have hj : natSet.{u} (i+1) ∈ natSet (n+1) := (natSet_mem_natSet _ _).mpr (by omega)
      obtain ⟨w,hw,hjw,_⟩ := hfun.2 _ hj
      have hs := hstep (natSet i) ((natSet_mem_natSet _ _).mpr (by omega)) (natSet (i+1))
        ((mem_omega _).mpr ⟨i+1,rfl⟩) rfl (a i) (ha i) w hw (ih hin) hjw
      have he : w = a (i+1) := hS i w hw hs
      exact he ▸ hjw
  exact hfun.functional ((natSet_mem_natSet n (n+1)).mpr (Nat.lt_succ_self n)) hy (computes n
    le_rfl)

namespace Formula
/-- Variable renaming supplying the index and adjacent values in a model iteration trace. -/
def modelIterationVars : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | i+3 => i+4

/-- Bounded formula expressing the function graph, initial value, and transitions of a model
iteration trace. -/
def modelIterationTrace (o R z k n b f : ℕ) (θ : Formula) : Formula :=
  .conj (.functionGraph f k R) (.conj (.successor k n) (.conj (.empty z)
    (.conj (.pairMem z b f)
      (allMem n (allMem (o+1) (imp (.successor 0 1)
        (allMem (R+2) (allMem (R+3) (imp (.pairMem 3 1 (f+4))
          (imp (.pairMem 2 0 (f+4)) (θ.rename modelIterationVars)))))))))))

theorem eval_modelIterationTrace (o R z k n b f : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u}) :
    (modelIterationTrace o R z k n b f θ).Eval e ↔ ModelIterationTrace (e o) (e R) (e z) (e k) (e
      n) (e b) (e f)
      (fun i v w => θ.Eval (cons w (cons v (cons i e)))) := by
  simp only [modelIterationTrace,ModelIterationTrace,TransitiveNameModel.FunctionGraph,Formula.Eval,
eval_functionGraph, eval_successor, eval_empty, eval_pairMem, eval_allMem, eval_imp, eval_rename,
  cons_zero, cons_succ]
  have eq (i j v w : ZFSet.{u}) :
      (fun n => cons w (cons v (cons j (cons i e))) (modelIterationVars n)) = cons w (cons v (cons
        i e)) := by
    funext n
    rcases n with _ | n
    · rfl
    rcases n with _ | n
    · rfl
    rcases n with _|n <;> rfl
  simp only [eq]
end Formula

end TuringRigidity.BoundedSetTheory

end OAI
