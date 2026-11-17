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
public import LeanPool.TuringConeRigidity.Effective.FiniteTuple

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
  :=
  TransitiveNameModel.FunctionGraph k o f ∧ k = insert n n ∧ z = ∅ ∧ ZFSet.pair z b ∈ f ∧
    ∀ i ∈ n, ∀ j ∈ o, j = insert i i → ∀ v ∈ o, ∀ w ∈ o,
      ZFSet.pair i v ∈ f → ZFSet.pair j w ∈ f → S i v w

theorem iterationTrace_exists (b : ℕ) (g : ℕ → ℕ → ℕ)
    (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : ∀ i v, S (natSet i) (natSet v) (natSet (g i v))) (n : ℕ) :
    IterationTrace ZFSet.omega (natSet 0) (natSet (n+1)) (natSet n) (natSet b)
      (finiteNaturalGraph (fun i => Nat.rec b g i) n) S := by
  refine ⟨finiteNaturalGraph_function _ n,rfl,rfl,?_,?_⟩
  · exact (finiteNaturalGraph_pair _ n 0 _).mpr ⟨Nat.zero_le _,rfl⟩
  · intro i hi j _ hj v _ w _ hiv hjw
    obtain ⟨i,_,rfl⟩ := (mem_natSet n i).mp hi
    have hj' : j = natSet (i+1) := hj
    subst j
    rw [((finiteNaturalGraph_pair _ n i v).mp hiv).2,
      ((finiteNaturalGraph_pair _ n (i+1) w).mp hjw).2]
    exact hS i (Nat.rec b g i)

theorem IterationTrace.correct {z k f : ZFSet.{u}} (b n : ℕ) (g : ℕ → ℕ → ℕ)
    (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : ∀ i v w, S (natSet i) (natSet v) w → w = natSet (g i v))
    (hf : IterationTrace ZFSet.omega z k (natSet n) (natSet b) f S)
    {y : ZFSet.{u}} (hy : ZFSet.pair (natSet n) y ∈ f) : y = natSet (Nat.rec b g n) := by
  obtain ⟨hfun,hk,rfl,hzero,hstep⟩ := hf
  have hk' : k = natSet (n+1) := hk
  subst k
  have computes (i : ℕ) (hi : i ≤ n) : ZFSet.pair (natSet i) (natSet (Nat.rec b g i)) ∈ f := by
    induction i with
    | zero => exact hzero
    | succ i ih =>
      have hin : i ≤ n := by omega
      have hj : natSet.{u} (i+1) ∈ natSet (n+1) := (natSet_mem_natSet _ _).mpr (by omega)
      obtain ⟨w,hw,hjw,_⟩ := hfun.2 _ hj
      have hs := hstep (natSet i) ((natSet_mem_natSet _ _).mpr (by omega)) (natSet (i+1))
        ((mem_omega _).mpr ⟨i+1,rfl⟩) rfl (natSet (Nat.rec b g i))
        ((mem_omega _).mpr ⟨Nat.rec b g i,rfl⟩) w hw (ih hin) hjw
      have he : w = natSet (Nat.rec b g (i+1)) := hS i (Nat.rec b g i) w hs
      exact he ▸ hjw
  exact hfun.functional ((natSet_mem_natSet n (n+1)).mpr (Nat.lt_succ_self n)) hy (computes n
    le_rfl)

namespace Formula
/-- Variable renaming supplying the step index and adjacent values inside an iteration trace. -/
def iterationVars : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | i+3 => i+4

/-- Bounded formula expressing the initial value and every adjacent iteration step. -/
def iterationTrace (o z k n b f : ℕ) (θ : Formula) : Formula :=
  .conj (.functionGraph f k o) (.conj (.successor k n) (.conj (.empty z)
    (.conj (.pairMem z b f)
      (allMem n (allMem (o+1) (imp (.successor 0 1)
        (allMem (o+2) (allMem (o+3) (imp (.pairMem 3 1 (f+4))
          (imp (.pairMem 2 0 (f+4)) (θ.rename iterationVars)))))))))))

theorem eval_iterationTrace (o z k n b f : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u}) :
    (iterationTrace o z k n b f θ).Eval e ↔ IterationTrace (e o) (e z) (e k) (e n) (e b) (e f)
      (fun i v w => θ.Eval (cons w (cons v (cons i e)))) := by
  simp only [iterationTrace,IterationTrace,TransitiveNameModel.FunctionGraph,Formula.Eval,
eval_functionGraph, eval_successor, eval_empty, eval_pairMem, eval_allMem, eval_imp, eval_rename,
  cons_zero, cons_succ]
  have eq (i j v w : ZFSet.{u}) :
      (fun n => cons w (cons v (cons j (cons i e))) (iterationVars n)) = cons w (cons v (cons i
        e)) := by
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
