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
  TransitiveNameModel.FunctionGraph k o f ∧ k = insert n n ∧ z = ∅ ∧ ZFSet.pair z x ∈ f ∧
    ∀ i ∈ n, ∀ j ∈ o, j = insert i i → ∀ v ∈ o, ∀ w ∈ o,
      ZFSet.pair i v ∈ f → ZFSet.pair j w ∈ f → w = insert v v

theorem additionTrace_exists (a n : ℕ) :
    AdditionTrace ZFSet.omega (natSet 0) (natSet (n+1)) (natSet n) (natSet a)
      (finiteNaturalGraph.{u} (fun i => a+i) n) := by
  refine ⟨finiteNaturalGraph_function _ n,rfl,rfl,?_,?_⟩
  · exact (finiteNaturalGraph_pair _ n 0 _).mpr ⟨Nat.zero_le _,by simp⟩
  · intro i hi j _ hj v _ w _ hiv hjw
    obtain ⟨i,hi,rfl⟩ := (mem_natSet n i).mp hi
    have hj' : j = natSet (i+1) := hj
    subst j
    have hv := ((finiteNaturalGraph_pair _ n i v).mp hiv).2
    have hw := ((finiteNaturalGraph_pair _ n (i+1) w).mp hjw).2
    rw [hv,hw,Nat.add_succ]
    rfl

theorem AdditionTrace.correct {z k f : ZFSet.{u}} (a n : ℕ)
    (hf : AdditionTrace ZFSet.omega z k (natSet n) (natSet a) f)
    {y : ZFSet.{u}} (hy : ZFSet.pair (natSet n) y ∈ f) : y = natSet (a+n) := by
  obtain ⟨hfun,hk,rfl,hzero,hstep⟩ := hf
  have hk' : k = natSet (n+1) := hk
  subst k
  have computes (i : ℕ) (hi : i ≤ n) : ZFSet.pair (natSet i) (natSet (a+i)) ∈ f := by
    induction i with
    | zero => simpa only [Nat.add_zero,natSet] using hzero
    | succ i ih =>
      have hin : i ≤ n := by omega
      have hj : natSet.{u} (i+1) ∈ natSet (n+1) := (natSet_mem_natSet _ _).mpr (by omega)
      obtain ⟨w,hw,hjw,_⟩ := hfun.2 _ hj
      have he := hstep (natSet i) ((natSet_mem_natSet _ _).mpr (by omega)) (natSet (i+1))
        ((mem_omega _).mpr ⟨i+1,rfl⟩) rfl (natSet (a+i)) ((mem_omega _).mpr ⟨a+i,rfl⟩)
        w hw (ih hin) hjw
      have he' : w = natSet (a+(i+1)) := by
        rw [Nat.add_succ]
        exact he
      exact he' ▸ hjw
  exact hfun.functional ((natSet_mem_natSet n (n+1)).mpr (Nat.lt_succ_self n)) hy (computes n
    le_rfl)

namespace Formula
/-- Bounded formula expressing the finite successor trace for addition. -/
def additionTrace (o z k n x f : ℕ) : Formula :=
  .conj (.functionGraph f k o) (.conj (.successor k n) (.conj (.empty z)
    (.conj (.pairMem z x f)
      (allMem n (allMem (o+1) (imp (.successor 0 1)
        (allMem (o+2) (allMem (o+3) (imp (.pairMem 3 1 (f+4))
          (imp (.pairMem 2 0 (f+4)) (.successor 0 1)))))))))))

theorem eval_additionTrace (o z k n x f : ℕ) (e : ℕ → ZFSet.{u}) :
    (additionTrace o z k n x f).Eval e ↔ AdditionTrace (e o) (e z) (e k) (e n) (e x) (e f) := by
  simp only
    [additionTrace, AdditionTrace, TransitiveNameModel.FunctionGraph, Formula.Eval,
      eval_functionGraph, eval_successor,
    eval_empty,eval_pairMem,eval_allMem,eval_imp,cons_zero,cons_succ]

/-- Bounded formula computing addition by selecting the endpoint of a successor trace. -/
def addition (o Q x n y : ℕ) : Formula := .existsMem o (.existsMem (o+1) (.existsMem (Q+2)
  (.conj (additionTrace (o+3) 1 2 (n+3) (x+3) 0) (.pairMem (n+3) (y+3) 0))))

theorem eval_addition (o Q x n y : ℕ) (e : ℕ → ZFSet.{u}) :
    (addition o Q x n y).Eval e ↔ ∃ k ∈ e o, ∃ z ∈ e o, ∃ f ∈ e Q,
      AdditionTrace (e o) z k (e n) (e x) f ∧ ZFSet.pair (e n) (e y) ∈ f := by
  simp only [addition,Formula.Eval,eval_additionTrace,eval_pairMem,cons_zero,cons_succ]
end Formula

theorem additionFormula_correct (Q : ZFSet.{u})
    (hQ : ∀ f : ℕ → ℕ, ∀ n, finiteNaturalGraph f n ∈ Q) (a n : ℕ) (y : ZFSet.{u}) :
    (Formula.addition 3 4 1 2 0).Eval (cons y (cons (natSet a) (cons (natSet n)
      (cons ZFSet.omega (fun _ => Q))))) ↔ y = natSet (a+n) := by
  rw [Formula.eval_addition]
  simp only [cons_zero,cons_succ]
  constructor
  · rintro ⟨k,_,z,_,f,_,hf,hy⟩
    exact hf.correct a n hy
  · intro hy
    refine ⟨natSet (n+1),(mem_omega _).mpr ⟨n+1,rfl⟩,natSet 0,
      (mem_omega _).mpr ⟨0,rfl⟩,finiteNaturalGraph (fun i => a+i) n,hQ _ _,additionTrace_exists a
        n,?_⟩
    exact (finiteNaturalGraph_pair _ n n y).mpr ⟨le_rfl,hy⟩

end TuringRigidity.BoundedSetTheory

end OAI
