/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/CanonicalAdditionSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelPairing
public import LeanPool.TuringConeRigidity.SetModels.UnionIteration

/-!
# Canonical Addition Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel SetModelArithmetic SetModelIteration
universe u

/-- A set-coded function satisfying the zero and successor recursion equations for addition. -/
def AdditionSystem (w d A : ZFSet.{u}) : Prop :=
  TransitiveNameModel.FunctionGraph d w A ∧
  (∃ z ∈ w, z = ∅ ∧ ∀ x ∈ w, ZFSet.pair (ZFSet.pair x z) x ∈ A) ∧
  ∀ x ∈ w, ∀ y ∈ w, ∀ v ∈ w,
    ZFSet.pair (ZFSet.pair x y) v ∈ A →
    ∀ y' ∈ w, ∀ v' ∈ w, y' = insert y y → v' = insert v v →
      ZFSet.pair (ZFSet.pair x y') v' ∈ A

theorem additionSet_members (z : ZFSet.{u}) :
    z ∈ additionSet ↔ ∃ n m, z = ZFSet.pair (ZFSet.pair (natSet n) (natSet m)) (natSet (n+m)) := by
  rw [additionSet,mem_iterationSet setSucc setSucc_omega]
  constructor
  · rintro ⟨n,x,hx,hz⟩
    obtain ⟨m,rfl⟩ := (mem_omega x).mp hx
    exact ⟨n,m,by simpa only [iterate_setSucc,Nat.add_comm] using hz⟩
  · rintro ⟨n,m,rfl⟩
    exact ⟨n,natSet m,(mem_omega _).mpr ⟨m,rfl⟩,by rw [iterate_setSucc,Nat.add_comm]⟩

theorem additionSet_function : TransitiveNameModel.FunctionGraph pairNumbers.{u} ZFSet.omega
  additionSet := by
  constructor
  · intro z hz
    obtain ⟨n,m,rfl⟩ := (additionSet_members z).mp hz
    exact ⟨_,natPair_mem n m,_,(mem_omega _).mpr ⟨n+m,rfl⟩,rfl⟩
  · intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain ⟨n,rfl⟩ := (mem_omega a).mp ha
    obtain ⟨m,rfl⟩ := (mem_omega b).mp hb
    refine ⟨natSet (n+m),(mem_omega _).mpr ⟨n+m,rfl⟩,(addition_code n m _).mpr rfl,?_⟩
    intro z hz hpair
    obtain ⟨k,rfl⟩ := (mem_omega z).mp hz
    exact congrArg natSet ((addition_code n m k).mp hpair)

theorem additionSystem_canonical : AdditionSystem ZFSet.omega pairNumbers.{u} additionSet := by
  refine ⟨additionSet_function,⟨natSet 0,(mem_omega _).mpr ⟨0,rfl⟩,rfl,?_⟩,?_⟩
  · intro x hx
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact (addition_code n 0 n).mpr (Nat.add_zero n).symm
  · intro x hx y hy v hv hp y' _ v' _ hy' hv'
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    obtain ⟨m,rfl⟩ := (mem_omega y).mp hy
    obtain ⟨k,rfl⟩ := (mem_omega v).mp hv
    subst y'; subst v'
    change ZFSet.pair (ZFSet.pair (natSet n) (natSet (m+1))) (natSet (k+1)) ∈ additionSet
    exact (addition_code n (m+1) (k+1)).mpr (by have hk := (addition_code n m k).mp hp; omega)

theorem AdditionSystem.exact {A : ZFSet.{u}} (h : AdditionSystem ZFSet.omega pairNumbers A) :
    A = additionSet := by
  have hn (n : ℕ) : natSet.{u} n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
  have computes (n m : ℕ) : ZFSet.pair (ZFSet.pair (natSet n) (natSet m)) (natSet (n+m)) ∈ A := by
    induction m with
    | zero =>
      obtain ⟨z,_,rfl,hzero⟩ := h.2.1
      simpa only [Nat.add_zero,natSet] using hzero _ (hn n)
    | succ m ih =>
      have hs := h.2.2 _ (hn n) _ (hn m) _ (hn (n+m)) ih _ (hn (m+1)) _ (hn (n+m+1)) rfl rfl
      simpa only [Nat.add_succ] using hs
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := h.1.1 z hz
    obtain ⟨a,ha,b,hb,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain ⟨n,rfl⟩ := (mem_omega a).mp ha
    obtain ⟨m,rfl⟩ := (mem_omega b).mp hb
    have eq := h.1.functional (natPair_mem n m) hz (computes n m)
    rw [eq]
    exact (addition_code n m _).mpr rfl
  · intro hz
    obtain ⟨n,m,rfl⟩ := (additionSet_members z).mp hz
    exact computes n m

/-- Bounded formula expressing the addition-system recursion equations. -/
def additionSystemFormula (w d A : ℕ) : Formula :=
  .conj (.functionGraph A d w)
    (.conj (.existsMem w (.conj (.empty 0)
      (.allMem (w+1) (tripleFormula 0 1 0 (A+2) (d+2)))))
      (.allMem w (.allMem (w+1) (.allMem (w+2)
        (.imp (tripleFormula 2 1 0 (A+3) (d+3))
          (.allMem (w+3) (.allMem (w+4)
            (.imp (.successor 1 3) (.imp (.successor 0 2)
              (tripleFormula 4 1 0 (A+5) (d+5)))))))))))

theorem additionSystemFormula_spec (w d A : ℕ) (e : ℕ → ZFSet.{u})
    (hd : e d = ZFSet.prod (e w) (e w)) :
    (additionSystemFormula w d A).Eval e ↔ AdditionSystem (e w) (e d) (e A) := by
  simp only [additionSystemFormula,AdditionSystem,Formula.Eval,Formula.eval_functionGraph,
    Formula.eval_empty,Formula.eval_allMem,Formula.eval_imp,Formula.eval_successor,
    eval_tripleFormula,cons_zero,cons_succ]
  simp only [hd,ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨hf,⟨z,hz,he,hzero⟩,hstep⟩
    exact ⟨hf,⟨z,hz,he,fun x hx => (hzero x hx).2⟩,
      fun x hx y hy v hv hp y' hy' v' hv' hys hvs =>
        (hstep x hx y hy v hv ⟨⟨hx,hy⟩,hp⟩ y' hy' v' hv' hys hvs).2⟩
  · rintro ⟨hf,⟨z,hz,he,hzero⟩,hstep⟩
    exact ⟨hf,⟨z,hz,he,fun x hx => ⟨⟨hx,hz⟩,hzero x hx⟩⟩,
      fun x hx y hy v hv hp y' hy' v' hv' hys hvs =>
        ⟨⟨hx,hy'⟩,hstep x hx y hy v hv hp.2 y' hy' v' hv' hys hvs⟩⟩

theorem additionSystemFormula_unique (w d A : ℕ) (e : ℕ → ZFSet.{u})
    (hw : e w = ZFSet.omega) (hd : e d = pairNumbers) :
    (additionSystemFormula w d A).Eval e ↔ e A = additionSet := by
  rw [additionSystemFormula_spec w d A e (by rw [hd,hw]; rfl),hw,hd]
  exact ⟨AdditionSystem.exact,fun h => h ▸ additionSystem_canonical⟩

end TuringRigidity.RelativeConstructible

end OAI
