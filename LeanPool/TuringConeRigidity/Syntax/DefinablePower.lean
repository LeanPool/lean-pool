/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/DefinablePower.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ElementaryLanguage

/-!
# Definable Power
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

/-- Extend a finite tuple to an environment using the empty set outside its length. -/
noncomputable def tupleEnv {n : ℕ} (v : Fin n → ZFSet.{u}) (i : ℕ) : ZFSet.{u} :=
  if h : i < n then v ⟨i,h⟩ else ∅

theorem tupleEnv_lt {n : ℕ} (v : Fin n → ZFSet.{u}) (i : Fin n) :
    tupleEnv v i = v i := by simp [tupleEnv]

/-- The subset of `A` defined over `A` by the full formula with the supplied finite
parameters. -/
noncomputable def definedSubset (A : ZFSet.{u}) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) : ZFSet.{u} :=
  A.sep (fun x => p.Sat (A : Set ZFSet) (cons x (tupleEnv v)))

theorem mem_definedSubset (A x : ZFSet.{u}) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) :
    x ∈ definedSubset A p v ↔ x ∈ A ∧ p.Sat (A : Set ZFSet) (cons x (tupleEnv v)) :=
  ZFSet.mem_sep

/-- A subset is definable over `A` by a full formula with finitely many parameters in `A`. -/
def DefinableOver (A S : ZFSet.{u}) : Prop :=
  ∃ (n : ℕ) (p : SentenceForm) (v : Fin n → ZFSet.{u}),
    p.bound ≤ n + 1 ∧ (∀ i, v i ∈ A) ∧ S = definedSubset A p v

/-- The set of all subsets of `A` definable over `A` with finite parameters from `A`. -/
noncomputable def definablePower (A : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.powerset A).sep (DefinableOver A)

theorem definableOver_subset {A S : ZFSet.{u}} (h : DefinableOver A S) : S ⊆ A := by
  obtain ⟨n,p,v,_,_,rfl⟩ := h
  exact fun _ hx => (mem_definedSubset A _ p v).mp hx |>.1

theorem mem_definablePower (A S : ZFSet.{u}) :
    S ∈ definablePower A ↔ DefinableOver A S := by
  rw [definablePower,ZFSet.mem_sep]
  exact ⟨And.right,fun h => ⟨ZFSet.mem_powerset.mpr (definableOver_subset h),h⟩⟩

theorem subset_of_mem_definablePower {A S : ZFSet.{u}}
    (h : S ∈ definablePower A) : S ⊆ A :=
  definableOver_subset ((mem_definablePower A S).mp h)

theorem separation_mem_definablePower (A : ZFSet.{u}) (p : SentenceForm)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, i < p.bound → e i ∈ A) :
    A.sep (fun x => p.Sat (A : Set ZFSet) (cons x e)) ∈ definablePower A := by
  apply (mem_definablePower A _).mpr
  let v : Fin p.bound → ZFSet.{u} := fun i => e i
  refine ⟨p.bound,p,v,by omega,fun i => he i i.isLt,?_⟩
  apply ZFSet.ext; intro x
  rw [ZFSet.mem_sep,mem_definedSubset]
  apply and_congr_right; intro _
  apply p.finite_support
  intro i hi
  cases i with
  | zero => rfl
  | succ i =>
    change e i = tupleEnv v i
    simp [tupleEnv,v,show i < p.bound by omega]

theorem self_mem_definablePower (A : ZFSet.{u}) : A ∈ definablePower A := by
  apply (mem_definablePower A A).mpr
  refine ⟨0,.equal 0 0,Fin.elim0,by decide,fun i => Fin.elim0 i,?_⟩
  apply ZFSet.ext; intro x
  simp [mem_definedSubset,SentenceForm.Sat]

theorem subset_definablePower {A : ZFSet.{u}} (hA : Transitive A) : A ⊆ definablePower A := by
  intro S hS
  apply (mem_definablePower A S).mpr
  refine ⟨1,.member 0 1,fun _ => S,by decide,fun _ => hS,?_⟩
  apply ZFSet.ext; intro x
  simp only [mem_definedSubset,SentenceForm.Sat,cons_zero,cons_succ]
  simp only [tupleEnv,show 0 < 1 by decide,dite_eq_left]
  exact ⟨fun hx => ⟨hA S hS x hx,hx⟩,And.right⟩

theorem definablePower_transitive {A : ZFSet.{u}} (hA : Transitive A) :
    Transitive (definablePower A) := by
  intro S hS x hx
  exact subset_definablePower hA (subset_of_mem_definablePower hS hx)

end TuringRigidity.RelativeConstructible

end OAI
