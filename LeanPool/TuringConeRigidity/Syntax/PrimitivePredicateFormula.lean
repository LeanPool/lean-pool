/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/PrimitivePredicateFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalPrimitiveGraph

/-!
# Primitive Predicate Formula
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

def DefinesPredicate (φ : Formula) (P : ℕ → Prop) : Prop :=
  ∀ e : ℕ → ZFSet.{u}, e 1 = ZFSet.omega →
    (∀ g : ℕ → ℕ, ∀ k, finiteNaturalGraph g k ∈ e 2) → ∀ n, e 0 = natSet n →
      (φ.Eval e ↔ P n)

def Formula.numericalPredicate (φ : Formula) : Formula := .existsMem 1
  (.conj (unary φ 2 3 1 0) (.neg (.empty 0)))

theorem primitive_predicate_bounded {P : ℕ → Prop} (hP : PrimrecPred P) :
    ∃ φ : Formula, DefinesPredicate.{u} φ P := by
  obtain ⟨inst,hP⟩ := hP
  let : DecidablePred P := inst
  let f := fun n => Encodable.encode (decide (P n))
  have hf : Nat.Primrec f := Primrec.nat_iff.mp (Primrec.encode.comp hP)
  obtain ⟨φ,hφ⟩ := primitive_bounded_definition.{u} hf
  refine ⟨φ.numericalPredicate,?_⟩
  intro e ho hQ n hn
  have hw (w : ZFSet.{u}) := Formula.unary_spec hφ 2 3 1 0 (cons w e) ho hQ n hn
  have htest : (natSet.{u} (f n) ≠ ∅) ↔ P n := by
    change (natSet.{u} (f n) ≠ natSet 0) ↔ P n
    rw [natSet_injective.ne_iff]
    dsimp [f]
    by_cases h : P n <;> simp [h]
  simp only [Formula.numericalPredicate,Formula.Eval,Formula.eval_empty,cons_zero]
  constructor
  · rintro ⟨w,_,hf',hne⟩
    obtain rfl := (hw w).mp hf'
    exact htest.mp hne
  · intro h
    refine ⟨natSet (f n),?_,(hw _).mpr rfl,htest.mpr h⟩
    rw [ho]; exact (mem_omega _).mpr ⟨f n,rfl⟩

end TuringRigidity.BoundedSetTheory

end OAI
