/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticParameterFormula.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticRelations
public import LeanPool.TuringConeRigidity.Computability.ArithmeticSetSyntax

/-!
# Arithmetic Parameter Formula
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open UniformArithmetic
universe u
namespace Formula

/-- Place arithmetic and oracle parameters in the variable slots of a bounded formula. -/
def oracleParameterVars (o Q n : ℕ) (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => n
  | 1 => o
  | 2 => Q
  | i+3 => r i

/-- Rename a bounded formula to use the supplied arithmetic and oracle parameter slots. -/
def oracleParameters (φ : Formula) (o Q n : ℕ) (r : ℕ → ℕ) : Formula :=
  φ.rename (oracleParameterVars o Q n r)

theorem oracleParameters_spec {φ : Formula} {P : Predicate} (hφ : DefinesArithmetic.{u} φ P)
    (o Q n : ℕ) (r : ℕ → ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (O : Oracles) (hO : ∀ i, e (r i) = realCode (O i)) (N : ℕ) (hn : e n = natSet N) :
    (oracleParameters φ o Q n r).Eval e ↔ P O N := by
  rw [oracleParameters,eval_rename]
  have he : (fun i => e (oracleParameterVars o Q n r i)) = arithmeticEnv (e Q) O N := by
    funext i
    rcases i with _ | i
    · exact hn
    rcases i with _ | i
    · exact ho
    rcases i with _ | i
    · rfl
    exact hO i
  rw [he]
  exact hφ _ hQ _ _

/-- Specialize an arithmetic formula to two oracle parameter slots. -/
def twoOracles (φ : Formula) (o Q n x y : ℕ) : Formula :=
  oracleParameters φ o Q n (fun i => if i = 0 then x else y)

theorem twoOracles_spec {φ : Formula} {P : Predicate} (hφ : DefinesArithmetic.{u} φ P)
    (o Q n x y : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (A B : Oracle) (hx : e x = realCode A) (hy : e y = realCode B)
    (N : ℕ) (hn : e n = natSet N) :
    (twoOracles φ o Q n x y).Eval e ↔ P (fun i => if i = 0 then A else B) N := by
  apply oracleParameters_spec hφ o Q n _ e ho hQ _ _ N hn
  intro i; by_cases hi : i = 0 <;> simp only [hi,ite_true,ite_false] <;> assumption
end Formula

theorem degree_equality_bounded : ∃ φ : Formula, ∀ o Q z x y : ℕ, ∀ e : ℕ → ZFSet.{u},
    e o = ZFSet.omega → (∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) →
    e z = natSet 0 → ∀ A B : Oracle, e x = realCode A → e y = realCode B →
      ((Formula.twoOracles φ o Q z x y).Eval e ↔ degree A = degree B) := by
  have hp := degree_equal_arith (parameter_arith 0) (parameter_arith 1)
  obtain ⟨φ,hφ⟩ := arithmetic_bounded_definition.{u} hp
  refine ⟨φ,?_⟩
  intro o Q z x y e ho hQ hz A B hx hy
  simpa using
    Formula.twoOracles_spec hφ o Q z x y e ho hQ A B hx hy 0 hz

end TuringRigidity.BoundedSetTheory

end OAI
