/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticSetSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.PrimitivePredicateFormula
public import LeanPool.TuringConeRigidity.SetModels.ModelReals
public import LeanPool.TuringConeRigidity.Computability.UniformArithmetic

/-!
# Arithmetic Set Syntax
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open UniformArithmetic
universe u

/-- Set-theoretic environment containing the input numeral, omega, finite-graph bound, and
oracle codes. -/
noncomputable def arithmeticEnv (Q : ZFSet.{u}) (O : Oracles) (n : ℕ) : ℕ → ZFSet.{u} :=
  cons (natSet n) (cons ZFSet.omega (cons Q (fun i => realCode (O i))))

/-- A bounded formula defines the arithmetic predicate for every sufficient finite-graph
bound. -/
def DefinesArithmetic (φ : Formula) (P : Predicate) : Prop :=
  ∀ Q : ZFSet.{u}, (∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ Q) → ∀ O n,
    (φ.Eval (arithmeticEnv Q O n) ↔ P O n)

namespace Formula
/-- Shift oracle parameter slots while keeping the distinguished arithmetic input slot fixed. -/
def arithmeticVars (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => i+k+1

theorem eval_arithmetic_shift_one (φ : Formula) (Q : ZFSet.{u}) (O : Oracles) (n m : ℕ) :
    (φ.rename (arithmeticVars 1)).Eval (cons (natSet m) (arithmeticEnv Q O n)) ↔
      φ.Eval (arithmeticEnv Q O m) := by
  rw [eval_rename]
  have he : (fun i => cons (natSet m) (arithmeticEnv Q O n) (arithmeticVars 1 i)) = arithmeticEnv
    Q O m := by
    funext i; cases i <;> rfl
  rw [he]

theorem eval_arithmetic_shift_two (φ : Formula) (Q : ZFSet.{u}) (O : Oracles) (n k m : ℕ) :
    (φ.rename (arithmeticVars 2)).Eval (cons (natSet m) (cons (natSet k) (arithmeticEnv Q O n))) ↔
      φ.Eval (arithmeticEnv Q O m) := by
  rw [eval_rename]
  have he : (fun i => cons (natSet m) (cons (natSet k) (arithmeticEnv Q O n)) (arithmeticVars 2
    i)) =
      arithmeticEnv Q O m := by
    funext i; cases i <;> rfl
  rw [he]

/-- Bounded formula implementing existential number quantification through natural-pair
coding. -/
def arithmeticExists (φ : Formula) : Formula := .existsMem 1 (.existsMem 2
  (.conj (naturalPair 3 4 2 1 0) (φ.rename (arithmeticVars 2))))

/-- Bounded formula composing two arithmetic definitions through an existential intermediate
value. -/
def arithmeticComp (φ ψ : Formula) : Formula := .existsMem 1
  (.conj (unary ψ 2 3 1 0) (φ.rename (arithmeticVars 1)))
end Formula

theorem DefinesArithmetic.existsNat {φ : Formula} {P : Predicate} (hφ : DefinesArithmetic.{u} φ P) :
    DefinesArithmetic.{u} φ.arithmeticExists (fun O n => ∃ k, P O (Nat.pair n k)) := by
  intro Q hQ O n
  have hp (k : ℕ) (w : ZFSet.{u}) := Formula.naturalPair_spec 3 4 2 1 0
    (cons w (cons (natSet k) (arithmeticEnv Q O n))) rfl hQ n k rfl rfl
  simp only [Formula.arithmeticExists,Formula.Eval,arithmeticEnv,cons_zero,cons_succ]
  constructor
  · rintro ⟨x,hx,w,_,hpair,h⟩
    obtain ⟨k,rfl⟩ := (mem_omega x).mp hx
    obtain rfl := (hp k w).mp hpair
    exact ⟨k,(hφ Q hQ O _).mp ((Formula.eval_arithmetic_shift_two φ Q O n k _).mp h)⟩
  · rintro ⟨k,h⟩
    exact ⟨natSet k,(mem_omega _).mpr ⟨k,rfl⟩,natSet (Nat.pair n k),
      (mem_omega _).mpr ⟨Nat.pair n k,rfl⟩,(hp k _).mpr rfl,
      (Formula.eval_arithmetic_shift_two φ Q O n k _).mpr ((hφ Q hQ O _).mpr h)⟩

theorem DefinesArithmetic.comp {φ ψ : Formula} {P : Predicate} {f : ℕ → ℕ}
    (hφ : DefinesArithmetic.{u} φ P) (hψ : DefinesNatural.{u} ψ f) :
    DefinesArithmetic.{u} (φ.arithmeticComp ψ) (fun O n => P O (f n)) := by
  intro Q hQ O n
  have hf (w : ZFSet.{u}) := Formula.unary_spec hψ 2 3 1 0
    (cons w (arithmeticEnv Q O n)) rfl hQ n rfl
  simp only [Formula.arithmeticComp,Formula.Eval,arithmeticEnv,cons_zero,cons_succ]
  constructor
  · rintro ⟨w,_,hw,h⟩
    obtain rfl := (hf w).mp hw
    exact (hφ Q hQ O _).mp ((Formula.eval_arithmetic_shift_one φ Q O n _).mp h)
  · intro h
    exact ⟨natSet (f n),(mem_omega _).mpr ⟨f n,rfl⟩,(hf _).mpr rfl,
      (Formula.eval_arithmetic_shift_one φ Q O n _).mpr ((hφ Q hQ O _).mpr h)⟩

theorem arithmetic_bounded_definition {P : Predicate} (hP : Arith P) :
    ∃ φ : Formula, DefinesArithmetic.{u} φ P := by
  induction hP with
  | pure P hP =>
    obtain ⟨φ,hφ⟩ := primitive_predicate_bounded.{u} hP
    exact ⟨φ,fun Q hQ O n => hφ (arithmeticEnv Q O n) rfl hQ n rfl⟩
  | query i =>
    exact ⟨.member 0 (i+3),fun Q _ O n => natSet_mem_realCode (O i) n⟩
  | neg h ih =>
    obtain ⟨φ,hφ⟩ := ih
    exact ⟨.neg φ,fun Q hQ O n => not_congr (hφ Q hQ O n)⟩
  | and h k ih ik =>
    obtain ⟨φ,hφ⟩ := ih; obtain ⟨ψ,hψ⟩ := ik
    exact ⟨.conj φ ψ,fun Q hQ O n => and_congr (hφ Q hQ O n) (hψ Q hQ O n)⟩
  | ex h ih =>
    obtain ⟨φ,hφ⟩ := ih
    exact ⟨φ.arithmeticExists,hφ.existsNat⟩
  | comp f h hf ih =>
    obtain ⟨φ,hφ⟩ := ih
    obtain ⟨ψ,hψ⟩ := primitive_bounded_definition.{u} (Primrec.nat_iff.mp hf)
    exact ⟨φ.arithmeticComp ψ,hφ.comp hψ⟩

end TuringRigidity.BoundedSetTheory

end OAI
