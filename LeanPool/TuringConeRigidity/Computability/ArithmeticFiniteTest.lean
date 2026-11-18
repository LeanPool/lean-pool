/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticFiniteTest.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.UniformArithmetic

/-!
# Arithmetic Finite Test
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic

/-- Arithmetic terms with primitive-recursive operations and queries to a numerical witness
function. -/
inductive Term where
  | input : Term
  | const : ℕ → Term
  | prim (f : ℕ → ℕ) (hf : Primrec f) : Term → Term
  | pair : Term → Term → Term
  | witness : Term → Term

namespace Term

/-- Evaluate a term with the given input and witness function. -/
def eval (O : ℕ → ℕ) (v : ℕ) : Term → ℕ
  | .input => v
  | .const n => n
  | .prim f _ t => f (t.eval O v)
  | .pair t s => Nat.pair (t.eval O v) (s.eval O v)
  | .witness t => O (t.eval O v)

/-- Apply the primitive-recursive left projection of natural-number pairing to a term. -/
def left (t : Term) : Term := .prim UniformArithmetic.left left_primrec t
/-- Apply the primitive-recursive right projection of natural-number pairing to a term. -/
def right (t : Term) : Term := .prim UniformArithmetic.right right_primrec t

/-- Substitute the input term and transform witness queries throughout a term. -/
def subst (t : Term) (inputTerm : Term) (query : Term → Term) : Term :=
  match t with
  | .input => inputTerm
  | .const n => .const n
  | .prim f hf t => .prim f hf (t.subst inputTerm query)
  | .pair t s => .pair (t.subst inputTerm query) (s.subst inputTerm query)
  | .witness t => query (t.subst inputTerm query)

theorem eval_subst (t inputTerm : Term) (query : Term → Term)
    (f g : ℕ → ℕ) (v : ℕ)
    (hq : ∀ t, (query t).eval f v = g (t.eval f v)) :
    (t.subst inputTerm query).eval f v = t.eval g (inputTerm.eval f v) := by
  induction t with
  | input => rfl
  | const n => rfl
  | prim f hf t ih => simp only [subst,eval,ih]
  | pair t s ih ik => simp only [subst,eval,ih,ik]
  | witness t ih => simp only [subst,eval,hq,ih]
end Term

/-- Finite arithmetic tests using primitive-recursive predicates, oracle queries, negation,
and conjunction. -/
inductive Test where
  | pure (P : ℕ → Prop) (hP : PrimrecPred P) : Term → Test
  | query : ℕ → Term → Test
  | neg : Test → Test
  | and : Test → Test → Test

namespace Test

/-- Interpret an arithmetic test using its oracles, witness function, and input. -/
def eval (O : Oracles) (f : ℕ → ℕ) (v : ℕ) : Test → Prop
  | .pure P _ t => P (t.eval f v)
  | .query i t => O i (t.eval f v) = true
  | .neg t => ¬ t.eval O f v
  | .and t s => t.eval O f v ∧ s.eval O f v

/-- Substitute input and witness-query terms throughout an arithmetic test. -/
def subst (inputTerm : Term) (query : Term → Term) : Test → Test
  | .pure P hP t => .pure P hP (t.subst inputTerm query)
  | .query i t => .query i (t.subst inputTerm query)
  | .neg t => .neg (t.subst inputTerm query)
  | .and t s => .and (t.subst inputTerm query) (s.subst inputTerm query)

theorem eval_subst (t : Test) (inputTerm : Term) (query : Term → Term)
    (O : Oracles) (f g : ℕ → ℕ) (v : ℕ)
    (hq : ∀ t, (query t).eval f v = g (t.eval f v)) :
    (t.subst inputTerm query).eval O f v ↔ t.eval O g (inputTerm.eval f v) := by
  induction t with
  | pure P hP t => simp only [subst,eval,Term.eval_subst t inputTerm query f g v hq]
  | query i t => simp only [subst,eval,Term.eval_subst t inputTerm query f g v hq]
  | neg t ih => exact not_congr ih
  | and t s ih ik => exact and_congr ih ik

/-- Disjunction of two tests, expressed using negation and conjunction. -/
def or (t s : Test) : Test := .neg (.and (.neg t) (.neg s))

@[simp] theorem eval_or (t s : Test) (O : Oracles) (f : ℕ → ℕ) (v : ℕ) :
    (t.or s).eval O f v ↔ t.eval O f v ∨ s.eval O f v := by
  classical
  change (¬ (¬ t.eval O f v ∧ ¬ s.eval O f v)) ↔ _
  tauto

/-- The test presents a predicate by existence of a numerical witness satisfying every
numbered test. -/
def Presents (t : Test) (P : Predicate) : Prop :=
  ∀ O v, P O v ↔ ∃ f : ℕ → ℕ, ∀ n, t.eval O f (Nat.pair v n)
end Test

end TuringRigidity.ArithmeticTree

end OAI
