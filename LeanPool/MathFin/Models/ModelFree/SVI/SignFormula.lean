/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.ParameterPolynomials

/-! # Sign formulas and sign programs

Part of the SVI polynomial-sign certificate (#174).

`SignFormula` is a finite negation-free combination (and, or, constants) of atoms "the polynomial
`f` in the parameters has sign `s`". `SignProgram α` is a finite decision tree branching three ways
on such signs, with leaves in `α`; a Boolean program expands to a formula with the same value.

## Main definitions

* `SignFormula`: a finite combination (and, or, constants) of atoms "the parameter polynomial `f`
  has sign `s`".
* `SignFormula.eval`: the truth value of a sign formula at the parameters `p`.
* `SignProgram α`: a finite decision tree that branches on signs of parameter polynomials, with
  leaves in `α`.
* `SignProgram.bind`, `SignProgram.eval`: sequencing, and the result of running a program at `p`.
* `SignProgram.toFormula`: the sign formula with the same value as a Boolean sign program.
* `signQuery`, `signListProgram`: the programs returning the sign of one parameter polynomial and
  the signs of a list of them.

## Main results

* `SignProgram.eval_bind`: `(s.bind k).eval p = (k (s.eval p)).eval p`.
* `SignProgram.eval_toFormula`: `s.toFormula.eval p = s.eval p` for a Boolean program `s`.
* `signQuery_eval`, `signListProgram_eval`: the programs evaluate to the signs of
  `parameterEval p f`.

## Tags

sign formula, decision tree, sign program, semialgebraic condition, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI

/-- A literal finite Boolean combination of parameter-polynomial sign atoms. -/
inductive SignFormula where
  | truth : Bool → SignFormula
  | atom : ParameterRing → SignType → SignFormula
  | and : SignFormula → SignFormula → SignFormula
  | or : SignFormula → SignFormula → SignFormula

/-- The truth value of a sign formula at the parameters `p`. -/
noncomputable def SignFormula.eval (p : Params) : SignFormula → Bool
  | .truth b => b
  | .atom f s => decide (SignType.sign (parameterEval p f) = s)
  | .and f g => f.eval p && g.eval p
  | .or f g => f.eval p || g.eval p

/-- A finite decision tree asking only signs of explicit parameter polynomials. -/
inductive SignProgram (α : Type*) where
  | pure : α → SignProgram α
  | query : ParameterRing → SignProgram α → SignProgram α → SignProgram α → SignProgram α

/-- Sequencing of sign programs. -/
def SignProgram.bind {α β : Type*} : SignProgram α → (α → SignProgram β) → SignProgram β
  | .pure a, k => k a
  | .query f neg zero pos, k => .query f (neg.bind k) (zero.bind k) (pos.bind k)

/-- The result of running a sign program at the parameters `p`. -/
noncomputable def SignProgram.eval {α : Type*} (p : Params) : SignProgram α → α
  | .pure a => a
  | .query f neg zero pos => match SignType.sign (parameterEval p f) with
    | .neg => neg.eval p
    | .zero => zero.eval p
    | .pos => pos.eval p

@[simp] theorem SignProgram.eval_bind {α β : Type*} (p : Params) (s : SignProgram α)
    (k : α → SignProgram β) : (s.bind k).eval p = (k (s.eval p)).eval p := by
  induction s with
  | pure a => rfl
  | query f neg zero pos hn hz hp =>
    simp only [bind, eval]
    cases SignType.sign (parameterEval p f) <;> simp_all

/-- The sign formula with the same value as a Boolean sign program (`SignProgram.eval_toFormula`).
-/
def SignProgram.toFormula : SignProgram Bool → SignFormula
  | .pure b => .truth b
  | .query f neg zero pos =>
    .or (.and (.atom f .neg) neg.toFormula)
      (.or (.and (.atom f .zero) zero.toFormula) (.and (.atom f .pos) pos.toFormula))

@[simp] theorem SignProgram.eval_toFormula (p : Params) (s : SignProgram Bool) :
    s.toFormula.eval p = s.eval p := by
  induction s with
  | pure b => rfl
  | query f neg zero pos hn hz hp =>
    simp only [toFormula, SignFormula.eval, eval]
    cases SignType.sign (parameterEval p f) <;> simp_all

/-- The program returning the sign of `f`. -/
def signQuery (f : ParameterRing) : SignProgram SignType :=
  .query f (.pure .neg) (.pure .zero) (.pure .pos)

@[simp] theorem signQuery_eval (p : Params) (f : ParameterRing) :
    (signQuery f).eval p = SignType.sign (parameterEval p f) := by
  simp only [signQuery, SignProgram.eval]
  cases SignType.sign (parameterEval p f) <;> rfl

/-- The program returning the signs of a list of parameter polynomials. -/
def signListProgram : List ParameterRing → SignProgram (List SignType)
  | [] => .pure []
  | f :: fs => (signQuery f).bind fun s ↦ (signListProgram fs).bind fun ss ↦ .pure (s :: ss)

@[simp] theorem signListProgram_eval (p : Params) (fs : List ParameterRing) :
    (signListProgram fs).eval p = fs.map (fun f ↦ SignType.sign (parameterEval p f)) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [signListProgram, SignProgram.eval_bind, ih, SignProgram.eval]

end SVI
end MathFin
