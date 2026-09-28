/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Engine.AD.Basic
public import LeanPool.MovingSofa.LeanCert.Engine.AD.Transcendental
/-!
# Automatic Differentiation - Evaluators

This file provides the evaluation functions for automatic differentiation,
mapping expressions to dual intervals.

## Main definitions

* `DualEnv` - Environment mapping variable indices to dual intervals
* `LeanCert.Internal.AD.evalUnchecked` - Main evaluator for supported expressions (total)
* `evalDual?` - Partial evaluator supporting domain-checked functions (returns Option)
* `evalDual?1` - Single-variable version of evalDual?
* `mkDualEnv` - Create a dual environment for differentiation w.r.t. a variable
* `evalWithDeriv` - Evaluate and differentiate w.r.t. a variable index
* `derivInterval` - Get just the derivative interval
* `evalWithDeriv1` - Single-variable evaluation and differentiation
-/

/-! ### Dual evaluation -/

@[expose] public section

namespace LeanCert.Engine

open LeanCert.Core

/-- Environment for dual evaluation -/
abbrev DualEnv := Nat → DualInterval

end LeanCert.Engine

namespace LeanCert.Internal.AD

open LeanCert.Core LeanCert.Engine

/-- Evaluate expression in dual interval mode.

    For supported expressions (const, var, add, mul, neg, sin, cos, exp), this
    computes correct dual interval bounds with a fully-verified proof.

    For unsupported expressions (inv, log), returns a default interval.
    Do not rely on results for expressions containing inv or log.
    Use evalDual? for partial functions like inv and log. -/
noncomputable def evalUnchecked (e : Expr) (ρ : DualEnv) : DualInterval :=
  match e with
  | Expr.const q => DualInterval.const q
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ => DualInterval.add (LeanCert.Internal.AD.evalUnchecked e₁ ρ)
    (LeanCert.Internal.AD.evalUnchecked e₂ ρ)
  | Expr.mul e₁ e₂ => DualInterval.mul (LeanCert.Internal.AD.evalUnchecked e₁ ρ)
    (LeanCert.Internal.AD.evalUnchecked e₂ ρ)
  | Expr.neg e => DualInterval.neg (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.inv _ => default  -- Not in ADSupported; safe default
  | Expr.exp e => DualInterval.exp (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.sin e => DualInterval.sin (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.cos e => DualInterval.cos (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.log _ => default  -- Not in ADSupported; use evalDual? for log
  | Expr.atan e => DualInterval.atan (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.arsinh e => DualInterval.arsinh (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.atanh _ => default  -- Partial function; use evalDual? for atanh
  | Expr.sinc e => DualInterval.sinc (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.erf e => DualInterval.erf (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.sinh e => DualInterval.sinh (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.cosh e => DualInterval.cosh (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.tanh e => DualInterval.tanh (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.sqrt e => DualInterval.sqrt (LeanCert.Internal.AD.evalUnchecked e ρ)
  | Expr.namedConst c => DualInterval.ofMathConst c

end LeanCert.Internal.AD

namespace LeanCert.Engine

open LeanCert.Core

/-! ### Partial dual evaluation -/

/-- Partial dual evaluator that supports domain-checked functions.
    Returns `none` if any domain error would occur:
    - inv of an interval containing zero
    - log of an interval not strictly positive
    When it returns `some`, the result is guaranteed to be correct.

    The total and computable dual evaluators support `tanh`, but this
    Option-returning evaluator deliberately keeps `tanh` disabled until the
    `evalDual?`-specific value/differentiability/derivative correctness path
    is wired for that constructor. -/
noncomputable def evalDual? (e : Expr) (ρ : DualEnv) : Option DualInterval :=
  match e with
  | Expr.const q => some (DualInterval.const q)
  | Expr.var idx => some (ρ idx)
  | Expr.add e₁ e₂ =>
      match evalDual? e₁ ρ, evalDual? e₂ ρ with
      | some d₁, some d₂ => some (DualInterval.add d₁ d₂)
      | _, _ => none
  | Expr.mul e₁ e₂ =>
      match evalDual? e₁ ρ, evalDual? e₂ ρ with
      | some d₁, some d₂ => some (DualInterval.mul d₁ d₂)
      | _, _ => none
  | Expr.neg e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.neg d)
      | none => none
  | Expr.inv e₁ =>
      match evalDual? e₁ ρ with
      | none => none
      | some d => DualInterval.inv? d
  | Expr.exp e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.exp d)
      | none => none
  | Expr.sin e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.sin d)
      | none => none
  | Expr.cos e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.cos d)
      | none => none
  | Expr.log e =>
      match evalDual? e ρ with
      | none => none
      | some d => DualInterval.log? d
  | Expr.atan e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.atan d)
      | none => none
  | Expr.arsinh e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.arsinh d)
      | none => none
  | Expr.atanh _ =>
      -- atanh is partial (defined only for |x| < 1) and requires complex bounds
      -- We return none to avoid the complexity of proving atanh bounds
      none
  | Expr.sinc e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.sinc d)
      | none => none
  | Expr.erf e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.erf d)
      | none => none
  | Expr.sinh e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.sinh d)
      | none => none
  | Expr.cosh e =>
      match evalDual? e ρ with
      | some d => some (DualInterval.cosh d)
      | none => none
  | Expr.tanh _ =>
      -- See the docstring above:
      -- `LeanCert.Internal.AD.evalUnchecked`/`LeanCert.Internal.AD.evalTotalCore` support tanh, but
      -- the partial `evalDual?` correctness theorem currently treats tanh as
      -- outside this Option API.
      none
  | Expr.sqrt e =>
      match evalDual? e ρ with
      | some d => DualInterval.sqrt? d
      | none => none
  | Expr.namedConst c => some (DualInterval.ofMathConst c)

/-- Single-variable version of evalDual? -/
noncomputable def evalDual?1 (e : Expr) (I : IntervalRat) : Option DualInterval :=
  evalDual? e (fun _ => DualInterval.varActive I)

/-! ### Single variable differentiation -/

/-- Create dual environment for differentiating with respect to variable `idx` -/
def mkDualEnv (ρ : IntervalEnv) (idx : Nat) : DualEnv :=
  fun i => if i = idx then DualInterval.varActive (ρ i) else DualInterval.varPassive (ρ i)

/-- Evaluate and differentiate with respect to variable `idx` -/
noncomputable def evalWithDeriv (e : Expr) (ρ : IntervalEnv) (idx : Nat) : DualInterval :=
  LeanCert.Internal.AD.evalUnchecked e (mkDualEnv ρ idx)

/-- Get just the derivative interval -/
noncomputable def derivInterval (e : Expr) (ρ : IntervalEnv) (idx : Nat) : IntervalRat :=
  (evalWithDeriv e ρ idx).der

/-- Evaluate and differentiate a single-variable expression -/
noncomputable def evalWithDeriv1 (e : Expr) (I : IntervalRat) : DualInterval :=
  LeanCert.Internal.AD.evalUnchecked e (fun _ => DualInterval.varActive I)

end LeanCert.Engine
