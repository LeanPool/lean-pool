/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Core.Expr
/-!
# Expression Support Predicates

This file defines predicates indicating which expressions are supported by
different interval evaluation strategies.

## Main definitions

* `ExprSupportedCore` - Predicate for expressions in the computable subset
  (const, var, add, mul, neg, sin, cos, exp, log, sqrt, sinh, cosh, tanh, erf, pi)

* `ADSupported` - Predicate for the noncomputable AD subset
  (const, var, add, mul, neg, sin, cos, exp)

## Design notes

`ADSupported` is the differentiable fragment used by automatic
differentiation. It is contained in `ExprSupportedCore` via
`ADSupported.toCore`. Checked evaluators accept arbitrary expressions and
encode domain failure in their result type, so they need no syntactic support
predicate.

The core subset is kept computable so that tactics can use `native_decide`
for interval bound checking. The extended subset uses `Real.exp` with
floor/ceil bounds, which requires noncomputability.
-/

/-! ### Core supported expression subset (computable) -/

@[expose] public section

namespace LeanCert.Core

open LeanCert.Core

/-- Predicate indicating an expression is in the computable core subset.
    Supports: const, var, add, mul, neg, sin, cos, exp, log, sqrt, sinh, cosh, tanh, erf, pi

    Note: log requires positive domain for correctness. The correctness theorem
    `evalIntervalCore_correct` has an additional hypothesis `evalDomainValid`
    that ensures log arguments evaluate to positive intervals. -/
inductive ExprSupportedCore : Expr → Prop where
  | const (q : ℚ) : ExprSupportedCore (Expr.const q)
  | var (idx : Nat) : ExprSupportedCore (Expr.var idx)
  | add {e₁ e₂ : Expr} : ExprSupportedCore e₁ → ExprSupportedCore e₂ →
      ExprSupportedCore (Expr.add e₁ e₂)
  | mul {e₁ e₂ : Expr} : ExprSupportedCore e₁ → ExprSupportedCore e₂ →
      ExprSupportedCore (Expr.mul e₁ e₂)
  | neg {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.neg e)
  | sin {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.sin e)
  | cos {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.cos e)
  | exp {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.exp e)
  | log {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.log e)
  | sqrt {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.sqrt e)
  | sinh {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.sinh e)
  | cosh {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.cosh e)
  | tanh {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.tanh e)
  | erf {e : Expr} : ExprSupportedCore e → ExprSupportedCore (Expr.erf e)
  | namedConst (c : MathConst) : ExprSupportedCore (Expr.namedConst c)

/-! ### Extended supported expression subset (with exp) -/

/-- Predicate indicating an expression is in the fully-verified subset for AD.
    Supports: const, var, add, mul, neg, sin, cos, exp
    Does NOT support:
    - sqrt (not differentiable at 0 - use ExprSupportedCore for interval evaluation only)
    - inv (requires nonzero interval checks)
    - log (requires positive interval checks)
    - atan/arsinh/atanh (derivative proofs incomplete in the total AD evaluator) -/
inductive ADSupported : Expr → Prop where
  | const (q : ℚ) : ADSupported (Expr.const q)
  | var (idx : Nat) : ADSupported (Expr.var idx)
  | add {e₁ e₂ : Expr} : ADSupported e₁ → ADSupported e₂ → ADSupported (Expr.add e₁ e₂)
  | mul {e₁ e₂ : Expr} : ADSupported e₁ → ADSupported e₂ → ADSupported (Expr.mul e₁ e₂)
  | neg {e : Expr} : ADSupported e → ADSupported (Expr.neg e)
  | sin {e : Expr} : ADSupported e → ADSupported (Expr.sin e)
  | cos {e : Expr} : ADSupported e → ADSupported (Expr.cos e)
  | exp {e : Expr} : ADSupported e → ADSupported (Expr.exp e)

/-- ADSupported expressions are also in ExprSupportedCore -/
theorem ADSupported.toCore {e : Expr} (h : ADSupported e) : ExprSupportedCore e := by
  induction h with
  | const q => exact ExprSupportedCore.const q
  | var idx => exact ExprSupportedCore.var idx
  | add _ _ ih₁ ih₂ => exact ExprSupportedCore.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact ExprSupportedCore.mul ih₁ ih₂
  | neg _ ih => exact ExprSupportedCore.neg ih
  | sin _ ih => exact ExprSupportedCore.sin ih
  | cos _ ih => exact ExprSupportedCore.cos ih
  | exp _ ih => exact ExprSupportedCore.exp ih

/-- Computable recognition of the differentiable `ADSupported` subset used
by Newton/AD backends. -/
def Expr.checkADSupported : Expr → Bool
  | .const _ | .var _ => true
  | .add e₁ e₂ | .mul e₁ e₂ => e₁.checkADSupported && e₂.checkADSupported
  | .neg e | .exp e | .sin e | .cos e => e.checkADSupported
  | _ => false

/-- The executable support check recognizes exactly the differentiable
`ADSupported` fragment used by the checked AD/monotonicity backend. -/
theorem Expr.checkADSupported_eq_true_iff (e : Expr) :
    e.checkADSupported = true ↔ ADSupported e := by
  induction e with
  | const q => simp [Expr.checkADSupported, ADSupported.const]
  | var i => simp [Expr.checkADSupported, ADSupported.var]
  | add e₁ e₂ ih₁ ih₂ =>
      simp only [Expr.checkADSupported, Bool.and_eq_true, ih₁, ih₂]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact .add h₁ h₂
      · intro h
        cases h
        exact ⟨by assumption, by assumption⟩
  | mul e₁ e₂ ih₁ ih₂ =>
      simp only [Expr.checkADSupported, Bool.and_eq_true, ih₁, ih₂]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact .mul h₁ h₂
      · intro h
        cases h
        exact ⟨by assumption, by assumption⟩
  | neg e ih | exp e ih | sin e ih | cos e ih =>
      simp only [Expr.checkADSupported, ih]
      constructor
      · intro h
        first | exact .neg h | exact .exp h | exact .sin h | exact .cos h
      · intro h
        cases h
        assumption
  | inv e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | log e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | atan e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | arsinh e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | atanh e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | sinc e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | erf e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | sinh e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | cosh e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | tanh e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | sqrt e ih => exact ⟨by simp [Expr.checkADSupported], fun h => by cases h⟩
  | namedConst c =>
      constructor
      · simp [Expr.checkADSupported]
      · intro h
        cases h

/-- Computable recognition of `ExprSupportedCore`. -/
def Expr.checkSupportedCore : Expr → Bool
  | .const _ | .var _ | .namedConst _ => true
  | .add e₁ e₂ | .mul e₁ e₂ => e₁.checkSupportedCore && e₂.checkSupportedCore
  | .neg e | .exp e | .sin e | .cos e | .log e | .sqrt e |
      .sinh e | .cosh e | .tanh e | .erf e => e.checkSupportedCore
  | _ => false

/-- A successful computable core-support check produces the corresponding
proof object required by the tight Rational evaluator theorem. -/
theorem Expr.checkSupportedCore_correct {e : Expr}
    (h : e.checkSupportedCore = true) : ExprSupportedCore e := by
  induction e with
  | const q => exact .const q
  | var idx => exact .var idx
  | add left right ihLeft ihRight =>
      simp only [Expr.checkSupportedCore, Bool.and_eq_true] at h
      exact .add (ihLeft h.1) (ihRight h.2)
  | mul left right ihLeft ihRight =>
      simp only [Expr.checkSupportedCore, Bool.and_eq_true] at h
      exact .mul (ihLeft h.1) (ihRight h.2)
  | neg e ih => exact .neg (ih h)
  | exp e ih => exact .exp (ih h)
  | sin e ih => exact .sin (ih h)
  | cos e ih => exact .cos (ih h)
  | log e ih => exact .log (ih h)
  | erf e ih => exact .erf (ih h)
  | sinh e ih => exact .sinh (ih h)
  | cosh e ih => exact .cosh (ih h)
  | tanh e ih => exact .tanh (ih h)
  | sqrt e ih => exact .sqrt (ih h)
  | namedConst c => exact .namedConst c
  | inv _ _ | atan _ _ | arsinh _ _ | atanh _ _ | sinc _ _ =>
      simp [Expr.checkSupportedCore] at h

end LeanCert.Core
