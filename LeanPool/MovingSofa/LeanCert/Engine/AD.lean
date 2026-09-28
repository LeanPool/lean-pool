/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Engine.AD.Basic
public import LeanPool.MovingSofa.LeanCert.Engine.AD.Transcendental
public import LeanPool.MovingSofa.LeanCert.Engine.AD.Eval
public import LeanPool.MovingSofa.LeanCert.Engine.AD.Correctness
public import LeanPool.MovingSofa.LeanCert.Engine.AD.PartialCorrectness
public import LeanPool.MovingSofa.LeanCert.Engine.AD.Computable
public import LeanPool.MovingSofa.LeanCert.Engine.AD.DomainChecked
public import LeanPool.MovingSofa.LeanCert.Engine.AD.Dyadic
/-!
# Automatic Differentiation via Intervals

This module provides forward-mode automatic differentiation using interval
arithmetic. We compute both the value and derivative of an expression,
with rigorous bounds on both.

## Module Structure

* `AD.Basic` - Core types: `DualInterval`, basic operations (`add`, `mul`, `neg`)
* `AD.Transcendental` - Transcendental functions (`sin`, `cos`, `exp`, etc.)
* `AD.Eval` - Evaluators: `LeanCert.Internal.AD.evalUnchecked`, `evalDual?`, `derivInterval`
* `AD.Correctness` - Correctness theorems for supported expressions
* `AD.PartialCorrectness` - Correctness for partial functions (inv, log, sqrt)
* `AD.Computable` - Taylor-based computable evaluators
* `AD.DomainChecked` - Computable AD with box-dependent checks for inv and log
* `AD.Dyadic` - Domain-aware AD with bounded-denominator Dyadic arithmetic

## Main definitions

* `DualInterval` - A pair of intervals representing (value, derivative)
* `LeanCert.Internal.AD.evalUnchecked` - Evaluate expression to get value and derivative intervals
* `evalDual?` - Partial evaluator supporting inv, log, sqrt
* `LeanCert.Internal.AD.evalTotalCore` - Computable evaluator for native_decide
* `evalDualChecked`, `derivIntervalChecked` - Computable, structured-failure APIs for inv/log
* `evalDualDyadicChecked`, `derivIntervalDyadicChecked` - Checked Dyadic counterparts

## Main theorems

* `LeanCert.Engine.evalDualUnchecked_val_correct` - Value component is correct for supported
expressions
* `LeanCert.Engine.evalDualUnchecked_der_correct` - Derivative component is correct for supported
expressions
* `evalDual?_val_correct`, `evalDual?_der_correct` - Correctness with domain checks
* `LeanCert.Internal.AD.evalTotalCore_val_correct`, `LeanCert.Internal.AD.evalTotalCore_der_correct`
- Computable correctness
* `evalWithDerivChecked_der_correct`, `derivIntervalChecked_correct` - Golden theorems for
  successful domain-aware computation

All theorems are FULLY PROVED with no sorry or axioms.
-/

@[expose] public section

