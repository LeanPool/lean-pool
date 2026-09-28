/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Core.IntervalRat.Basic
/-!
# Checked evaluation results

Certified evaluators return a finite enclosure only after all partial-domain
conditions have been checked.  Failures are data: callers must propagate them
instead of substituting a finite sentinel that could be mistaken for an
enclosure.
-/

@[expose] public section

namespace LeanCert.Engine

open LeanCert.Core

/-- Why a checked evaluator could not produce a finite certified enclosure. -/
inductive EvalError where
  | reciprocalContainsZero (interval : IntervalRat)
  | logNonpositive (interval : IntervalRat)
  | atanhOutsideUnitBall (interval : IntervalRat)
  | unsupportedBackend (operation : String)
  | unsupportedFeature (feature : String)
  | invalidConfiguration (message : String)
  | nestedFailure (operation : String) (cause : EvalError)
  deriving Repr, DecidableEq

/-- Result type used by checked evaluators and public computation APIs. -/
abbrev EvalResult (α : Type) := Except EvalError α

end LeanCert.Engine
