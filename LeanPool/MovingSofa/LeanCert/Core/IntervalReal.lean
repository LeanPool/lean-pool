/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Core.IntervalRat.Basic
public import LeanPool.MovingSofa.LeanCert.Core.IntervalRat.Transcendental
public import LeanPool.MovingSofa.LeanCert.Core.IntervalRat.Taylor
/-!
# Rational Endpoint Intervals

This file defines `IntervalRat`, a concrete interval type with rational endpoints
suitable for computation. We prove the Fundamental Theorem of Interval Arithmetic
(FTIA) for each operation.

## Module Structure

* `IntervalRat.Basic` - Core types: `IntervalRat`, membership, basic operations
* `IntervalRat.Transcendental` - Noncomputable transcendental bounds (exp, log, sqrt, atanh)
* `IntervalRat.Taylor` - Computable Taylor series evaluators

## Main definitions

* `LeanCert.Core.IntervalRat` - Intervals with rational endpoints
* `LeanCert.Core.IntervalRat.toSet` - Semantic interpretation as a subset of ℝ
* Operations: `add`, `neg`, `sub`, `mul`, `inv`, `div`
* Computable: `expComputable`, `sinComputable`, `cosComputable`

## Main theorems

* `mem_add` - FTIA for addition
* `mem_neg` - FTIA for negation
* `mem_sub` - FTIA for subtraction
* `mem_mul` - FTIA for multiplication
* `mem_expComputable`, `mem_sinComputable`, `mem_cosComputable` - FTIA for computable functions

## Design notes

All operations maintain the invariant `lo ≤ hi`. Domain restrictions for partial
operations (like `inv`) are encoded via separate types or explicit hypotheses.
-/

@[expose] public section

