/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Engine.Eval.Extended
/-!
# Semantic Lemmas for Interval Bounds

This file provides semantic lemmas for deriving real bounds from certified
interval enclosures. Tactics consume these lemmas, but the definitions belong
to the engine layer so checked programmatic APIs do not depend on tactic
modules.

## Main theorems

### Core (computable) lemmas
* `exprCore_le_of_interval_hi` - Upper bound from interval high endpoint
* `exprCore_ge_of_interval_lo` - Lower bound from interval low endpoint
* `exprCore_lt_of_interval_hi_lt` - Strict upper bound
* `exprCore_gt_of_interval_lo_gt` - Strict lower bound

### Extended (noncomputable) lemmas
* `expr_le_of_interval_hi` - Upper bound from interval high endpoint
* `expr_ge_of_interval_lo` - Lower bound from interval low endpoint
* `expr_lt_of_interval_hi_lt` - Strict upper bound
* `expr_gt_of_interval_lo_gt` - Strict lower bound
* `expr_le_of_mem_interval` - Single-point variant
* `expr_ge_of_mem_interval` - Single-point variant

## Usage

These lemmas are intended to be used by tactics like `certify_bound` and
`interval_decide` to close goals of the form `∀ x ∈ I, f(x) ≤ c` or similar.

The core lemmas use the computable evaluator and can work with `native_decide`.
The extended lemmas use the noncomputable evaluator with floor/ceil bounds.
-/

/-! ### Tactic-facing lemmas for interval bounds (core, computable) -/

@[expose] public section

namespace LeanCert.Engine

open LeanCert.Core

/-- Upper bound lemma for core expressions (computable).
    FULLY PROVED - no sorry, no axioms. Accepts configurable Taylor depth.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem exprCore_le_of_interval_hi (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hdom : evalDomainValid1 e I cfg)
    (hhi : (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).hi ≤ c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have hmem := evalIntervalCore1_correct e hsupp x I hx cfg hdom
  simp only [IntervalRat.mem_def] at hmem
  have heval_le_hi : Expr.eval (fun _ => x) e ≤ (LeanCert.Internal.Rational.evalTotalCore1 e I
    cfg).hi := hmem.2
  have hhi_le_c : ((LeanCert.Internal.Rational.evalTotalCore1 e I cfg).hi : ℝ) ≤ c := by
    exact_mod_cast hhi
  exact le_trans heval_le_hi hhi_le_c

/-- Lower bound lemma for core expressions (computable).
    FULLY PROVED - no sorry, no axioms. Accepts configurable Taylor depth.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem exprCore_ge_of_interval_lo (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hdom : evalDomainValid1 e I cfg)
    (hlo : c ≤ (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).lo) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalIntervalCore1_correct e hsupp x I hx cfg hdom
  simp only [IntervalRat.mem_def] at hmem
  have hlo_le_eval : (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).lo ≤ Expr.eval (fun _ =>
    x) e := hmem.1
  have hc_le_lo : (c : ℝ) ≤ (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).lo := by
    exact_mod_cast hlo
  exact le_trans hc_le_lo hlo_le_eval

/-- Strict upper bound for core expressions (computable).
    FULLY PROVED - no sorry, no axioms. Accepts configurable Taylor depth.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem exprCore_lt_of_interval_hi_lt (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hdom : evalDomainValid1 e I cfg)
    (hhi : (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).hi < c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  intro x hx
  have hmem := evalIntervalCore1_correct e hsupp x I hx cfg hdom
  simp only [IntervalRat.mem_def] at hmem
  have heval_le_hi : Expr.eval (fun _ => x) e ≤ (LeanCert.Internal.Rational.evalTotalCore1 e I
    cfg).hi := hmem.2
  have hhi_lt_c : ((LeanCert.Internal.Rational.evalTotalCore1 e I cfg).hi : ℝ) < c := by
    exact_mod_cast hhi
  exact lt_of_le_of_lt heval_le_hi hhi_lt_c

/-- Strict lower bound for core expressions (computable).
    FULLY PROVED - no sorry, no axioms. Accepts configurable Taylor depth.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem exprCore_gt_of_interval_lo_gt (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hdom : evalDomainValid1 e I cfg)
    (hlo : c < (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).lo) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalIntervalCore1_correct e hsupp x I hx cfg hdom
  simp only [IntervalRat.mem_def] at hmem
  have hlo_le_eval : (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).lo ≤ Expr.eval (fun _ =>
    x) e := hmem.1
  have hc_lt_lo : (c : ℝ) < (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).lo := by
    exact_mod_cast hlo
  exact lt_of_lt_of_le hc_lt_lo hlo_le_eval

/-! ### Tactic-facing lemmas for interval bounds (extended, noncomputable) -/

/-- Upper bound lemma for extended expressions.
    FULLY PROVED - no sorry, no axioms. -/
theorem expr_le_of_interval_hi (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (c : ℚ) (hhi : (LeanCert.Internal.Rational.evalUnchecked1 e I).hi ≤ c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have hmem := evalInterval1_correct e hsupp x I hx
  simp only [IntervalRat.mem_def] at hmem
  have heval_le_hi : Expr.eval (fun _ => x) e ≤ (LeanCert.Internal.Rational.evalUnchecked1 e I).hi
    := hmem.2
  have hhi_le_c : ((LeanCert.Internal.Rational.evalUnchecked1 e I).hi : ℝ) ≤ c := by
    exact_mod_cast hhi
  exact le_trans heval_le_hi hhi_le_c

/-- Lower bound lemma for extended expressions.
    FULLY PROVED - no sorry, no axioms. -/
theorem expr_ge_of_interval_lo (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (c : ℚ) (hlo : c ≤ (LeanCert.Internal.Rational.evalUnchecked1 e I).lo) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalInterval1_correct e hsupp x I hx
  simp only [IntervalRat.mem_def] at hmem
  have hlo_le_eval : (LeanCert.Internal.Rational.evalUnchecked1 e I).lo ≤ Expr.eval (fun _ => x) e
    := hmem.1
  have hc_le_lo : (c : ℝ) ≤ (LeanCert.Internal.Rational.evalUnchecked1 e I).lo := by
    exact_mod_cast hlo
  exact le_trans hc_le_lo hlo_le_eval

/-- Strict upper bound for extended expressions.
    FULLY PROVED - no sorry, no axioms. -/
theorem expr_lt_of_interval_hi_lt (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (c : ℚ) (hhi : (LeanCert.Internal.Rational.evalUnchecked1 e I).hi < c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  intro x hx
  have hmem := evalInterval1_correct e hsupp x I hx
  simp only [IntervalRat.mem_def] at hmem
  have heval_le_hi : Expr.eval (fun _ => x) e ≤ (LeanCert.Internal.Rational.evalUnchecked1 e I).hi
    := hmem.2
  have hhi_lt_c : ((LeanCert.Internal.Rational.evalUnchecked1 e I).hi : ℝ) < c := by
    exact_mod_cast hhi
  exact lt_of_le_of_lt heval_le_hi hhi_lt_c

/-- Strict lower bound for extended expressions.
    FULLY PROVED - no sorry, no axioms. -/
theorem expr_gt_of_interval_lo_gt (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (c : ℚ) (hlo : c < (LeanCert.Internal.Rational.evalUnchecked1 e I).lo) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalInterval1_correct e hsupp x I hx
  simp only [IntervalRat.mem_def] at hmem
  have hlo_le_eval : (LeanCert.Internal.Rational.evalUnchecked1 e I).lo ≤ Expr.eval (fun _ => x) e
    := hmem.1
  have hc_lt_lo : (c : ℝ) < (LeanCert.Internal.Rational.evalUnchecked1 e I).lo := by
    exact_mod_cast hlo
  exact lt_of_lt_of_le hc_lt_lo hlo_le_eval

/-- Variant for single point (extended). -/
theorem expr_le_of_mem_interval (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (c : ℚ) (x : ℝ) (hx : x ∈ I)
    (hhi : (LeanCert.Internal.Rational.evalUnchecked1 e I).hi ≤ c) :
    Expr.eval (fun _ => x) e ≤ c :=
  expr_le_of_interval_hi e hsupp I c hhi x hx

/-- Variant for single point (extended). -/
theorem expr_ge_of_mem_interval (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (c : ℚ) (x : ℝ) (hx : x ∈ I)
    (hlo : c ≤ (LeanCert.Internal.Rational.evalUnchecked1 e I).lo) :
    c ≤ Expr.eval (fun _ => x) e :=
  expr_ge_of_interval_lo e hsupp I c hlo x hx

end LeanCert.Engine
