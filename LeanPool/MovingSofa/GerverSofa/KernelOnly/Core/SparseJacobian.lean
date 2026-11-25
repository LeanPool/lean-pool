/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.MovingSofa.Development.IntervalArithmetic.Foundations.Development002

/-!
# Sparse interval derivatives for Gerver's Jacobian

A passive coordinate has the exact singleton zero derivative. Recognizing it
before replay avoids evaluating the rational interval expression for that coordinate.
-/

@[expose] public section

namespace GerverSofa.PartALeanCert.SparseJacobian

open LeanCert.Core LeanCert.Engine
open LeanCert.Internal.AD (evalTotalCore)

private theorem interval_ext {I J : IntervalRat} (lower : I.lo = J.lo) (upper : I.hi = J.hi) :
    I = J := by
  cases I
  cases J
  cases lower
  cases upper
  rfl

private theorem zero_mul_interval (I : IntervalRat) :
    (IntervalRat.singleton 0).mul I = IntervalRat.singleton 0 := by
  apply interval_ext <;>
    simp only [IntervalRat.mul, IntervalRat.min4, IntervalRat.max4, IntervalRat.singleton,
      zero_mul, min_self, max_self]

private theorem mul_zero_interval (I : IntervalRat) :
    I.mul (IntervalRat.singleton 0) = IntervalRat.singleton 0 := by
  apply interval_ext <;>
    simp only [IntervalRat.mul, IntervalRat.min4, IntervalRat.max4, IntervalRat.singleton,
      mul_zero, min_self, max_self]

private theorem zero_add_interval (I : IntervalRat) :
    (IntervalRat.singleton 0).add I = I := by
  apply interval_ext <;> simp only [IntervalRat.add, IntervalRat.singleton, zero_add]

private theorem add_zero_interval (I : IntervalRat) :
    I.add (IntervalRat.singleton 0) = I := by
  apply interval_ext <;> simp only [IntervalRat.add, IntervalRat.singleton, add_zero]

/-- Add interval derivatives, using `none` for an identically zero derivative. -/
def add (left right : Option IntervalRat) : Option IntervalRat :=
  match left, right with
  | none, value | value, none => value
  | some a, some b => some (a.add b)

private theorem add_getD (left right : Option IntervalRat) :
    (add left right).getD (IntervalRat.singleton 0) =
      (left.getD (IntervalRat.singleton 0)).add (right.getD (IntervalRat.singleton 0)) := by
  cases left <;> cases right <;> simp [add, zero_add_interval, add_zero_interval]

private theorem mul_left_getD (value : IntervalRat) (derivative : Option IntervalRat) :
    (derivative.map (value.mul ·)).getD (IntervalRat.singleton 0) =
      value.mul (derivative.getD (IntervalRat.singleton 0)) := by
  cases derivative <;> simp [mul_zero_interval]

private theorem mul_right_getD (derivative : Option IntervalRat) (value : IntervalRat) :
    (derivative.map (·.mul value)).getD (IntervalRat.singleton 0) =
      (derivative.getD (IntervalRat.singleton 0)).mul value := by
  cases derivative <;> simp [zero_mul_interval]

private theorem neg_getD (derivative : Option IntervalRat) :
    (derivative.map IntervalRat.neg).getD (IntervalRat.singleton 0) =
      (derivative.getD (IntervalRat.singleton 0)).neg := by
  cases derivative <;> rfl

/-- Propagate only active derivatives through the Gerver expression fragment.

The product and chain rules can skip a primal subexpression whenever the
opposite derivative is identically zero. Other constructors use the original
derivative evaluator.
-/
def derivative (environment : IntervalEnv) (index : ℕ) (configuration : EvalConfig) :
    Expr → Option IntervalRat
  | .const _ | .namedConst _ => none
  | .var coordinate => if coordinate = index then some (IntervalRat.singleton 1) else none
  | .add left right =>
    add (derivative environment index configuration left)
      (derivative environment index configuration right)
  | .mul left right =>
    let valueLeft := (Optimization.evalWithDerivCore left environment index configuration).val
    let valueRight := (Optimization.evalWithDerivCore right environment index configuration).val
    add ((derivative environment index configuration left).map (·.mul valueRight))
      ((derivative environment index configuration right).map (valueLeft.mul ·))
  | .neg inner => (derivative environment index configuration inner).map IntervalRat.neg
  | .exp inner =>
    let value := (Optimization.evalWithDerivCore inner environment index configuration).val
    (derivative environment index configuration inner).map
      ((value.expComputable configuration.taylorDepth).mul ·)
  | .sin inner =>
    let value := (Optimization.evalWithDerivCore inner environment index configuration).val
    (derivative environment index configuration inner).map
      ((value.cosComputable configuration.taylorDepth).mul ·)
  | .cos inner =>
    let value := (Optimization.evalWithDerivCore inner environment index configuration).val
    (derivative environment index configuration inner).map
      ((value.sinComputable configuration.taylorDepth).neg.mul ·)
  | other => some (Optimization.derivIntervalCoreN other environment index configuration)

/-- Interpreting a skipped derivative as zero recovers the original interval bounds. -/
theorem derivative_eq (environment : IntervalEnv) (index : ℕ) (configuration : EvalConfig)
    (expression : Expr) :
    (derivative environment index configuration expression).getD (IntervalRat.singleton 0) =
      Optimization.derivIntervalCoreN expression environment index configuration := by
  unfold Optimization.derivIntervalCoreN
  induction expression
  case var coordinate =>
    simp only [derivative, Optimization.evalWithDerivCore, evalTotalCore,
      Optimization.mkDualEnvCore]
    by_cases active : coordinate = index
    · rw [ite_eq_left active, ite_eq_left active]
      rfl
    · rw [ite_eq_right active, ite_eq_right active]
      rfl
  case add ihLeft ihRight =>
    simp only [derivative, add_getD, ihLeft, ihRight]
    rfl
  case mul ihLeft ihRight =>
    simp only [derivative, add_getD, mul_left_getD, mul_right_getD, ihLeft, ihRight]
    rfl
  case neg ih =>
    simp only [derivative, neg_getD, ih]
    rfl
  case exp ih =>
    simp only [derivative, mul_left_getD, ih]
    rfl
  case sin ih =>
    simp only [derivative, mul_left_getD, ih]
    rfl
  case cos ih =>
    simp only [derivative, mul_left_getD, ih]
    rfl
  all_goals rfl

end GerverSofa.PartALeanCert.SparseJacobian
