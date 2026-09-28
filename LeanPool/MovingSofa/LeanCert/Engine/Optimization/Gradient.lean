/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Engine.AD
public import LeanPool.MovingSofa.LeanCert.Engine.Optimize
public import LeanPool.MovingSofa.LeanCert.Engine.Optimization.Box
/-!
# Gradient Interval Computation for Optimization

This file provides functions to compute interval bounds on the gradient ∇f(B)
of an expression over a box B. This is used for monotonicity-based pruning
in branch-and-bound global optimization.

## Main definitions

* `gradientInterval` - Compute interval bounds on all partial derivatives over a box
* `gradientSignature` - Determine the sign of each partial derivative
* `canPruneToLo` / `canPruneToHi` - Check if a coordinate can be pruned by monotonicity

## Design

The gradient is computed by running forward-mode AD (from AD.lean) for each
coordinate direction. The result is a list of intervals, one per variable.

Monotonicity pruning: If ∂f/∂xᵢ > 0 on the entire box B, then f is minimized
when xᵢ = B[i].lo. We can shrink the box in that dimension to a point.
-/

/-! ### Gradient computation -/

@[expose] public section

namespace LeanCert.Engine.Optimization

open LeanCert.Core
open LeanCert.Engine

/-- Compute the gradient interval: bounds on each partial derivative over a box.
    Returns a list of intervals, where the i-th interval contains ∂f/∂xᵢ for all x ∈ B. -/
noncomputable def gradientInterval (e : Expr) (B : Box) : List IntervalRat :=
  List.ofFn fun (i : Fin B.length) => derivInterval e (Box.toEnv B) i.val

/-- Compute gradient for n variables (explicit dimension) -/
noncomputable def gradientIntervalN (e : Expr) (B : Box) (n : Nat) : List IntervalRat :=
  (List.range n).map fun i => derivInterval e (Box.toEnv B) i

/-! ### Computable versions -/

/-- Create dual environment for differentiating with respect to variable `idx` (computable).
    Active variable gets der = 1, passive variables get der = 0. -/
def mkDualEnvCore (ρ : IntervalEnv) (idx : Nat) : DualEnv :=
  fun i => if i = idx then DualInterval.varActive (ρ i) else DualInterval.varPassive (ρ i)

/-- Evaluate with derivative with respect to variable `idx` (computable version) -/
def evalWithDerivCore (e : Expr) (ρ : IntervalEnv) (idx : Nat) (cfg : EvalConfig := {}) :
  DualInterval :=
  LeanCert.Internal.AD.evalTotalCore e (mkDualEnvCore ρ idx) cfg

/-- Computable derivative interval for multi-variable expressions.
    Computes the interval containing ∂f/∂xᵢ over the box. -/
def derivIntervalCoreN (e : Expr) (ρ : IntervalEnv) (idx : Nat) (cfg : EvalConfig := {}) :
  IntervalRat :=
  (evalWithDerivCore e ρ idx cfg).der

/-- Correctness of the computable derivative evaluator for an arbitrary
coordinate of a multivariate expression. -/
theorem evalDualTotalCore_der_correct_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i) (x : ℝ) (hx : x ∈ ρ_int idx)
    (cfg : EvalConfig) :
    deriv (Expr.evalAlong e ρ_real idx) x ∈
      (LeanCert.Internal.AD.evalTotalCore e (mkDualEnvCore ρ_int idx) cfg).der := by
  have hmem : ∀ i, Expr.updateVar ρ_real idx x i ∈
      (mkDualEnvCore ρ_int idx i).val := by
    simpa only [mkDualEnvCore, mkDualEnv] using
      (updateVar_mem_mkDualEnv_val ρ_real ρ_int idx x hx hρ)
  induction hsupp generalizing x with
  | const q =>
      simp only [Expr.evalAlong_const', deriv_const, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.const]
      exact_mod_cast IntervalRat.mem_singleton 0
  | var i =>
      by_cases hi : i = idx
      · subst i
        simp only [Expr.evalAlong_var_active, LeanCert.Internal.AD.evalTotalCore, mkDualEnvCore,
          ↓reduceIte, DualInterval.varActive, deriv_id]
        exact_mod_cast IntervalRat.mem_singleton 1
      · simp only [Expr.evalAlong_var_passive _ _ _ hi, deriv_const,
        LeanCert.Internal.AD.evalTotalCore,
          mkDualEnvCore, ite_eq_right hi, DualInterval.varPassive]
        exact_mod_cast IntervalRat.mem_singleton 0
  | add h₁ h₂ ih₁ ih₂ =>
      have hd₁ := evalAlong_differentiable _ h₁ ρ_real idx
      have hd₂ := evalAlong_differentiable _ h₂ ρ_real idx
      simp only [Expr.evalAlong_add_pi, deriv_add (hd₁ x) (hd₂ x),
        LeanCert.Internal.AD.evalTotalCore,
        DualInterval.add]
      exact IntervalRat.mem_add (ih₁ x hx hmem) (ih₂ x hx hmem)
  | mul h₁ h₂ ih₁ ih₂ =>
      have hd₁ := evalAlong_differentiable _ h₁ ρ_real idx
      have hd₂ := evalAlong_differentiable _ h₂ ρ_real idx
      simp only [Expr.evalAlong_mul_pi, deriv_mul (hd₁ x) (hd₂ x),
        LeanCert.Internal.AD.evalTotalCore,
        DualInterval.mul]
      have hdom₁ := evalDomainValidDual_of_ExprSupported _ h₁
        (mkDualEnvCore ρ_int idx) cfg
      have hdom₂ := evalDomainValidDual_of_ExprSupported _ h₂
        (mkDualEnvCore ρ_int idx) cfg
      have hval₁ := LeanCert.Engine.evalDualTotalCore_val_correct _ h₁.toCore
        (Expr.updateVar ρ_real idx x) (mkDualEnvCore ρ_int idx) cfg hmem hdom₁
      have hval₂ := LeanCert.Engine.evalDualTotalCore_val_correct _ h₂.toCore
        (Expr.updateVar ρ_real idx x) (mkDualEnvCore ρ_int idx) cfg hmem hdom₂
      exact IntervalRat.mem_add (IntervalRat.mem_mul (ih₁ x hx hmem) hval₂)
        (IntervalRat.mem_mul hval₁ (ih₂ x hx hmem))
  | neg hs ih =>
      have hd := evalAlong_differentiable _ hs ρ_real idx
      simp only [Expr.evalAlong_neg_pi, deriv.neg, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.neg]
      exact IntervalRat.mem_neg (ih x hx hmem)
  | @sin e' hs ih =>
      have hd := evalAlong_differentiable e' hs ρ_real idx
      simp only [Expr.evalAlong_sin, deriv_sin (hd.differentiableAt),
        LeanCert.Internal.AD.evalTotalCore,
        DualInterval.sinCore]
      have hdom := evalDomainValidDual_of_ExprSupported e' hs
        (mkDualEnvCore ρ_int idx) cfg
      have hval := LeanCert.Engine.evalDualTotalCore_val_correct e' hs.toCore
        (Expr.updateVar ρ_real idx x) (mkDualEnvCore ρ_int idx) cfg hmem hdom
      exact IntervalRat.mem_mul
        (IntervalRat.mem_cosComputable hval cfg.taylorDepth) (ih x hx hmem)
  | @cos e' hs ih =>
      have hd := evalAlong_differentiable e' hs ρ_real idx
      simp only [Expr.evalAlong_cos, deriv_cos (hd.differentiableAt),
        LeanCert.Internal.AD.evalTotalCore,
        DualInterval.cosCore]
      have hdom := evalDomainValidDual_of_ExprSupported e' hs
        (mkDualEnvCore ρ_int idx) cfg
      have hval := LeanCert.Engine.evalDualTotalCore_val_correct e' hs.toCore
        (Expr.updateVar ρ_real idx x) (mkDualEnvCore ρ_int idx) cfg hmem hdom
      exact IntervalRat.mem_mul
        (IntervalRat.mem_neg (IntervalRat.mem_sinComputable hval cfg.taylorDepth)) (ih x hx hmem)
  | @exp e' hs ih =>
      have hd := evalAlong_differentiable e' hs ρ_real idx
      simp only [Expr.evalAlong_exp, deriv_exp (hd.differentiableAt),
        LeanCert.Internal.AD.evalTotalCore,
        DualInterval.expCore]
      have hdom := evalDomainValidDual_of_ExprSupported e' hs
        (mkDualEnvCore ρ_int idx) cfg
      have hval := LeanCert.Engine.evalDualTotalCore_val_correct e' hs.toCore
        (Expr.updateVar ρ_real idx x) (mkDualEnvCore ρ_int idx) cfg hmem hdom
      exact IntervalRat.mem_mul
        (IntervalRat.mem_expComputable hval cfg.taylorDepth) (ih x hx hmem)

/-- Computable version of gradient interval for Core expressions.
    This can be used with `native_decide` for verified optimization. -/
def gradientIntervalCore (e : Expr) (B : Box) (cfg : EvalConfig := {}) : List IntervalRat :=
  (List.range B.length).map fun i => derivIntervalCoreN e (Box.toEnv B) i cfg

/-- Compute every partial derivative using the domain-aware checked AD path.
Unlike `gradientIntervalCore`, this rejects unsupported syntax, reciprocal
arguments containing zero, and nonpositive logarithm arguments instead of
returning a finite interval that could be mistaken for a certificate. -/
def gradientIntervalChecked (e : Expr) (B : Box) (cfg : EvalConfig := {}) :
    EvalResult (List IntervalRat) :=
  (List.range B.length).mapM fun i =>
    derivIntervalChecked e (Box.toEnv B) i cfg

private theorem derivIntervalsChecked_correct (e : Expr) (B : Box)
    (cfg : EvalConfig) (ρReal : Nat → ℝ)
    (hρ : ∀ i, ρReal i ∈ Box.toEnv B i) (indices : List Nat)
    (gradient : List IntervalRat)
    (hok : indices.mapM (fun i => derivIntervalChecked e (Box.toEnv B) i cfg) =
      .ok gradient) :
    List.Forall₂ (fun i dI => deriv (Expr.evalAlong e ρReal i) (ρReal i) ∈ dI)
      indices gradient := by
  induction indices generalizing gradient with
  | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hok
      subst gradient
      exact .nil
  | cons i indices ih =>
      simp only [List.mapM_cons] at hok
      cases hdi : derivIntervalChecked e (Box.toEnv B) i cfg with
      | error err =>
          rw [hdi] at hok
          simp only [bind, Except.bind] at hok
          cases hok
      | ok dI =>
          rw [hdi] at hok
          simp only [bind, Except.bind] at hok
          cases htail : List.mapM
              (fun j => derivIntervalChecked e (Box.toEnv B) j cfg) indices with
          | error err =>
              rw [htail] at hok
              cases hok
          | ok tail =>
              rw [htail] at hok
              simp only [pure, Except.pure, Except.ok.injEq] at hok
              subst gradient
              exact .cons
                (derivIntervalChecked_correct e ρReal (Box.toEnv B) i cfg dI
                  (ρReal i) (hρ i) hρ hdi)
                (ih tail htail)

/-- Golden soundness theorem for a successfully computed checked gradient.
The output list is aligned with coordinates `0, …, B.length - 1`. -/
theorem gradientIntervalChecked_correct (e : Expr) (B : Box)
    (cfg : EvalConfig) (ρReal : Nat → ℝ)
    (hρ : Box.envMem ρReal B)
    (hzero : ∀ i, i ≥ B.length → ρReal i = 0)
    (gradient : List IntervalRat)
    (hok : gradientIntervalChecked e B cfg = .ok gradient) :
    List.Forall₂ (fun i dI => deriv (Expr.evalAlong e ρReal i) (ρReal i) ∈ dI)
      (List.range B.length) gradient := by
  exact derivIntervalsChecked_correct e B cfg ρReal
    (Box.envMem_toEnv ρReal B hρ hzero) (List.range B.length) gradient hok

/-! ### Sign classification -/

/-- Classification of an interval's sign -/
inductive IntervalSign where
  | positive     -- lo > 0 (strictly positive)
  | negative     -- hi < 0 (strictly negative)
  | nonpositive  -- hi ≤ 0
  | nonnegative  -- lo ≥ 0
  | indefinite   -- contains zero in interior
  deriving Repr, DecidableEq

/-- Classify the sign of an interval -/
def classifySign (I : IntervalRat) : IntervalSign :=
  if I.lo > 0 then .positive
  else if I.hi < 0 then .negative
  else if I.hi ≤ 0 then .nonpositive
  else if I.lo ≥ 0 then .nonnegative
  else .indefinite

/-- The gradient signature: sign of each partial derivative (noncomputable wrapper) -/
noncomputable def gradientSignature (e : Expr) (B : Box) : List IntervalSign :=
  (gradientIntervalN e B B.length).map classifySign

/-! ### Monotonicity predicates -/

/-- Check if interval is strictly positive -/
def isStrictlyPositive (I : IntervalRat) : Bool := I.lo > 0

/-- Check if interval is strictly negative -/
def isStrictlyNegative (I : IntervalRat) : Bool := I.hi < 0

/-- Check if interval is nonnegative -/
def isNonnegative (I : IntervalRat) : Bool := I.lo ≥ 0

/-- Check if interval is nonpositive -/
def isNonpositive (I : IntervalRat) : Bool := I.hi ≤ 0

/-! ### Pruning queries -/

/-- Can we prune coordinate i to its low endpoint for minimization?
    True if ∂f/∂xᵢ > 0 on B (f is increasing in xᵢ, so min is at lo). -/
def canPruneToLo (deriv_i : IntervalRat) : Bool :=
  isStrictlyPositive deriv_i

/-- Can we prune coordinate i to its high endpoint for minimization?
    True if ∂f/∂xᵢ < 0 on B (f is decreasing in xᵢ, so min is at hi). -/
def canPruneToHi (deriv_i : IntervalRat) : Bool :=
  isStrictlyNegative deriv_i

/-- Prune a box for minimization by fixing monotonic coordinates.
    Returns a (potentially smaller) box and a list of fixed coordinates. -/
def pruneBoxForMin (B : Box) (grad : List IntervalRat) : Box × List Nat :=
  let pruned := B.zipIdx.map fun (I, idx) =>
    match grad[idx]? with
    | some di =>
      if canPruneToLo di then
        -- ∂f/∂xᵢ > 0: fix xᵢ = I.lo
        (IntervalRat.singleton I.lo, some idx)
      else if canPruneToHi di then
        -- ∂f/∂xᵢ < 0: fix xᵢ = I.hi
        (IntervalRat.singleton I.hi, some idx)
      else
        (I, none)
    | none => (I, none)
  (pruned.map (·.1), pruned.filterMap (·.2))

/-! ### Correctness theorems -/

/-- The computed gradient interval contains the true partial derivatives.
    This follows from evalDual_der_correct_idx in AD.lean. -/
theorem gradientInterval_correct (e : Expr) (hsupp : ADSupported e)
    (B : Box) (ρ : Nat → ℝ) (hρ : Box.envMem ρ B)
    (hzero : ∀ i, i ≥ B.length → ρ i = 0)
    (i : Fin B.length) :
    deriv (Expr.evalAlong e ρ i.val) (ρ i.val) ∈
      ((gradientIntervalN e B B.length)[i.val]?).getD default := by
  -- The i-th element of gradientIntervalN is derivInterval e (toEnv B) i
  have hget : (gradientIntervalN e B B.length)[i.val]? =
      some (derivInterval e (Box.toEnv B) i.val) := by
    simp only [gradientIntervalN]
    rw [List.getElem?_map]
    simp only [List.getElem?_range i.isLt, Option.map_some]
  simp only [hget, Option.getD]
  -- Apply the AD correctness theorem
  have henv : ∀ j, ρ j ∈ Box.toEnv B j := Box.envMem_toEnv ρ B hρ hzero
  exact derivInterval_correct_idx e hsupp ρ (Box.toEnv B) i.val henv (ρ i.val) (henv i.val)

/-- If we prune a coordinate to lo because ∂f/∂xᵢ > 0, the minimum is preserved.
    Informal: if f is increasing in xᵢ on B, then min{f(x) : x ∈ B} = min{f(x) : xᵢ = B[i].lo}.
    NOTE: Requires ρ j = 0 for j ≥ B.length (standard assumption for box membership). -/
theorem pruneToLo_preserves_min (e : Expr) (hsupp : ADSupported e)
    (B : Box) (i : Fin B.length)
    (hgrad : isStrictlyPositive (derivInterval e (Box.toEnv B) i.val) = true) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ j, j ≥ B.length → ρ j = 0) →
      ∃ (ρ' : Nat → ℝ), Box.envMem ρ' B ∧ (∀ j, j ≥ B.length → ρ' j = 0) ∧
        ρ' i.val = B[i.val].lo ∧ Expr.eval ρ' e ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  -- The idea: if ∂f/∂xᵢ > 0 everywhere, then f(ρ) ≥ f(ρ[xᵢ := lo])
  -- We construct ρ' by replacing coordinate i with the low endpoint
  let ρ' : Nat → ℝ := fun j => if j = i.val then (B[i.val].lo : ℝ) else ρ j
  use ρ'
  constructor
  · -- ρ' ∈ B
    intro ⟨j, hj⟩
    by_cases h : j = i.val
    · subst h
      simp only [↓reduceIte, ρ', IntervalRat.mem_def]
      constructor
      · exact le_refl _
      · have := B[i.val].le
        exact_mod_cast this
    · simp only [ite_eq_right h, ρ']
      exact hρ ⟨j, hj⟩
  constructor
  · -- ρ' j = 0 for j ≥ B.length
    intro j hj
    simp only [ρ']
    have hne : j ≠ i.val := by
      intro heq
      rw [heq] at hj
      exact absurd i.isLt (not_lt.mpr hj)
    simp only [ite_eq_right hne]
    exact hzero j hj
  constructor
  · -- ρ' i = B[i].lo
    simp only [↓reduceIte, ρ']
  · -- f(ρ') ≤ f(ρ)
    -- Use the monotonicity theorem: if ∂f/∂xᵢ > 0, minimum is at left endpoint
    -- Convert the boolean condition to a real inequality
    simp only [isStrictlyPositive, decide_eq_true_eq] at hgrad
    -- Build the interval environment from the box
    let ρ_int : IntervalEnv := Box.toEnv B
    -- Show ρ ∈ ρ_int (membership in the interval environment)
    have hρ_int : ∀ j, ρ j ∈ ρ_int j := by
      intro j
      simp only [ρ_int, Box.toEnv, List.getD]
      by_cases hj : j < B.length
      · simp only [List.getElem?_eq_getElem hj, Option.getD]
        exact hρ ⟨j, hj⟩
      · simp only [List.getElem?_eq_none (not_lt.mp hj), Option.getD]
        rw [IntervalRat.mem_default]
        exact hzero j (not_lt.mp hj)
    -- Apply the monotonicity theorem
    have hmono := increasing_min_at_left_idx e hsupp ρ ρ_int i.val hρ_int hgrad
    -- The key fact: ρ i.val ∈ ρ_int i.val = B[i.val]
    have hρ_i_mem : ρ i.val ∈ ρ_int i.val := hρ_int i.val
    have hmin := hmono (ρ i.val) hρ_i_mem
    -- Now relate evalAlong to eval via ρ'
    -- evalAlong e ρ i.val t = eval (updateVar ρ i.val t) e
    simp only [Expr.evalAlong] at hmin
    -- Need: (ρ_int i.val).lo = B[i.val].lo
    have hlo_eq : (ρ_int i.val).lo = B[i.val].lo := by
      simp only [ρ_int, Box.toEnv, List.getD, List.getElem?_eq_getElem i.isLt, Option.getD]
    -- And: updateVar ρ i.val (ρ_int i.val).lo = ρ'
    have hρ'_eq : Expr.updateVar ρ i.val ((ρ_int i.val).lo : ℝ) = ρ' := by
      funext j
      simp only [Expr.updateVar, ρ']
      split_ifs with hj
      · simp only [hlo_eq]
      · rfl
    -- And: updateVar ρ i.val (ρ i.val) = ρ
    have hρ_eq : Expr.updateVar ρ i.val (ρ i.val) = ρ := Expr.updateVar_self ρ i.val
    rw [hρ'_eq, hρ_eq] at hmin
    exact hmin

/-- If we prune a coordinate to hi because ∂f/∂xᵢ < 0, the minimum is preserved.
    NOTE: Requires ρ j = 0 for j ≥ B.length (standard assumption for box membership). -/
theorem pruneToHi_preserves_min (e : Expr) (hsupp : ADSupported e)
    (B : Box) (i : Fin B.length)
    (hgrad : isStrictlyNegative (derivInterval e (Box.toEnv B) i.val) = true) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ j, j ≥ B.length → ρ j = 0) →
      ∃ (ρ' : Nat → ℝ), Box.envMem ρ' B ∧ (∀ j, j ≥ B.length → ρ' j = 0) ∧
        ρ' i.val = B[i.val].hi ∧ Expr.eval ρ' e ≤ Expr.eval ρ e := by
  intro ρ hρ hzero
  let ρ' : Nat → ℝ := fun j => if j = i.val then (B[i.val].hi : ℝ) else ρ j
  use ρ'
  constructor
  · -- ρ' ∈ B
    intro ⟨j, hj⟩
    by_cases h : j = i.val
    · subst h
      simp only [↓reduceIte, ρ', IntervalRat.mem_def]
      constructor
      · have := B[i.val].le
        exact_mod_cast this
      · exact le_refl _
    · simp only [ite_eq_right h, ρ']
      exact hρ ⟨j, hj⟩
  constructor
  · -- ρ' j = 0 for j ≥ B.length
    intro j hj
    simp only [ρ']
    have hne : j ≠ i.val := by
      intro heq
      rw [heq] at hj
      exact absurd i.isLt (not_lt.mpr hj)
    simp only [ite_eq_right hne]
    exact hzero j hj
  constructor
  · simp only [↓reduceIte, ρ']
  · -- f(ρ') ≤ f(ρ)
    -- Use the monotonicity theorem: if ∂f/∂xᵢ < 0, minimum is at right endpoint
    simp only [isStrictlyNegative, decide_eq_true_eq] at hgrad
    -- Build the interval environment from the box
    let ρ_int : IntervalEnv := Box.toEnv B
    -- Show ρ ∈ ρ_int
    have hρ_int : ∀ j, ρ j ∈ ρ_int j := by
      intro j
      simp only [ρ_int, Box.toEnv, List.getD]
      by_cases hj : j < B.length
      · simp only [List.getElem?_eq_getElem hj, Option.getD]
        exact hρ ⟨j, hj⟩
      · simp only [List.getElem?_eq_none (not_lt.mp hj), Option.getD]
        rw [IntervalRat.mem_default]
        exact hzero j (not_lt.mp hj)
    -- Apply the monotonicity theorem for decreasing functions
    have hmono := decreasing_min_at_right_idx e hsupp ρ ρ_int i.val hρ_int hgrad
    -- The key fact: ρ i.val ∈ ρ_int i.val = B[i.val]
    have hρ_i_mem : ρ i.val ∈ ρ_int i.val := hρ_int i.val
    have hmin := hmono (ρ i.val) hρ_i_mem
    -- Now relate evalAlong to eval via ρ'
    simp only [Expr.evalAlong] at hmin
    -- Need: (ρ_int i.val).hi = B[i.val].hi
    have hhi_eq : (ρ_int i.val).hi = B[i.val].hi := by
      simp only [ρ_int, Box.toEnv, List.getD, List.getElem?_eq_getElem i.isLt, Option.getD]
    -- And: updateVar ρ i.val (ρ_int i.val).hi = ρ'
    have hρ'_eq : Expr.updateVar ρ i.val ((ρ_int i.val).hi : ℝ) = ρ' := by
      funext j
      simp only [Expr.updateVar, ρ']
      split_ifs with hj
      · simp only [hhi_eq]
      · rfl
    -- And: updateVar ρ i.val (ρ i.val) = ρ
    have hρ_eq : Expr.updateVar ρ i.val (ρ i.val) = ρ := Expr.updateVar_self ρ i.val
    rw [hρ'_eq, hρ_eq] at hmin
    exact hmin

/-! ### Pruned box membership and correctness -/

/-- Helper: membership in the pruned box implies membership in the original box.
    The pruned box only shrinks coordinates, never expands them. -/
theorem pruneBoxForMin_subset (B : Box) (grad : List IntervalRat) :
    ∀ ρ, Box.envMem ρ (pruneBoxForMin B grad).1 → Box.envMem ρ B := by
  intro ρ hρ'
  let B' := (pruneBoxForMin B grad).1
  intro ⟨j, hj⟩
  have hj' : j < B'.length := by
    simp only [B', pruneBoxForMin, List.length_map, List.length_zipIdx]
    exact hj
  have hρ'_mem : ρ j ∈ B'[j] := hρ' ⟨j, hj'⟩
  -- Get the j-th element of B'
  simp only [B', pruneBoxForMin] at hρ'_mem
  rw [List.getElem_map, List.getElem_map] at hρ'_mem
  have h_zipIdx_len : j < (B.zipIdx).length := by simp only [List.length_zipIdx]; exact hj
  have h_zipIdx : (B.zipIdx)[j] = (B[j], j) := by
    rw [List.getElem_zipIdx (h := h_zipIdx_len)]
    simp only [Nat.zero_add]
  simp only [h_zipIdx] at hρ'_mem
  -- Now analyze the cases
  cases hgrad_j : grad[j]? with
  | none =>
    simp only [hgrad_j] at hρ'_mem
    exact hρ'_mem
  | some di =>
    simp only [hgrad_j] at hρ'_mem
    by_cases hlo : canPruneToLo di
    · simp only [hlo, ↓reduceIte] at hρ'_mem
      simp only [IntervalRat.mem_def]
      have hρ_eq : ρ j = B[j].lo := by
        simp only [IntervalRat.singleton, IntervalRat.mem_def] at hρ'_mem
        linarith [hρ'_mem.1, hρ'_mem.2]
      rw [hρ_eq]
      exact ⟨le_refl _, by exact_mod_cast B[j].le⟩
    · by_cases hhi : canPruneToHi di
      · simp only [hlo, Bool.false_eq_true, ↓reduceIte, hhi] at hρ'_mem
        simp only [IntervalRat.mem_def]
        have hρ_eq : ρ j = B[j].hi := by
          simp only [IntervalRat.singleton, IntervalRat.mem_def] at hρ'_mem
          linarith [hρ'_mem.1, hρ'_mem.2]
        rw [hρ_eq]
        exact ⟨by exact_mod_cast B[j].le, le_refl _⟩
      · simp only [hlo, Bool.false_eq_true, ↓reduceIte, hhi] at hρ'_mem
        exact hρ'_mem

/-- The pruned box has the same length as the original box -/
theorem pruneBoxForMin_length (B : Box) (grad : List IntervalRat) :
    (pruneBoxForMin B grad).1.length = B.length := by
  simp only [pruneBoxForMin, List.length_map, List.length_zipIdx]

/-- A positive computable derivative enclosure makes the objective increasing
along the selected coordinate. -/
theorem increasing_min_at_left_idx_core (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i) (cfg : EvalConfig)
    (hpos : 0 < (derivIntervalCoreN e ρ_int idx cfg).lo) :
    ∀ x ∈ ρ_int idx,
      Expr.evalAlong e ρ_real idx (ρ_int idx).lo ≤ Expr.evalAlong e ρ_real idx x := by
  have hdiff := evalAlong_differentiable e hsupp ρ_real idx
  have hmono : StrictMonoOn (Expr.evalAlong e ρ_real idx)
      (Set.Icc ((ρ_int idx).lo : ℝ) ((ρ_int idx).hi : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact hdiff.continuous.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ ρ_int idx := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      have hmem := evalDualTotalCore_der_correct_idx e hsupp ρ_real ρ_int idx hρ x hx' cfg
      exact lt_of_lt_of_le (by exact_mod_cast hpos) ((IntervalRat.mem_def _ _).mp hmem).1
  intro x hx
  rcases hx with ⟨hlo, hhi⟩
  by_cases heq : ((ρ_int idx).lo : ℝ) = x
  · exact heq ▸ le_rfl
  · exact le_of_lt (hmono
      ⟨le_rfl, by exact_mod_cast (ρ_int idx).le⟩ ⟨hlo, hhi⟩
      (lt_of_le_of_ne hlo heq))

/-- A negative computable derivative enclosure makes the objective decreasing
along the selected coordinate. -/
theorem decreasing_min_at_right_idx_core (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i) (cfg : EvalConfig)
    (hneg : (derivIntervalCoreN e ρ_int idx cfg).hi < 0) :
    ∀ x ∈ ρ_int idx,
      Expr.evalAlong e ρ_real idx (ρ_int idx).hi ≤ Expr.evalAlong e ρ_real idx x := by
  have hdiff := evalAlong_differentiable e hsupp ρ_real idx
  have hmono : StrictAntiOn (Expr.evalAlong e ρ_real idx)
      (Set.Icc ((ρ_int idx).lo : ℝ) ((ρ_int idx).hi : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · exact hdiff.continuous.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ ρ_int idx := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      have hmem := evalDualTotalCore_der_correct_idx e hsupp ρ_real ρ_int idx hρ x hx' cfg
      exact lt_of_le_of_lt ((IntervalRat.mem_def _ _).mp hmem).2 (by exact_mod_cast hneg)
  intro x hx
  rcases hx with ⟨hlo, hhi⟩
  by_cases heq : x = ((ρ_int idx).hi : ℝ)
  · exact heq ▸ le_rfl
  · exact le_of_lt (hmono ⟨hlo, hhi⟩
      ⟨by exact_mod_cast (ρ_int idx).le, le_rfl⟩
      (lt_of_le_of_ne hhi heq))

/-- **Main correctness theorem for pruneBoxForMin:**

    After pruning, for any point ρ in the original box B, there exists a point ρ'
    in the pruned box B' such that f(ρ') ≤ f(ρ).

    This means the minimum over B can be found by searching only in B'.

    The proof constructs ρ' by moving each coordinate to its endpoint when the
    gradient has a definite sign. For each coordinate:
    - If ∂f/∂xᵢ > 0 on B, move xᵢ to B[i].lo (f is increasing, min at left)
    - If ∂f/∂xᵢ < 0 on B, move xᵢ to B[i].hi (f is decreasing, min at right)
    - Otherwise, keep xᵢ = ρ[i]

    The proof then shows f(ρ') ≤ f(ρ) by induction on coordinates, using
    the monotonicity lemmas `increasing_min_at_left_idx` and `decreasing_min_at_right_idx`.
-/
private def prunePrefixEnvironment (B : Box) (grad : List IntervalRat) (ρ : Nat → ℝ) :
    Nat → (Nat → ℝ) := fun k j =>
  if h : j < k ∧ j < B.length then
    match grad[j]? with
    | some di =>
      if canPruneToLo di then (B[j].lo : ℝ)
      else if canPruneToHi di then (B[j].hi : ℝ)
      else ρ j
    | none => ρ j
  else if hj : j < B.length then ρ j
  else 0

private theorem prunePrefixEnvironment_mem (B : Box) (grad : List IntervalRat)
    (ρ : Nat → ℝ) (m : ℕ)
    (hρB : Box.envMem ρ B)
    : Box.envMem (prunePrefixEnvironment B grad ρ m) B := by
  let ρ_seq := prunePrefixEnvironment B grad ρ
  intro ⟨j, hj⟩
  simp only [prunePrefixEnvironment]
  by_cases h1 : j < m ∧ j < B.length
  · simp only [dite_eq_left h1]
    cases hgrad_j : grad[j]? with
    | none => exact hρB ⟨j, hj⟩
    | some dj =>
      simp only [IntervalRat.mem_def]
      by_cases hlo_j : canPruneToLo dj
      · simp only [hlo_j, ↓reduceIte]
        exact ⟨le_refl _, by exact_mod_cast B[j].le⟩
      · by_cases hhi_j : canPruneToHi dj
        · simp only [hlo_j, Bool.false_eq_true, ↓reduceIte, hhi_j]
          exact ⟨by exact_mod_cast B[j].le, le_refl _⟩
        · simp only [hlo_j, Bool.false_eq_true, ↓reduceIte, hhi_j]
          exact hρB ⟨j, hj⟩
  · simp only [dite_eq_right h1, dite_eq_left hj]
    exact hρB ⟨j, hj⟩

private theorem prunePrefixEnvironment_zero (B : Box) (grad : List IntervalRat)
    (ρ : Nat → ℝ) (m : ℕ)
    : ∀ j, j ≥ B.length → prunePrefixEnvironment B grad ρ m j = 0 := by
  let ρ_seq := prunePrefixEnvironment B grad ρ
  intro j hjge
  simp only [prunePrefixEnvironment]
  have h1 : ¬(j < m ∧ j < B.length) := fun h => absurd h.2 (not_lt.mpr hjge)
  simp only [dite_eq_right h1]
  have h2 : ¬(j < B.length) := not_lt.mpr hjge
  simp only [dite_eq_right h2]

private theorem prunePrefixEnvironment_step (e : Expr) (hsupp : ADSupported e)
    (B : Box) (cfg : EvalConfig) (ρ : Nat → ℝ) (hρB : Box.envMem ρ B) :
    ∀ m < B.length,
      Expr.eval (prunePrefixEnvironment B (gradientIntervalCore e B cfg) ρ (m + 1)) e ≤
        Expr.eval (prunePrefixEnvironment B (gradientIntervalCore e B cfg) ρ m) e := by
  let grad := gradientIntervalCore e B cfg
  let ρ_seq := prunePrefixEnvironment B grad ρ
  have hρ_seq_step : ∀ k j, k ≠ j → ρ_seq k j = ρ_seq (k + 1) j := by
    intro k j hne
    simp only [ρ_seq, prunePrefixEnvironment]
    by_cases h1 : j < k ∧ j < B.length
    · -- j < k and j < B.length: both difs are positive
      have h2 : j < k + 1 ∧ j < B.length := ⟨Nat.lt_of_lt_of_le h1.1 (Nat.le_succ k), h1.2⟩
      simp only [dite_eq_left h1, dite_eq_left h2]
    · by_cases h2 : j < k + 1 ∧ j < B.length
      · -- j < k + 1 but not (j < k ∧ j < B.length)
        have hj_ge_k : k ≤ j := by
          by_contra! hlt
          exact h1 ⟨hlt, h2.2⟩
        have hj_lt_k1 : j < k + 1 := h2.1
        have hj_eq_k : j = k := Nat.eq_of_le_of_lt_succ hj_ge_k hj_lt_k1
        exact absurd hj_eq_k.symm hne
      · -- Neither condition holds
        simp only [dite_eq_right h1, dite_eq_right h2]
  intro m hm
  change Expr.eval (ρ_seq (m + 1)) e ≤ Expr.eval (ρ_seq m) e
  cases hgrad_m : grad[m]? with
  | none =>
    have heq : ∀ j, ρ_seq (m + 1) j = ρ_seq m j := by
      intro j
      by_cases hj_eq : j = m
      · -- When j = m: both sides simplify to ρ m
        simp only [ρ_seq, prunePrefixEnvironment, hgrad_m, hj_eq]
        have h1 : ¬(m < m ∧ m < B.length) := fun h => Nat.lt_irrefl m h.1
        have h2 : m < m + 1 ∧ m < B.length := ⟨Nat.lt_succ_self m, hm⟩
        simp only [dite_eq_right h1, dite_eq_left h2, dite_eq_left hm]
      · exact (hρ_seq_step m j (Ne.symm hj_eq)).symm
    simp only [funext heq]
    exact le_refl _
  | some di =>
    by_cases hlo : canPruneToLo di
    · -- ∂f/∂x_m > 0, fixing x_m = lo decreases f
      have hcoord_m_before : ρ_seq m m = ρ m := by
        simp only [ρ_seq, prunePrefixEnvironment]
        have h1 : ¬(m < m ∧ m < B.length) := fun h => Nat.lt_irrefl m h.1
        simp only [dite_eq_right h1, dite_eq_left hm]
      have hcoord_m_after : ρ_seq (m + 1) m = B[m].lo := by
        simp only [ρ_seq, prunePrefixEnvironment, hgrad_m, hlo, ↓reduceIte]
        have h2 : m < m + 1 ∧ m < B.length := ⟨Nat.lt_succ_self m, hm⟩
        simp only [dite_eq_left h2]
      have hρ_seq_m_mem := prunePrefixEnvironment_mem B grad ρ m hρB
      have hρ_seq_m_zero := prunePrefixEnvironment_zero B grad ρ m
      have hgrad_di : derivIntervalCoreN e (Box.toEnv B) m cfg = di := by
        simp only [grad, gradientIntervalCore] at hgrad_m
        rw [List.getElem?_map, List.getElem?_range hm] at hgrad_m
        simp only [Option.map_some] at hgrad_m
        exact Option.some.inj hgrad_m
      let ρ_int : IntervalEnv := Box.toEnv B
      have hρ_int : ∀ j, ρ_seq m j ∈ ρ_int j := by
        intro j
        simp only [ρ_int, Box.toEnv, List.getD]
        by_cases hj : j < B.length
        · simp only [List.getElem?_eq_getElem hj, Option.getD]
          exact hρ_seq_m_mem ⟨j, hj⟩
        · simp only [List.getElem?_eq_none (not_lt.mp hj), Option.getD]
          rw [IntervalRat.mem_default]
          exact hρ_seq_m_zero j (not_lt.mp hj)
      have hpos : 0 < (derivIntervalCoreN e ρ_int m cfg).lo := by
        simp only [ρ_int]
        rw [hgrad_di]
        simp only [isStrictlyPositive, canPruneToLo] at hlo
        exact decide_eq_true_iff.mp hlo
      have hmono := increasing_min_at_left_idx_core e hsupp (ρ_seq m) ρ_int m
        hρ_int cfg hpos
      have hρ_m_mem : ρ_seq m m ∈ ρ_int m := hρ_int m
      have hmin := hmono (ρ_seq m m) hρ_m_mem
      have hlo_eq : (ρ_int m).lo = B[m].lo := by
        simp only [ρ_int, Box.toEnv, List.getD, List.getElem?_eq_getElem hm, Option.getD]
      simp only [Expr.evalAlong] at hmin
      have hupdate_self : Expr.updateVar (ρ_seq m) m (ρ_seq m m) = ρ_seq m :=
        Expr.updateVar_self (ρ_seq m) m
      have hρ_seq_update : ρ_seq (m + 1) = Expr.updateVar (ρ_seq m) m (B[m].lo : ℝ) := by
        funext j
        simp only [Expr.updateVar]
        by_cases hj_eq : j = m
        · subst hj_eq
          simp only [↓reduceIte]
          exact hcoord_m_after
        · simp only [ite_eq_right hj_eq]
          exact (hρ_seq_step m j (Ne.symm hj_eq)).symm
      have hupdate_lo : Expr.updateVar (ρ_seq m) m ((ρ_int m).lo : ℝ) = ρ_seq (m + 1) := by
        rw [hlo_eq, ← hρ_seq_update]
      rw [hupdate_lo, hupdate_self] at hmin
      exact hmin
    · by_cases hhi : canPruneToHi di
      · -- ∂f/∂x_m < 0, fixing x_m = hi decreases f
        have hcoord_m_before : ρ_seq m m = ρ m := by
          simp only [ρ_seq, prunePrefixEnvironment]
          have h1 : ¬(m < m ∧ m < B.length) := fun h => Nat.lt_irrefl m h.1
          simp only [dite_eq_right h1, dite_eq_left hm]
        have hcoord_m_after : ρ_seq (m + 1) m = B[m].hi := by
          simp only [ρ_seq, prunePrefixEnvironment, hgrad_m, hlo, Bool.false_eq_true,
            ↓reduceIte, hhi]
          have h2 : m < m + 1 ∧ m < B.length := ⟨Nat.lt_succ_self m, hm⟩
          simp only [dite_eq_left h2]
        have hρ_seq_m_mem := prunePrefixEnvironment_mem B grad ρ m hρB
        have hρ_seq_m_zero := prunePrefixEnvironment_zero B grad ρ m
        have hgrad_di : derivIntervalCoreN e (Box.toEnv B) m cfg = di := by
          simp only [grad, gradientIntervalCore] at hgrad_m
          rw [List.getElem?_map, List.getElem?_range hm] at hgrad_m
          simp only [Option.map_some] at hgrad_m
          exact Option.some.inj hgrad_m
        let ρ_int : IntervalEnv := Box.toEnv B
        have hρ_int : ∀ j, ρ_seq m j ∈ ρ_int j := by
          intro j
          simp only [ρ_int, Box.toEnv, List.getD]
          by_cases hj : j < B.length
          · simp only [List.getElem?_eq_getElem hj, Option.getD]
            exact hρ_seq_m_mem ⟨j, hj⟩
          · simp only [List.getElem?_eq_none (not_lt.mp hj), Option.getD]
            rw [IntervalRat.mem_default]
            exact hρ_seq_m_zero j (not_lt.mp hj)
        have hneg : (derivIntervalCoreN e ρ_int m cfg).hi < 0 := by
          simp only [ρ_int]
          rw [hgrad_di]
          simp only [isStrictlyNegative, canPruneToHi] at hhi
          exact decide_eq_true_iff.mp hhi
        have hmono := decreasing_min_at_right_idx_core e hsupp (ρ_seq m) ρ_int m
          hρ_int cfg hneg
        have hρ_m_mem : ρ_seq m m ∈ ρ_int m := hρ_int m
        have hmin := hmono (ρ_seq m m) hρ_m_mem
        have hhi_eq : (ρ_int m).hi = B[m].hi := by
          simp only [ρ_int, Box.toEnv, List.getD, List.getElem?_eq_getElem hm, Option.getD]
        simp only [Expr.evalAlong] at hmin
        have hupdate_self : Expr.updateVar (ρ_seq m) m (ρ_seq m m) = ρ_seq m :=
          Expr.updateVar_self (ρ_seq m) m
        have hρ_seq_update : ρ_seq (m + 1) = Expr.updateVar (ρ_seq m) m (B[m].hi : ℝ) := by
          funext j
          simp only [Expr.updateVar]
          by_cases hj_eq : j = m
          · subst hj_eq
            simp only [↓reduceIte]
            exact hcoord_m_after
          · simp only [ite_eq_right hj_eq]
            exact (hρ_seq_step m j (Ne.symm hj_eq)).symm
        have hupdate_hi : Expr.updateVar (ρ_seq m) m ((ρ_int m).hi : ℝ) = ρ_seq (m + 1) := by
          rw [hhi_eq, ← hρ_seq_update]
        rw [hupdate_hi, hupdate_self] at hmin
        exact hmin
      · -- No pruning at coord m: ρ_seq (m+1) = ρ_seq m at all coords
        have heq : ∀ j, ρ_seq (m + 1) j = ρ_seq m j := by
          intro j
          by_cases hj_eq : j = m
          · -- When j = m: need ρ_seq (m+1) m = ρ_seq m m
            simp only [ρ_seq, prunePrefixEnvironment, hgrad_m, hlo, Bool.false_eq_true,
              ↓reduceIte, hhi, hj_eq]
            have h1 : ¬(m < m ∧ m < B.length) := fun h => Nat.lt_irrefl m h.1
            have h2 : m < m + 1 ∧ m < B.length := ⟨Nat.lt_succ_self m, hm⟩
            simp only [dite_eq_right h1, dite_eq_left h2, dite_eq_left hm]
          · exact (hρ_seq_step m j (Ne.symm hj_eq)).symm
        simp only [funext heq]
        exact le_refl _

theorem pruneBoxForMin_correct (e : Expr) (hsupp : ADSupported e) (B : Box)
    (cfg : EvalConfig := {}) :
    let grad := gradientIntervalCore e B cfg
    let B' := (pruneBoxForMin B grad).1
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      ∃ (ρ' : Nat → ℝ), Box.envMem ρ' B' ∧ (∀ i, i ≥ B'.length → ρ' i = 0) ∧
        Expr.eval ρ' e ≤ Expr.eval ρ e := by
  intro grad B' ρ hρB hzero
  let ρ' : Nat → ℝ := fun j =>
    if h : j < B.length then
      match grad[j]? with
      | some di =>
        if canPruneToLo di then (B[j].lo : ℝ)
        else if canPruneToHi di then (B[j].hi : ℝ)
        else ρ j
      | none => ρ j
    else 0
  use ρ'
  constructor
  · -- ρ' ∈ B'
    intro ⟨j, hj'⟩
    have hB'_len : B'.length = B.length := pruneBoxForMin_length B grad
    have hj : j < B.length := by rw [← hB'_len]; exact hj'
    simp only [ρ', hj, ↓reduceDIte]
    simp only [B', pruneBoxForMin]
    rw [List.getElem_map, List.getElem_map]
    have h_zipIdx_len : j < (B.zipIdx).length := by simp only [List.length_zipIdx]; exact hj
    have h_zipIdx : (B.zipIdx)[j] = (B[j], j) := by
      rw [List.getElem_zipIdx (h := h_zipIdx_len)]
      simp only [Nat.zero_add]
    simp only [h_zipIdx]
    cases hgrad_j : grad[j]? with
    | none =>
      simp only [IntervalRat.mem_def]
      exact hρB ⟨j, hj⟩
    | some di =>
      simp only [IntervalRat.mem_def]
      by_cases hlo : canPruneToLo di
      · simp only [hlo, ↓reduceIte]
        exact IntervalRat.mem_singleton _
      · by_cases hhi : canPruneToHi di
        · simp only [hlo, Bool.false_eq_true, ↓reduceIte, hhi]
          exact IntervalRat.mem_singleton _
        · simp only [hlo, Bool.false_eq_true, ↓reduceIte, hhi]
          exact hρB ⟨j, hj⟩
  constructor
  · -- ρ' i = 0 for i ≥ B'.length
    intro i hi
    have hB'_len : B'.length = B.length := pruneBoxForMin_length B grad
    rw [hB'_len] at hi
    simp only [ρ', not_lt.mpr hi, ↓reduceDIte]
  · -- f(ρ') ≤ f(ρ)
    let ρ_seq := prunePrefixEnvironment B grad ρ
    have hρ_seq_zero : ∀ j, ρ_seq 0 j = if j < B.length then ρ j else 0 := by
      intro j
      simp only [ρ_seq, prunePrefixEnvironment]
      have h_neg : ¬(j < 0 ∧ j < B.length) := fun h => Nat.not_lt_zero j h.1
      simp only [dite_eq_right h_neg]
      split_ifs <;> rfl
    have hρ_seq_final : ∀ j, ρ_seq B.length j = ρ' j := by
      intro j
      simp only [ρ_seq, prunePrefixEnvironment, ρ']
      by_cases hj : j < B.length
      · -- j < B.length
        have h_and : j < B.length ∧ j < B.length := ⟨hj, hj⟩
        simp only [dite_eq_left h_and, dite_eq_left hj]
      · -- j ≥ B.length
        have h_nand : ¬(j < B.length ∧ j < B.length) := fun h => hj h.2
        simp only [dite_eq_right h_nand, dite_eq_right hj]
    have hstep := prunePrefixEnvironment_step e hsupp B cfg ρ hρB
    have hchain : ∀ n ≤ B.length, Expr.eval (ρ_seq n) e ≤ Expr.eval (ρ_seq 0) e := by
      intro n hn
      induction n with
      | zero => exact le_refl _
      | succ m ih =>
        have hm_lt : m < B.length := Nat.lt_of_succ_le hn
        calc Expr.eval (ρ_seq (m + 1)) e ≤ Expr.eval (ρ_seq m) e := hstep m hm_lt
          _ ≤ Expr.eval (ρ_seq 0) e := ih (Nat.le_of_lt hm_lt)
    have hfinal_eq : Expr.eval (ρ_seq B.length) e = Expr.eval ρ' e := by
      congr 1; funext j; exact hρ_seq_final j
    have hρ_seq0_eq : Expr.eval (ρ_seq 0) e = Expr.eval ρ e := by
      congr 1
      funext j
      rw [hρ_seq_zero]
      split_ifs with hj
      · rfl
      · exact (hzero j (not_lt.mp hj)).symm
    rw [← hfinal_eq, ← hρ_seq0_eq]
    exact hchain B.length (le_refl _)

end LeanCert.Engine.Optimization
