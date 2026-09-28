/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Engine.AD
public import Mathlib.Analysis.Calculus.MeanValue
/-!
# Global Optimization via Branch-and-Bound

This file implements verified global optimization over intervals using
branch-and-bound with interval arithmetic and derivative bounds.

## Phase Status

**This module is now largely Phase 1 (verified).** The core correctness theorems
are fully proved for the ADSupported subset.

## Main definitions

* `minimizeInterval` - Find a lower bound on min f over an interval
* `maximizeInterval` - Find an upper bound on max f over an interval
* Correctness theorems (fully proved for ADSupported)

## Algorithm

Branch-and-bound with the following pruning rules:
1. **Interval evaluation**: If f([a,b]) = [lo, hi], then min f ≥ lo
2. **Monotonicity**: If f'([a,b]) > 0, f is increasing, so min is at a
3. **Subdivision**: Split interval and recurse

-/

/-! ### Optimization result -/

@[expose] public section

namespace LeanCert.Engine

open LeanCert.Core

/-- Result of an optimization computation -/
structure OptResult where
  /-- Interval containing the optimum value -/
  valueBound : IntervalRat
  /-- Interval containing an optimizing point (if found) -/
  argBound : Option IntervalRat
  /-- Depth of search performed -/
  depth : ℕ

/-- Combine two subinterval bounds, preserving their lower and upper bounds. -/
noncomputable def OptResult.merge (r₁ r₂ : OptResult) : OptResult :=
  if h : r₁.valueBound.lo ≤ r₂.valueBound.lo then
    { valueBound :=
        { lo := r₁.valueBound.lo
          hi := min r₁.valueBound.hi r₂.valueBound.hi
          le := by
            apply le_min
            · exact r₁.valueBound.le
            · calc r₁.valueBound.lo ≤ r₂.valueBound.lo := h
                _ ≤ r₂.valueBound.hi := r₂.valueBound.le }
      argBound := r₁.argBound
      depth := max r₁.depth r₂.depth }
  else
    { valueBound :=
        { lo := r₂.valueBound.lo
          hi := min r₁.valueBound.hi r₂.valueBound.hi
          le := by
            apply le_min
            · calc r₂.valueBound.lo ≤ r₁.valueBound.lo := le_of_lt (not_le.mp h)
                _ ≤ r₁.valueBound.hi := r₁.valueBound.le
            · exact r₂.valueBound.le }
      argBound := r₂.argBound
      depth := max r₁.depth r₂.depth }

/-! ### Minimization -/

/-- Check if derivative interval is strictly positive -/
noncomputable def derivStrictlyPositive (e : Expr) (I : IntervalRat) (varIdx : Nat) : Bool :=
  let dI := derivInterval e (fun _ => I) varIdx
  0 < dI.lo

/-- Check if derivative interval is strictly negative -/
noncomputable def derivStrictlyNegative (e : Expr) (I : IntervalRat) (varIdx : Nat) : Bool :=
  let dI := derivInterval e (fun _ => I) varIdx
  dI.hi < 0

/-- Simple branch-and-bound minimization.

Returns an interval [lo, hi] such that:
- lo ≤ min_{x ∈ I} f(x)
- hi ≥ min_{x ∈ I} f(x)
-/
noncomputable def minimizeInterval (e : Expr) (I : IntervalRat) (varIdx : Nat)
    (maxDepth : ℕ) : OptResult :=
  go I maxDepth
where
  /-- Recursive interval minimization with a decreasing subdivision budget. -/
  go (J : IntervalRat) (depth : ℕ) : OptResult :=
    if depth = 0 then
      -- Base case: just use interval evaluation
      { valueBound := LeanCert.Internal.Rational.evalUnchecked1 e J
        argBound := some J
        depth := maxDepth }
    else
      -- Check monotonicity
      if derivStrictlyPositive e J varIdx then
        -- f is increasing, minimum is at left endpoint
        { valueBound := LeanCert.Internal.Rational.evalUnchecked1 e (IntervalRat.singleton J.lo)
          argBound := some (IntervalRat.singleton J.lo)
          depth := maxDepth - depth }
      else if derivStrictlyNegative e J varIdx then
        -- f is decreasing, minimum is at right endpoint
        { valueBound := LeanCert.Internal.Rational.evalUnchecked1 e (IntervalRat.singleton J.hi)
          argBound := some (IntervalRat.singleton J.hi)
          depth := maxDepth - depth }
      else
        -- Bisect and take the better bound
        let (J₁, J₂) := J.bisect
        let r₁ := go J₁ (depth - 1)
        let r₂ := go J₂ (depth - 1)
        OptResult.merge r₁ r₂
  termination_by depth
  decreasing_by all_goals omega

/-- Base case correctness: interval evaluation gives a valid lower bound.
    This theorem is FULLY PROVED - no sorry, no axioms. -/
theorem minimizeInterval_base_correct (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) :
    ∀ x ∈ I, (LeanCert.Internal.Rational.evalUnchecked1 e I).lo ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have h := evalInterval1_correct e hsupp x I hx
  simp only [IntervalRat.mem_def] at h
  exact h.1

/-! ### Derivative bounds and monotonicity -/

/-- For single-variable expressions evaluated with (fun _ => I), derivative is correct.
    We use evalWithDeriv1 which directly uses varActive for all variables. -/
theorem derivInterval_correct_evalWithDeriv1 (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    deriv (evalFunc1 e) x ∈ (evalWithDeriv1 e I).der := by
  -- evalWithDeriv1 e I = LeanCert.Internal.AD.evalUnchecked e (fun _ => DualInterval.varActive I)
  -- This matches exactly what LeanCert.Engine.evalDualUnchecked_der_correct expects
  simp only [evalWithDeriv1]
  exact LeanCert.Engine.evalDualUnchecked_der_correct e hsupp I x hx

/-- Derivative is in derivInterval for expressions that only use var 0.
    FULLY PROVED - no sorry. -/
theorem derivInterval_correct_single (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    deriv (evalFunc1 e) x ∈ derivInterval e (fun _ => I) 0 := by
  rw [derivInterval_eq_evalWithDeriv1_of_UsesOnlyVar0 e hvar0]
  exact derivInterval_correct_evalWithDeriv1 e hsupp I x hx

/-- If the derivative interval is strictly positive, derivative is positive everywhere -/
theorem deriv_pos_on_interval (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (hpos : 0 < (derivInterval e (fun _ => I) 0).lo) :
    ∀ x ∈ I, 0 < deriv (evalFunc1 e) x := by
  intro x hx
  have hmem := derivInterval_correct_single e hsupp hvar0 I x hx
  simp only [IntervalRat.mem_def] at hmem
  have hlo_cast : (0 : ℝ) < ((derivInterval e (fun _ => I) 0).lo : ℝ) := by exact_mod_cast hpos
  calc (0 : ℝ) < ((derivInterval e (fun _ => I) 0).lo : ℝ) := hlo_cast
    _ ≤ deriv (evalFunc1 e) x := hmem.1

/-- If the derivative interval is strictly negative, derivative is negative everywhere -/
theorem deriv_neg_on_interval (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (hneg : (derivInterval e (fun _ => I) 0).hi < 0) :
    ∀ x ∈ I, deriv (evalFunc1 e) x < 0 := by
  intro x hx
  have hmem := derivInterval_correct_single e hsupp hvar0 I x hx
  simp only [IntervalRat.mem_def] at hmem
  have hhi_cast : ((derivInterval e (fun _ => I) 0).hi : ℝ) < (0 : ℝ) := by exact_mod_cast hneg
  calc deriv (evalFunc1 e) x ≤ ((derivInterval e (fun _ => I) 0).hi : ℝ) := hmem.2
    _ < 0 := hhi_cast

/-- Strictly positive derivative implies strict monotonicity -/
theorem strictMonoOn_of_deriv_pos_interval (e : Expr) (hsupp : ADSupported e) (hvar0 :
  UsesOnlyVar0 e)
    (I : IntervalRat) (hpos : 0 < (derivInterval e (fun _ => I) 0).lo) :
    StrictMonoOn (evalFunc1 e) (Set.Icc (I.lo : ℝ) (I.hi : ℝ)) := by
  have hdiff := evalFunc1_differentiable e hsupp
  have hderiv_pos := deriv_pos_on_interval e hsupp hvar0 I hpos
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    -- Interior of Icc is Ioo, and Ioo ⊆ Icc
    rw [interior_Icc] at hx
    have hx_mem : x ∈ I := by
      simp only [IntervalRat.mem_def]
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact hderiv_pos x hx_mem

/-- Strictly negative derivative implies strict antitonicity -/
theorem strictAntiOn_of_deriv_neg_interval (e : Expr) (hsupp : ADSupported e) (hvar0 :
  UsesOnlyVar0 e)
    (I : IntervalRat) (hneg : (derivInterval e (fun _ => I) 0).hi < 0) :
    StrictAntiOn (evalFunc1 e) (Set.Icc (I.lo : ℝ) (I.hi : ℝ)) := by
  have hdiff := evalFunc1_differentiable e hsupp
  have hderiv_neg := deriv_neg_on_interval e hsupp hvar0 I hneg
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    -- Interior of Icc is Ioo
    rw [interior_Icc] at hx
    have hx_mem : x ∈ I := by
      simp only [IntervalRat.mem_def]
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact hderiv_neg x hx_mem

/-! ### Monotonicity-based bounds -/

/-- For increasing functions, minimum is at the left endpoint -/
theorem increasing_min_at_left (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (hpos : 0 < (derivInterval e (fun _ => I) 0).lo) :
    ∀ x ∈ I, evalFunc1 e I.lo ≤ evalFunc1 e x := by
  intro x hx
  have hmono := strictMonoOn_of_deriv_pos_interval e hsupp hvar0 I hpos
  simp only [IntervalRat.mem_def] at hx
  by_cases heq : (I.lo : ℝ) = x
  · rw [heq]
  · apply le_of_lt
    apply hmono
    · simp only [Set.mem_Icc]
      exact ⟨le_refl _, Rat.cast_le.mpr I.le⟩
    · simp only [Set.mem_Icc]; exact hx
    · exact lt_of_le_of_ne hx.1 heq

/-- For decreasing functions, minimum is at the right endpoint -/
theorem decreasing_min_at_right (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (hneg : (derivInterval e (fun _ => I) 0).hi < 0) :
    ∀ x ∈ I, evalFunc1 e I.hi ≤ evalFunc1 e x := by
  intro x hx
  have hmono := strictAntiOn_of_deriv_neg_interval e hsupp hvar0 I hneg
  simp only [IntervalRat.mem_def] at hx
  by_cases heq : x = (I.hi : ℝ)
  · rw [heq]
  · apply le_of_lt
    apply hmono
    · simp only [Set.mem_Icc]; exact hx
    · simp only [Set.mem_Icc]; exact ⟨(Rat.cast_le.mpr I.le), le_refl _⟩
    · exact lt_of_le_of_ne hx.2 heq

/-- Interval at left endpoint gives valid lower bound for increasing functions -/
theorem increasing_endpoint_bound (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (hpos : 0 < (derivInterval e (fun _ => I) 0).lo) :
    ∀ x ∈ I, (LeanCert.Internal.Rational.evalUnchecked1 e (IntervalRat.singleton I.lo)).lo ≤
      Expr.eval (fun _ => x) e := by
  intro x hx
  have hlo_mem : (I.lo : ℝ) ∈ IntervalRat.singleton I.lo := IntervalRat.mem_singleton I.lo
  have heval := evalInterval1_correct e hsupp I.lo (IntervalRat.singleton I.lo) hlo_mem
  simp only [IntervalRat.mem_def] at heval
  have hmin := increasing_min_at_left e hsupp hvar0 I hpos x hx
  simp only [evalFunc1] at hmin
  calc (LeanCert.Internal.Rational.evalUnchecked1 e (IntervalRat.singleton I.lo)).lo
      ≤ Expr.eval (fun _ => I.lo) e := by exact_mod_cast heval.1
    _ ≤ Expr.eval (fun _ => x) e := hmin

/-- Interval at right endpoint gives valid lower bound for decreasing functions -/
theorem decreasing_endpoint_bound (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (hneg : (derivInterval e (fun _ => I) 0).hi < 0) :
    ∀ x ∈ I, (LeanCert.Internal.Rational.evalUnchecked1 e (IntervalRat.singleton I.hi)).lo ≤
      Expr.eval (fun _ => x) e := by
  intro x hx
  have hhi_mem : (I.hi : ℝ) ∈ IntervalRat.singleton I.hi := IntervalRat.mem_singleton I.hi
  have heval := evalInterval1_correct e hsupp I.hi (IntervalRat.singleton I.hi) hhi_mem
  simp only [IntervalRat.mem_def] at heval
  have hmin := decreasing_min_at_right e hsupp hvar0 I hneg x hx
  simp only [evalFunc1] at hmin
  calc (LeanCert.Internal.Rational.evalUnchecked1 e (IntervalRat.singleton I.hi)).lo
      ≤ Expr.eval (fun _ => I.hi) e := by exact_mod_cast heval.1
    _ ≤ Expr.eval (fun _ => x) e := hmin

/-! ### Full optimization correctness -/

/-- Helper lemma for go correctness.
    FULLY PROVED for varIdx = 0 and UsesOnlyVar0 expressions. -/
theorem minimizeInterval_go_correct (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (maxDepth : ℕ) (depth : ℕ) (J : IntervalRat) :
    ∀ x ∈ J, (minimizeInterval.go e 0 maxDepth J depth).valueBound.lo
             ≤ Expr.eval (fun _ => x) e := by
  induction depth generalizing J with
  | zero =>
    -- Base case: depth = 0, just use interval evaluation
    intro x hx
    simp only [minimizeInterval.go, ↓reduceIte]
    exact minimizeInterval_base_correct e hsupp J x hx
  | succ n ih =>
    intro x hx
    -- Unfold the go definition for succ case
    -- Note: n + 1 ≠ 0, so we skip the first branch
    have hdepth : n + 1 ≠ 0 := Nat.succ_ne_zero n
    rw [minimizeInterval.go]
    simp only [hdepth, ↓reduceIte, OptResult.merge, Nat.add_sub_cancel]
    -- Now we branch on the derivative conditions
    split_ifs with hpos hneg hle
    · -- Derivative strictly positive: increasing function
      have hpos' : 0 < (derivInterval e (fun _ => J) 0).lo := by
        simp only [derivStrictlyPositive, decide_eq_true_eq] at hpos
        exact hpos
      exact increasing_endpoint_bound e hsupp hvar0 J hpos' x hx
    · -- Derivative strictly negative: decreasing function
      have hneg' : (derivInterval e (fun _ => J) 0).hi < 0 := by
        simp only [derivStrictlyNegative, decide_eq_true_eq] at hneg
        exact hneg
      exact decreasing_endpoint_bound e hsupp hvar0 J hneg' x hx
    · -- Bisection case, hle (r₁.lo ≤ r₂.lo)
      -- x is in one of the bisected intervals
      have hcases := IntervalRat.mem_bisect_or hx
      cases hcases with
      | inl h1 => exact ih J.bisect.1 x h1
      | inr h2 =>
        have h := ih J.bisect.2 x h2
        have hle_cast : ((minimizeInterval.go e 0 maxDepth (J.bisect.fst) n).valueBound.lo : ℝ)
            ≤ (minimizeInterval.go e 0 maxDepth (J.bisect.snd) n).valueBound.lo := by
              exact_mod_cast hle
        calc ((minimizeInterval.go e 0 maxDepth (J.bisect.fst) n).valueBound.lo : ℝ)
            ≤ (minimizeInterval.go e 0 maxDepth (J.bisect.snd) n).valueBound.lo := hle_cast
          _ ≤ Expr.eval (fun _ => x) e := h
    · -- Bisection case, ¬hle (r₁.lo > r₂.lo)
      have hcases := IntervalRat.mem_bisect_or hx
      cases hcases with
      | inl h1 =>
        have h := ih J.bisect.1 x h1
        have hlt := not_le.mp hle
        have hlt_cast : ((minimizeInterval.go e 0 maxDepth (J.bisect.snd) n).valueBound.lo : ℝ)
            ≤ (minimizeInterval.go e 0 maxDepth (J.bisect.fst) n).valueBound.lo := by
              exact_mod_cast (le_of_lt hlt)
        calc ((minimizeInterval.go e 0 maxDepth (J.bisect.snd) n).valueBound.lo : ℝ)
            ≤ (minimizeInterval.go e 0 maxDepth (J.bisect.fst) n).valueBound.lo := hlt_cast
          _ ≤ Expr.eval (fun _ => x) e := h
      | inr h2 => exact ih J.bisect.2 x h2

/-- Correctness: the minimum is in the computed interval.
    FULLY PROVED for varIdx = 0 and UsesOnlyVar0 expressions. -/
theorem minimizeInterval_correct (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat)
    (maxDepth : ℕ) :
    ∀ x ∈ I, (minimizeInterval e I 0 maxDepth).valueBound.lo ≤ Expr.eval (fun _ => x) e := by
  simp only [minimizeInterval]
  exact minimizeInterval_go_correct e hsupp hvar0 maxDepth maxDepth I

/-! ### Maximization -/

/-- Maximize by minimizing the negation -/
noncomputable def maximizeInterval (e : Expr) (I : IntervalRat) (varIdx : Nat)
    (maxDepth : ℕ) : OptResult :=
  let negResult := minimizeInterval (Expr.neg e) I varIdx maxDepth
  { valueBound := IntervalRat.neg negResult.valueBound
    argBound := negResult.argBound
    depth := negResult.depth }

/-- Correctness: the maximum is in the computed interval.
    FULLY PROVED for varIdx = 0 and UsesOnlyVar0 expressions. -/
theorem maximizeInterval_correct (e : Expr) (hsupp : ADSupported e) (hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat)
    (maxDepth : ℕ) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ (maximizeInterval e I 0 maxDepth).valueBound.hi := by
  intro x hx
  -- max f = -min(-f)
  -- result.valueBound = neg (minimizeInterval (neg e) ...).valueBound
  -- result.valueBound.hi = -(minimizeInterval (neg e) ...).valueBound.lo
  -- We need: f(x) ≤ result.valueBound.hi
  --        = -(minimizeInterval (neg e) ...).valueBound.lo
  -- Equivalently: (minimizeInterval (neg e) ...).valueBound.lo ≤ -f(x)
  have hneg_supp : ADSupported (Expr.neg e) := ADSupported.neg hsupp
  have hneg_var0 : UsesOnlyVar0 (Expr.neg e) := UsesOnlyVar0.neg e hvar0
  have hmin := minimizeInterval_correct (Expr.neg e) hneg_supp hneg_var0 I maxDepth x hx
  simp only [Expr.eval_neg] at hmin
  -- hmin: (minimizeInterval (neg e) ...).valueBound.lo ≤ -f(x)
  -- Need: f(x) ≤ (maximizeInterval e ...).valueBound.hi
  --     = -(minimizeInterval (neg e) ...).valueBound.lo
  simp only [maximizeInterval, IntervalRat.neg]
  -- Goal: f(x) ≤ ↑(-(minimizeInterval (neg e) ...).valueBound.lo)
  -- From hmin: ↑(minimizeInterval (neg e) ...).valueBound.lo ≤ -f(x)
  -- So: f(x) ≤ -(minimizeInterval (neg e) ...).valueBound.lo
  have h : Expr.eval (fun _ => x) e ≤
           -(((minimizeInterval (Expr.neg e) I 0 maxDepth).valueBound.lo) : ℝ) := by
    have hcast : (((minimizeInterval (Expr.neg e) I 0 maxDepth).valueBound.lo) : ℝ)
                 ≤ -Expr.eval (fun _ => x) e := hmin
    linarith
  convert h using 1
  -- Need: ↑(-(minimizeInterval e.neg I 0 maxDepth).valueBound.lo) =
  --       -↑(minimizeInterval e.neg I 0 maxDepth).valueBound.lo
  simp only [Rat.cast_neg]

/-! ### Bounds checking -/

/-- Check if f(x) ≥ c for all x in I -/
noncomputable def checkLowerBound (e : Expr) (I : IntervalRat) (c : ℚ) (varIdx : Nat)
    (maxDepth : ℕ) : Bool :=
  let result := minimizeInterval e I varIdx maxDepth
  c ≤ result.valueBound.lo

/-- Check if f(x) ≤ c for all x in I -/
noncomputable def checkUpperBound (e : Expr) (I : IntervalRat) (c : ℚ) (varIdx : Nat)
    (maxDepth : ℕ) : Bool :=
  let result := maximizeInterval e I varIdx maxDepth
  result.valueBound.hi ≤ c

/-! ## N-Variable Optimization Infrastructure

The following section provides generalized optimization infrastructure that works
with arbitrary variable indices and multi-variable environments. This allows
optimizing along any coordinate while holding other variables fixed.

Key types:
- `IntervalEnv := Nat → IntervalRat` - maps variable indices to intervals
- `evalAlong e ρ idx` - evaluates `e` as a function of variable `idx`

The main advantage is that we can now optimize expressions with multiple variables
by fixing all but one variable and optimizing along that coordinate.
-/

/-! ### N-variable derivative bounds -/

/-- If the derivative interval along `idx` is strictly positive, derivative is positive everywhere.
    Generalized version that works with any variable index and environment. -/
theorem deriv_pos_on_interval_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (hpos : 0 < (derivInterval e ρ_int idx).lo) :
    ∀ x ∈ ρ_int idx, 0 < deriv (Expr.evalAlong e ρ_real idx) x := by
  intro x hx
  have hmem := derivInterval_correct_idx e hsupp ρ_real ρ_int idx hρ x hx
  simp only [IntervalRat.mem_def] at hmem
  have hlo_cast : (0 : ℝ) < ((derivInterval e ρ_int idx).lo : ℝ) := by exact_mod_cast hpos
  calc (0 : ℝ) < ((derivInterval e ρ_int idx).lo : ℝ) := hlo_cast
    _ ≤ deriv (Expr.evalAlong e ρ_real idx) x := hmem.1

/-- If the derivative interval along `idx` is strictly negative, derivative is negative everywhere.
    Generalized version that works with any variable index and environment. -/
theorem deriv_neg_on_interval_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (hneg : (derivInterval e ρ_int idx).hi < 0) :
    ∀ x ∈ ρ_int idx, deriv (Expr.evalAlong e ρ_real idx) x < 0 := by
  intro x hx
  have hmem := derivInterval_correct_idx e hsupp ρ_real ρ_int idx hρ x hx
  simp only [IntervalRat.mem_def] at hmem
  have hhi_cast : ((derivInterval e ρ_int idx).hi : ℝ) < (0 : ℝ) := by exact_mod_cast hneg
  calc deriv (Expr.evalAlong e ρ_real idx) x ≤ ((derivInterval e ρ_int idx).hi : ℝ) := hmem.2
    _ < 0 := hhi_cast

/-- Strictly positive derivative along `idx` implies strict monotonicity.
    Generalized n-variable version. -/
theorem strictMonoOn_of_deriv_pos_interval_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (hpos : 0 < (derivInterval e ρ_int idx).lo) :
    StrictMonoOn (Expr.evalAlong e ρ_real idx)
      (Set.Icc ((ρ_int idx).lo : ℝ) ((ρ_int idx).hi : ℝ)) := by
  have hdiff := evalAlong_differentiable e hsupp ρ_real idx
  have hderiv_pos := deriv_pos_on_interval_idx e hsupp ρ_real ρ_int idx hρ hpos
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx_mem : x ∈ ρ_int idx := by
      simp only [IntervalRat.mem_def]
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact hderiv_pos x hx_mem

/-- Strictly negative derivative along `idx` implies strict antitonicity.
    Generalized n-variable version. -/
theorem strictAntiOn_of_deriv_neg_interval_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (hneg : (derivInterval e ρ_int idx).hi < 0) :
    StrictAntiOn (Expr.evalAlong e ρ_real idx)
      (Set.Icc ((ρ_int idx).lo : ℝ) ((ρ_int idx).hi : ℝ)) := by
  have hdiff := evalAlong_differentiable e hsupp ρ_real idx
  have hderiv_neg := deriv_neg_on_interval_idx e hsupp ρ_real ρ_int idx hρ hneg
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx_mem : x ∈ ρ_int idx := by
      simp only [IntervalRat.mem_def]
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact hderiv_neg x hx_mem

/-! ### N-variable monotonicity-based bounds -/

/-- For increasing functions along `idx`, minimum is at the left endpoint.
    Generalized n-variable version. -/
theorem increasing_min_at_left_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (hpos : 0 < (derivInterval e ρ_int idx).lo) :
    ∀ x ∈ ρ_int idx,
      Expr.evalAlong e ρ_real idx (ρ_int idx).lo ≤ Expr.evalAlong e ρ_real idx x := by
  intro x hx
  have hmono := strictMonoOn_of_deriv_pos_interval_idx e hsupp ρ_real ρ_int idx hρ hpos
  simp only [IntervalRat.mem_def] at hx
  by_cases heq : ((ρ_int idx).lo : ℝ) = x
  · rw [heq]
  · apply le_of_lt
    apply hmono
    · simp only [Set.mem_Icc]
      exact ⟨le_refl _, Rat.cast_le.mpr (ρ_int idx).le⟩
    · simp only [Set.mem_Icc]; exact hx
    · exact lt_of_le_of_ne hx.1 heq

/-- For decreasing functions along `idx`, minimum is at the right endpoint.
    Generalized n-variable version. -/
theorem decreasing_min_at_right_idx (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (hneg : (derivInterval e ρ_int idx).hi < 0) :
    ∀ x ∈ ρ_int idx,
      Expr.evalAlong e ρ_real idx (ρ_int idx).hi ≤ Expr.evalAlong e ρ_real idx x := by
  intro x hx
  have hmono := strictAntiOn_of_deriv_neg_interval_idx e hsupp ρ_real ρ_int idx hρ hneg
  simp only [IntervalRat.mem_def] at hx
  by_cases heq : x = ((ρ_int idx).hi : ℝ)
  · rw [heq]
  · apply le_of_lt
    apply hmono
    · simp only [Set.mem_Icc]; exact hx
    · simp only [Set.mem_Icc]; exact ⟨(Rat.cast_le.mpr (ρ_int idx).le), le_refl _⟩
    · exact lt_of_le_of_ne hx.2 heq

/-! ### N-variable minimization algorithm -/

/-- Check if derivative interval along `idx` is strictly positive -/
noncomputable def derivStrictlyPositiveIdx (e : Expr) (ρ : IntervalEnv) (idx : Nat) : Bool :=
  let dI := derivInterval e ρ idx
  0 < dI.lo

/-- Check if derivative interval along `idx` is strictly negative -/
noncomputable def derivStrictlyNegativeIdx (e : Expr) (ρ : IntervalEnv) (idx : Nat) : Bool :=
  let dI := derivInterval e ρ idx
  dI.hi < 0

/-- Update an interval environment at a specific index -/
def updateIntervalEnv (ρ : IntervalEnv) (idx : Nat) (J : IntervalRat) : IntervalEnv :=
  fun i => if i = idx then J else ρ i

/-- N-variable branch-and-bound minimization along coordinate `idx`.

Returns an interval [lo, hi] such that for any ρ_real with ρ_real i ∈ ρ i:
- lo ≤ min_{t ∈ ρ idx} evalAlong e ρ_real idx t
- hi ≥ min_{t ∈ ρ idx} evalAlong e ρ_real idx t
-/
noncomputable def minimizeIntervalIdx (e : Expr) (ρ : IntervalEnv) (idx : Nat)
    (maxDepth : ℕ) : OptResult :=
  go (ρ idx) maxDepth
where
  /-- Recursive coordinate minimization with a decreasing subdivision budget. -/
  go (J : IntervalRat) (depth : ℕ) : OptResult :=
    let ρ' := updateIntervalEnv ρ idx J
    if depth = 0 then
      -- Base case: just use interval evaluation
      { valueBound := LeanCert.Internal.Rational.evalUnchecked e ρ'
        argBound := some J
        depth := maxDepth }
    else
      -- Check monotonicity along idx
      if derivStrictlyPositiveIdx e ρ' idx then
        -- f is increasing along idx, minimum is at left endpoint
        let ρ_lo := updateIntervalEnv ρ idx (IntervalRat.singleton J.lo)
        { valueBound := LeanCert.Internal.Rational.evalUnchecked e ρ_lo
          argBound := some (IntervalRat.singleton J.lo)
          depth := maxDepth - depth }
      else if derivStrictlyNegativeIdx e ρ' idx then
        -- f is decreasing along idx, minimum is at right endpoint
        let ρ_hi := updateIntervalEnv ρ idx (IntervalRat.singleton J.hi)
        { valueBound := LeanCert.Internal.Rational.evalUnchecked e ρ_hi
          argBound := some (IntervalRat.singleton J.hi)
          depth := maxDepth - depth }
      else
        -- Bisect and take the better bound
        let (J₁, J₂) := J.bisect
        let r₁ := go J₁ (depth - 1)
        let r₂ := go J₂ (depth - 1)
        OptResult.merge r₁ r₂
  termination_by depth
  decreasing_by all_goals omega

/-! ### N-variable minimization correctness -/

/-- Base case correctness for n-variable optimization.
    Interval evaluation gives a valid lower bound. -/
theorem minimizeIntervalIdx_base_correct (e : Expr) (hsupp : ADSupported e)
    (ρ_int : IntervalEnv) :
    ∀ ρ_real : Nat → ℝ, (∀ i, ρ_real i ∈ ρ_int i) →
      (LeanCert.Internal.Rational.evalUnchecked e ρ_int).lo ≤ Expr.eval ρ_real e := by
  intro ρ_real hρ
  have h := evalInterval_correct e hsupp ρ_real ρ_int hρ
  simp only [IntervalRat.mem_def] at h
  exact h.1

/-- Helper lemma for go correctness in n-variable setting -/
theorem minimizeIntervalIdx_go_correct (e : Expr) (hsupp : ADSupported e)
    (ρ_int : IntervalEnv) (idx : Nat) (maxDepth depth : ℕ) (J : IntervalRat)
    (hJ_sub : ∀ t, t ∈ J → t ∈ ρ_int idx) :
    ∀ ρ_real : Nat → ℝ, (∀ i, ρ_real i ∈ ρ_int i) →
      ∀ t ∈ J,
        (minimizeIntervalIdx.go e ρ_int idx maxDepth J depth).valueBound.lo
          ≤ Expr.eval (Expr.updateVar ρ_real idx t) e := by
  induction depth generalizing J with
  | zero =>
    intro ρ_real hρ t ht
    rw [minimizeIntervalIdx.go]
    simp only [↓reduceIte]
    -- Base case: interval evaluation bounds all points
    have hρ' : ∀ i, (Expr.updateVar ρ_real idx t) i ∈ (updateIntervalEnv ρ_int idx J) i := by
      intro i
      simp only [Expr.updateVar, updateIntervalEnv]
      split_ifs with hi
      · exact ht
      · exact hρ i
    have heval := evalInterval_correct e hsupp (Expr.updateVar ρ_real idx t) (updateIntervalEnv
      ρ_int idx J) hρ'
    simp only [IntervalRat.mem_def] at heval
    exact heval.1
  | succ n ih =>
    intro ρ_real hρ t ht
    have hdepth : n + 1 ≠ 0 := Nat.succ_ne_zero n
    rw [minimizeIntervalIdx.go]
    simp only [hdepth, ↓reduceIte, OptResult.merge, Nat.add_sub_cancel]
    -- Note: ρ' in the go function is updateIntervalEnv ρ_int idx J
    split_ifs with hpos hneg hle
    · -- Derivative strictly positive: increasing function
      -- hpos : derivStrictlyPositiveIdx e (updateIntervalEnv ρ_int idx J) idx = true
      have hpos' : 0 < (derivInterval e (updateIntervalEnv ρ_int idx J) idx).lo := by
        simp only [derivStrictlyPositiveIdx, decide_eq_true_eq] at hpos
        exact hpos
      have hρ_lo : ∀ i, (Expr.updateVar ρ_real idx J.lo) i ∈
          (updateIntervalEnv ρ_int idx (IntervalRat.singleton J.lo)) i := by
        intro i
        simp only [Expr.updateVar, updateIntervalEnv]
        split_ifs with hi
        · exact IntervalRat.mem_singleton _
        · exact hρ i
      have heval := evalInterval_correct e hsupp (Expr.updateVar ρ_real idx J.lo)
        (updateIntervalEnv ρ_int idx (IntervalRat.singleton J.lo)) hρ_lo
      simp only [IntervalRat.mem_def] at heval
      -- Build membership for the derivative bound
      -- We use a modified ρ_real that has J.lo at index idx, since ρ_real idx is never used
      -- in the derivative computation (it gets replaced by the variable of differentiation)
      let ρ_real' := Expr.updateVar ρ_real idx (J.lo : ℝ)
      have hρ'_deriv : ∀ i, ρ_real' i ∈ (updateIntervalEnv ρ_int idx J) i := by
        intro i
        simp only [ρ_real', Expr.updateVar, updateIntervalEnv]
        split_ifs with hi
        · -- At idx: J.lo ∈ J
          simp only [IntervalRat.mem_def, Rat.cast_le]
          exact ⟨le_refl _, J.le⟩
        · exact hρ i
      -- Since evalAlong replaces ρ_real' idx with the variable x, monotonicity for ρ_real'
      -- is the same as for ρ_real
      have hmono' := strictMonoOn_of_deriv_pos_interval_idx e hsupp ρ_real'
        (updateIntervalEnv ρ_int idx J) idx hρ'_deriv hpos'
      -- evalAlong e ρ_real idx = evalAlong e ρ_real' idx because only ρ(idx) differs
      -- and evalAlong replaces it with the function argument
      have heq_along : ∀ x, Expr.evalAlong e ρ_real idx x = Expr.evalAlong e ρ_real' idx x := by
        intro x
        simp only [Expr.evalAlong]
        congr 1
        funext i
        simp only [Expr.updateVar, ρ_real']
        split_ifs with h1
        · rfl  -- i = idx: both give x
        · rfl  -- i ≠ idx: both give ρ_real i
      have hmono : StrictMonoOn (Expr.evalAlong e ρ_real idx)
          (Set.Icc ((updateIntervalEnv ρ_int idx J idx).lo : ℝ)
            ((updateIntervalEnv ρ_int idx J idx).hi : ℝ)) := by
        intro x hx y hy hxy
        rw [heq_along x, heq_along y]
        exact hmono' hx hy hxy
      simp only [IntervalRat.mem_def] at ht
      by_cases heq : (J.lo : ℝ) = t
      · calc (LeanCert.Internal.Rational.evalUnchecked e (updateIntervalEnv ρ_int idx
        (IntervalRat.singleton J.lo))).lo
            ≤ Expr.eval (Expr.updateVar ρ_real idx J.lo) e := heval.1
          _ = Expr.eval (Expr.updateVar ρ_real idx t) e := by rw [← heq]
      · have hlt : (J.lo : ℝ) < t := lt_of_le_of_ne ht.1 heq
        have hJlo_mem : (J.lo : ℝ) ∈ Set.Icc ((updateIntervalEnv ρ_int idx J idx).lo : ℝ)
            ((updateIntervalEnv ρ_int idx J idx).hi) := by
          simp only [Set.mem_Icc, updateIntervalEnv, ↓reduceIte]
          exact ⟨le_refl _, Rat.cast_le.mpr J.le⟩
        have ht_mem : t ∈ Set.Icc ((updateIntervalEnv ρ_int idx J idx).lo : ℝ)
            ((updateIntervalEnv ρ_int idx J idx).hi) := by
          simp only [Set.mem_Icc, updateIntervalEnv, ↓reduceIte]
          exact ht
        have hmono_at := hmono hJlo_mem ht_mem hlt
        simp only [Expr.evalAlong] at hmono_at
        calc (LeanCert.Internal.Rational.evalUnchecked e (updateIntervalEnv ρ_int idx
          (IntervalRat.singleton J.lo))).lo
            ≤ Expr.eval (Expr.updateVar ρ_real idx J.lo) e := heval.1
          _ ≤ Expr.eval (Expr.updateVar ρ_real idx t) e := le_of_lt hmono_at
    · -- Derivative strictly negative: decreasing function
      have hneg' : (derivInterval e (updateIntervalEnv ρ_int idx J) idx).hi < 0 := by
        simp only [derivStrictlyNegativeIdx, decide_eq_true_eq] at hneg
        exact hneg
      have hρ_hi : ∀ i, (Expr.updateVar ρ_real idx J.hi) i ∈
          (updateIntervalEnv ρ_int idx (IntervalRat.singleton J.hi)) i := by
        intro i
        simp only [Expr.updateVar, updateIntervalEnv]
        split_ifs with hi
        · exact IntervalRat.mem_singleton _
        · exact hρ i
      have heval := evalInterval_correct e hsupp (Expr.updateVar ρ_real idx J.hi)
        (updateIntervalEnv ρ_int idx (IntervalRat.singleton J.hi)) hρ_hi
      simp only [IntervalRat.mem_def] at heval
      -- We use a modified ρ_real that has J.hi at index idx
      let ρ_real' := Expr.updateVar ρ_real idx (J.hi : ℝ)
      have hρ'_deriv : ∀ i, ρ_real' i ∈ (updateIntervalEnv ρ_int idx J) i := by
        intro i
        simp only [ρ_real', Expr.updateVar, updateIntervalEnv]
        split_ifs with hi
        · simp only [IntervalRat.mem_def, Rat.cast_le]
          exact ⟨J.le, le_refl _⟩
        · exact hρ i
      have hmono' := strictAntiOn_of_deriv_neg_interval_idx e hsupp ρ_real'
        (updateIntervalEnv ρ_int idx J) idx hρ'_deriv hneg'
      have heq_along : ∀ x, Expr.evalAlong e ρ_real idx x = Expr.evalAlong e ρ_real' idx x := by
        intro x
        simp only [Expr.evalAlong]
        congr 1
        funext i
        simp only [Expr.updateVar, ρ_real']
        split_ifs with h1
        · rfl
        · rfl
      have hmono : StrictAntiOn (Expr.evalAlong e ρ_real idx)
          (Set.Icc ((updateIntervalEnv ρ_int idx J idx).lo : ℝ)
            ((updateIntervalEnv ρ_int idx J idx).hi : ℝ)) := by
        intro x hx y hy hxy
        rw [heq_along x, heq_along y]
        exact hmono' hx hy hxy
      simp only [IntervalRat.mem_def] at ht
      by_cases heq : t = (J.hi : ℝ)
      · calc (LeanCert.Internal.Rational.evalUnchecked e (updateIntervalEnv ρ_int idx
        (IntervalRat.singleton J.hi))).lo
            ≤ Expr.eval (Expr.updateVar ρ_real idx J.hi) e := heval.1
          _ = Expr.eval (Expr.updateVar ρ_real idx t) e := by rw [← heq]
      · have hlt : t < (J.hi : ℝ) := lt_of_le_of_ne ht.2 heq
        have ht_mem : t ∈ Set.Icc ((updateIntervalEnv ρ_int idx J idx).lo : ℝ)
            ((updateIntervalEnv ρ_int idx J idx).hi) := by
          simp only [Set.mem_Icc, updateIntervalEnv, ↓reduceIte]
          exact ht
        have hJhi_mem : (J.hi : ℝ) ∈ Set.Icc ((updateIntervalEnv ρ_int idx J idx).lo : ℝ)
            ((updateIntervalEnv ρ_int idx J idx).hi) := by
          simp only [Set.mem_Icc, updateIntervalEnv, ↓reduceIte]
          exact ⟨Rat.cast_le.mpr J.le, le_refl _⟩
        have hmono_at := hmono ht_mem hJhi_mem hlt
        simp only [Expr.evalAlong] at hmono_at
        calc (LeanCert.Internal.Rational.evalUnchecked e (updateIntervalEnv ρ_int idx
          (IntervalRat.singleton J.hi))).lo
            ≤ Expr.eval (Expr.updateVar ρ_real idx J.hi) e := heval.1
          _ ≤ Expr.eval (Expr.updateVar ρ_real idx t) e := le_of_lt hmono_at
    · -- Bisection case, hle (r₁.lo ≤ r₂.lo)
      have hcases := IntervalRat.mem_bisect_or ht
      cases hcases with
      | inl h1 =>
        have hsub1 : ∀ s, s ∈ J.bisect.1 → s ∈ ρ_int idx := fun s hs =>
          hJ_sub s (IntervalRat.mem_of_mem_bisect_left hs)
        exact ih J.bisect.1 hsub1 ρ_real hρ t h1
      | inr h2 =>
        have hsub2 : ∀ s, s ∈ J.bisect.2 → s ∈ ρ_int idx := fun s hs =>
          hJ_sub s (IntervalRat.mem_of_mem_bisect_right hs)
        have h := ih J.bisect.2 hsub2 ρ_real hρ t h2
        have hle_cast : ((minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.fst)
          n).valueBound.lo : ℝ)
            ≤ (minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.snd) n).valueBound.lo := by
              exact_mod_cast hle
        calc ((minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.fst) n).valueBound.lo : ℝ)
            ≤ (minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.snd) n).valueBound.lo :=
              hle_cast
          _ ≤ Expr.eval (Expr.updateVar ρ_real idx t) e := h
    · -- Bisection case, ¬hle (r₁.lo > r₂.lo)
      have hcases := IntervalRat.mem_bisect_or ht
      cases hcases with
      | inl h1 =>
        have hsub1 : ∀ s, s ∈ J.bisect.1 → s ∈ ρ_int idx := fun s hs =>
          hJ_sub s (IntervalRat.mem_of_mem_bisect_left hs)
        have h := ih J.bisect.1 hsub1 ρ_real hρ t h1
        have hlt := not_le.mp hle
        have hlt_cast : ((minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.snd)
          n).valueBound.lo : ℝ)
            ≤ (minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.fst) n).valueBound.lo := by
          exact_mod_cast (le_of_lt hlt)
        calc ((minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.snd) n).valueBound.lo : ℝ)
            ≤ (minimizeIntervalIdx.go e ρ_int idx maxDepth (J.bisect.fst) n).valueBound.lo :=
              hlt_cast
          _ ≤ Expr.eval (Expr.updateVar ρ_real idx t) e := h
      | inr h2 =>
        have hsub2 : ∀ s, s ∈ J.bisect.2 → s ∈ ρ_int idx := fun s hs =>
          hJ_sub s (IntervalRat.mem_of_mem_bisect_right hs)
        exact ih J.bisect.2 hsub2 ρ_real hρ t h2

/-- Correctness theorem for n-variable minimization:
    For any real environment ρ_real satisfying ρ_int, and any t in ρ_int idx,
    the computed lower bound is valid.

    FULLY PROVED - no sorry, no axioms. -/
theorem minimizeIntervalIdx_correct (e : Expr) (hsupp : ADSupported e)
    (ρ_int : IntervalEnv) (idx : Nat) (maxDepth : ℕ) :
    ∀ ρ_real : Nat → ℝ, (∀ i, ρ_real i ∈ ρ_int i) →
      ∀ t ∈ ρ_int idx,
        (minimizeIntervalIdx e ρ_int idx maxDepth).valueBound.lo
          ≤ Expr.eval (Expr.updateVar ρ_real idx t) e := by
  intro ρ_real hρ t ht
  simp only [minimizeIntervalIdx]
  exact minimizeIntervalIdx_go_correct e hsupp ρ_int idx maxDepth maxDepth (ρ_int idx)
    (fun s hs => hs) ρ_real hρ t ht

/-- N-variable maximization via minimization of negation -/
noncomputable def maximizeIntervalIdx (e : Expr) (ρ : IntervalEnv) (idx : Nat)
    (maxDepth : ℕ) : OptResult :=
  let negResult := minimizeIntervalIdx (Expr.neg e) ρ idx maxDepth
  { valueBound := IntervalRat.neg negResult.valueBound
    argBound := negResult.argBound
    depth := negResult.depth }

/-- Correctness theorem for n-variable maximization -/
theorem maximizeIntervalIdx_correct (e : Expr) (hsupp : ADSupported e)
    (ρ_int : IntervalEnv) (idx : Nat) (maxDepth : ℕ) :
    ∀ ρ_real : Nat → ℝ, (∀ i, ρ_real i ∈ ρ_int i) →
      ∀ t ∈ ρ_int idx,
        Expr.eval (Expr.updateVar ρ_real idx t) e
          ≤ (maximizeIntervalIdx e ρ_int idx maxDepth).valueBound.hi := by
  intro ρ_real hρ t ht
  have hneg_supp : ADSupported (Expr.neg e) := ADSupported.neg hsupp
  have hmin := minimizeIntervalIdx_correct (Expr.neg e) hneg_supp ρ_int idx maxDepth ρ_real hρ t ht
  simp only [Expr.eval_neg] at hmin
  simp only [maximizeIntervalIdx, IntervalRat.neg]
  have h : Expr.eval (Expr.updateVar ρ_real idx t) e ≤
           -(((minimizeIntervalIdx (Expr.neg e) ρ_int idx maxDepth).valueBound.lo) : ℝ) := by
    linarith
  convert h using 1
  simp only [Rat.cast_neg]

end LeanCert.Engine
