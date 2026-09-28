/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Engine.Eval.Core
public import LeanPool.MovingSofa.LeanCert.Engine.Eval.Result
/-!
# Extended (Noncomputable) Interval Evaluation

This file implements the noncomputable interval evaluator for `LeanCert.Core.Expr`,
supporting exp with floor/ceil bounds and partial evaluation for inv/log.

## Main definitions

* `evalInterval` - Noncomputable interval evaluator supporting exp
* `evalInterval_correct` - Correctness theorem for extended evaluation
* `evalInterval?` - Partial (Option-returning) evaluator with inv/log support
* `evalInterval?_correct` - Correctness theorem for partial evaluation

## Design notes

The extended evaluator uses `Real.exp` with floor/ceil bounds, which requires
noncomputability. For computability, use `LeanCert.Internal.Rational.evalTotalCore` instead.

The partial evaluator `evalInterval?` returns `none` when:
- The denominator interval for `inv` contains zero
- The argument interval for `log` is not strictly positive
- The argument for `atanh` is not in (-1, 1)

When it returns `some I`, correctness is guaranteed.
-/

/-! ### Extended interval evaluation (noncomputable, supports exp) -/

@[expose] public section

namespace LeanCert.Engine

open LeanCert.Core

end LeanCert.Engine

namespace LeanCert.Internal.Rational

open LeanCert.Core LeanCert.Engine

/-- Noncomputable interval evaluator supporting exp.

    For supported expressions (const, var, add, mul, neg, sin, cos, exp), this
    computes correct interval bounds with a fully-verified proof.

    For unsupported expressions (inv, log), returns a default interval.
    Do not rely on results for expressions containing inv or log.
    Use evalInterval? for partial functions like inv and log.

    This evaluator is NONCOMPUTABLE due to exp using Real.exp with floor/ceil. -/
noncomputable def evalUnchecked (e : Expr) (ρ : IntervalEnv) : IntervalRat :=
  match e with
  | Expr.const q => IntervalRat.singleton q
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ => IntervalRat.add (evalUnchecked e₁ ρ) (evalUnchecked e₂ ρ)
  | Expr.mul e₁ e₂ => IntervalRat.mul (evalUnchecked e₁ ρ) (evalUnchecked e₂ ρ)
  | Expr.neg e => IntervalRat.neg (evalUnchecked e ρ)
  | Expr.inv _ => default  -- Not in ADSupported; safe default
  | Expr.exp e => IntervalRat.expInterval (evalUnchecked e ρ)
  | Expr.sin e => sinInterval (evalUnchecked e ρ)
  | Expr.cos e => cosInterval (evalUnchecked e ρ)
  | Expr.log _ => default  -- Not in ADSupported; use evalInterval? for log
  | Expr.atan e => atanInterval (evalUnchecked e ρ)
  | Expr.arsinh e => arsinhInterval (evalUnchecked e ρ)
  | Expr.atanh _ => default  -- Not in ADSupported; use evalInterval? for atanh
  | Expr.sinc _ => ⟨-1, 1, by norm_num⟩  -- sinc is bounded by [-1, 1]
  | Expr.erf _ => ⟨-1, 1, by norm_num⟩  -- erf is bounded by [-1, 1]
  | Expr.sinh _ => default  -- sinh unbounded; use LeanCert.Internal.Rational.evalTotalCore for
    -- tight bounds
  | Expr.cosh _ => default  -- cosh unbounded; use LeanCert.Internal.Rational.evalTotalCore for
    -- tight bounds
  | Expr.tanh _ => default  -- tanh bounded but not in ADSupported; use
    -- LeanCert.Internal.Rational.evalTotalCore
  | Expr.sqrt e => IntervalRat.sqrtInterval (evalUnchecked e ρ)
  | Expr.namedConst c => c.interval

end LeanCert.Internal.Rational

namespace LeanCert.Engine

open LeanCert.Core

/-- Fundamental correctness theorem for extended evaluation.

    This theorem is FULLY PROVED (no sorry, no axioms) for supported expressions.
    The `hsupp` hypothesis ensures we only consider expressions in the verified subset. -/
theorem evalInterval_correct (e : Expr) (hsupp : ADSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (hρ : envMem ρ_real ρ_int) :
    Expr.eval ρ_real e ∈ LeanCert.Internal.Rational.evalUnchecked e ρ_int := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, LeanCert.Internal.Rational.evalUnchecked]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [Expr.eval_var, LeanCert.Internal.Rational.evalUnchecked]
    exact hρ idx
  | add h₁ h₂ ih₁ ih₂ =>
    simp only [Expr.eval_add, LeanCert.Internal.Rational.evalUnchecked]
    exact IntervalRat.mem_add ih₁ ih₂
  | mul h₁ h₂ ih₁ ih₂ =>
    simp only [Expr.eval_mul, LeanCert.Internal.Rational.evalUnchecked]
    exact IntervalRat.mem_mul ih₁ ih₂
  | neg _ ih =>
    simp only [Expr.eval_neg, LeanCert.Internal.Rational.evalUnchecked]
    exact IntervalRat.mem_neg ih
  | sin _ ih =>
    simp only [Expr.eval_sin, LeanCert.Internal.Rational.evalUnchecked]
    exact mem_sinInterval ih
  | cos _ ih =>
    simp only [Expr.eval_cos, LeanCert.Internal.Rational.evalUnchecked]
    exact mem_cosInterval ih
  | exp _ ih =>
    simp only [Expr.eval_exp, LeanCert.Internal.Rational.evalUnchecked]
    exact IntervalRat.mem_expInterval ih

/-! ### Convenience functions

Note: LeanCert.Internal.Rational.evalTotalCore now uses Taylor series for exp/sin/cos, which gives
different (often tighter) intervals than evalInterval's floor/ceil bounds.
Both are correct, but they are not necessarily equal.

For purely algebraic expressions (const, var, add, mul, neg),
both evaluators give identical results. -/

end LeanCert.Engine

namespace LeanCert.Internal.Rational

open LeanCert.Core LeanCert.Engine

/-- Internal single-variable wrapper around `evalUnchecked`. -/
noncomputable def evalUnchecked1 (e : Expr) (I : IntervalRat) : IntervalRat :=
  evalUnchecked e (fun _ => I)

end LeanCert.Internal.Rational

namespace LeanCert.Engine

open LeanCert.Core

/-- Correctness for single-variable extended evaluation -/
theorem evalInterval1_correct (e : Expr) (hsupp : ADSupported e)
    (x : ℝ) (I : IntervalRat) (hx : x ∈ I) :
    Expr.eval (fun _ => x) e ∈ LeanCert.Internal.Rational.evalUnchecked1 e I :=
  evalInterval_correct e hsupp _ _ (fun _ => hx)

/-! ### Partial interval evaluation with inv support -/

/-- Partial (Option-returning) interval evaluator supporting inv.

    For expressions with inv, this evaluator returns `none` if the denominator
    interval contains zero, and `some I` with a correct enclosure otherwise.

    This allows safe interval evaluation of expressions like 1/x when we can
    verify the denominator is bounded away from zero.

    For expressions without inv, this always returns `some` with the same
    result as `evalInterval`. -/
def evalIntervalLogDepth : ℕ := 60

/-- The Taylor truncation depth used by the checked exponential evaluator. -/
def evalIntervalExpDepth : ℕ := 30

/-- Taylor depth used by the strict `atanh` evaluator. -/
def evalIntervalAtanhDepth : ℕ := 30

/-- Evaluate an expression by rational intervals, failing when a domain check fails. -/
def evalInterval? (e : Expr) (ρ : IntervalEnv) : Option IntervalRat :=
  match e with
  | Expr.const q => some (IntervalRat.singleton q)
  | Expr.var idx => some (ρ idx)
  | Expr.add e₁ e₂ =>
      match evalInterval? e₁ ρ, evalInterval? e₂ ρ with
      | some I₁, some I₂ => some (IntervalRat.add I₁ I₂)
      | _, _ => none
  | Expr.mul e₁ e₂ =>
      match evalInterval? e₁ ρ, evalInterval? e₂ ρ with
      | some I₁, some I₂ => some (IntervalRat.mul I₁ I₂)
      | _, _ => none
  | Expr.neg e =>
      match evalInterval? e ρ with
      | some I => some (IntervalRat.neg I)
      | none => none
  | Expr.inv e₁ =>
      match evalInterval? e₁ ρ with
      | none => none
      | some J =>
          if h : IntervalRat.containsZero J then
            none
          else
            some (IntervalRat.invNonzero ⟨J, h⟩)
  | Expr.exp e =>
      match evalInterval? e ρ with
      | some I => some (IntervalRat.expComputable I evalIntervalExpDepth)
      | none => none
  | Expr.sin e =>
      match evalInterval? e ρ with
      | some I => some (sinInterval I)
      | none => none
  | Expr.cos e =>
      match evalInterval? e ρ with
      | some I => some (cosInterval I)
      | none => none
  | Expr.log e =>
      match evalInterval? e ρ with
      | none => none
      | some J =>
          if h : IntervalRat.isPositive J then
            some (IntervalRat.logComputable J evalIntervalLogDepth)
          else
            none
  | Expr.atan e =>
      match evalInterval? e ρ with
      | some I => some (atanInterval I)
      | none => none
  | Expr.arsinh e =>
      match evalInterval? e ρ with
      | some I => some (arsinhInterval I)
      | none => none
  | Expr.atanh e =>
      match evalInterval? e ρ with
      | none => none
      | some J =>
          if -1 < J.lo ∧ J.hi < 1 then
            some (IntervalRat.atanhComputable J evalIntervalAtanhDepth)
          else
            none
  | Expr.sinc e =>
      match evalInterval? e ρ with
      | some _ => some ⟨-1, 1, by norm_num⟩  -- sinc is bounded by [-1, 1]
      | none => none
  | Expr.erf e =>
      match evalInterval? e ρ with
      | some _ => some ⟨-1, 1, by norm_num⟩  -- erf is bounded by [-1, 1]
      | none => none
  | Expr.sinh e =>
      match evalInterval? e ρ with
      | some I => some (sinhInterval I)
      | none => none
  | Expr.cosh e =>
      match evalInterval? e ρ with
      | some I => some (coshInterval I)
      | none => none
  | Expr.tanh e =>
      match evalInterval? e ρ with
      | some I => some (tanhInterval I)
      | none => none
  | Expr.sqrt e =>
      match evalInterval? e ρ with
      | some I => some (IntervalRat.sqrtInterval I)
      | none => none
  | Expr.namedConst c => some c.interval

/-- Main correctness theorem for evalInterval? (approach 1 from plan).

    When evalInterval? returns `some I`:
    1. The expression evaluates to a value in I for all ρ_real ∈ ρ_int
    2. All inv denominators along the evaluation are guaranteed nonzero
       (because their intervals don't contain zero)

    This follows your suggestion to keep ADSupported syntactic and add
    separate semantic hypotheses. The key insight is that if evalInterval?
    succeeds (returns Some), the interval arithmetic has already verified
    that no denominator interval contains zero. -/
theorem evalInterval?_correct (e : Expr)
    (ρ_int : IntervalEnv) (I : IntervalRat)
    (hsome : evalInterval? e ρ_int = some I)
    (ρ_real : Nat → ℝ) (hρ : envMem ρ_real ρ_int) :
    Expr.eval ρ_real e ∈ I := by
  induction e generalizing I with
  | const q =>
    simp only [evalInterval?] at hsome
    cases hsome
    simp only [Expr.eval_const]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [evalInterval?] at hsome
    cases hsome
    simp only [Expr.eval_var]
    exact hρ idx
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [evalInterval?] at hsome
    cases heq₁ : evalInterval? e₁ ρ_int with
    | none => simp only [heq₁] at hsome; contradiction
    | some I₁ =>
      cases heq₂ : evalInterval? e₂ ρ_int with
      | none => simp only [heq₁, heq₂] at hsome; contradiction
      | some I₂ =>
        simp only [heq₁, heq₂] at hsome
        cases hsome
        simp only [Expr.eval_add]
        exact IntervalRat.mem_add (ih₁ I₁ heq₁) (ih₂ I₂ heq₂)
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [evalInterval?] at hsome
    cases heq₁ : evalInterval? e₁ ρ_int with
    | none => simp only [heq₁] at hsome; contradiction
    | some I₁ =>
      cases heq₂ : evalInterval? e₂ ρ_int with
      | none => simp only [heq₁, heq₂] at hsome; contradiction
      | some I₂ =>
        simp only [heq₁, heq₂] at hsome
        cases hsome
        simp only [Expr.eval_mul]
        exact IntervalRat.mem_mul (ih₁ I₁ heq₁) (ih₂ I₂ heq₂)
  | neg e ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some I' =>
      simp only [heq] at hsome
      cases hsome
      simp only [Expr.eval_neg]
      exact IntervalRat.mem_neg (ih I' heq)
  | inv e ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some J =>
      simp only [heq] at hsome
      split at hsome
      · contradiction
      · rename_i hnonzero
        cases hsome
        simp only [Expr.eval_inv]
        have hJ_mem := ih J heq
        -- The denominator is nonzero because J doesn't contain zero and eval ∈ J
        have heval_ne : Expr.eval ρ_real e ≠ 0 := by
          intro heq_zero
          rw [heq_zero] at hJ_mem
          simp only [IntervalRat.mem_def] at hJ_mem
          simp only [IntervalRat.containsZero, not_and, not_le] at hnonzero
          rcases le_or_gt J.lo 0 with hlo | hlo
          · have hhi_nonneg : (0 : ℚ) ≤ J.hi := by
              have h : (0 : ℝ) ≤ J.hi := hJ_mem.2
              exact_mod_cast h
            exact absurd (hnonzero hlo) (not_lt.mpr hhi_nonneg)
          · have hlo_pos : (0 : ℝ) < J.lo := by exact_mod_cast hlo
            exact absurd hJ_mem.1 (not_le.mpr hlo_pos)
        exact IntervalRat.mem_invNonzero hJ_mem heval_ne
  | log e ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some J =>
      simp only [heq] at hsome
      split at hsome
      · rename_i hpos
        cases hsome
        simp only [Expr.eval_log]
        have hJ_mem := ih J heq
        -- The argument is positive because J.lo > 0 and eval ∈ J
        exact IntervalRat.mem_logComputable hJ_mem hpos evalIntervalLogDepth
      · contradiction
  | atanh e ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some J =>
      simp only [heq] at hsome
      split at hsome
      · rename_i hunit
        cases hsome
        simp only [Expr.eval_atanh]
        exact IntervalRat.mem_atanhComputable (ih J heq) hunit.1 hunit.2
          evalIntervalAtanhDepth
      · contradiction
  | sinc e ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some I' =>
      simp only [heq] at hsome
      cases hsome
      simp only [Expr.eval_sinc]
      -- sinc(x) ∈ [-1, 1] for all x, using Mathlib's Real.sinc lemmas
      simp only [IntervalRat.mem_def]
      simpa only [Set.mem_Icc, Rat.cast_neg, Rat.cast_one] using
        (Real.sinc_mem_Icc (Expr.eval ρ_real e))
  | erf e ih =>
    simp only [evalInterval?] at hsome
    cases heq : evalInterval? e ρ_int with
    | none => simp only [heq] at hsome; contradiction
    | some I' =>
      simp only [heq] at hsome
      cases hsome
      simp only [Expr.eval_erf]
      -- erf(x) ∈ [-1, 1] for all x
      simp only [IntervalRat.mem_def]
      simpa only [Set.mem_Icc, Rat.cast_neg, Rat.cast_one] using
        (Real.erf_mem_Icc (Expr.eval ρ_real e))
  | namedConst c =>
    simp only [evalInterval?] at hsome
    cases hsome
    simp only [Expr.eval_namedConst]
    exact c.mem_interval
  | exp e ih | sin e ih | cos e ih | sinh e ih | cosh e ih | tanh e ih
  | atan e ih | arsinh e ih | sqrt e ih =>
    cases heq : evalInterval? e ρ_int with
    | none => simp only [evalInterval?, heq] at hsome; contradiction
    | some I' =>
      simp only [evalInterval?, heq] at hsome
      cases hsome
      first
      | exact IntervalRat.mem_expComputable (ih I' heq) evalIntervalExpDepth
      | exact mem_sinInterval (ih I' heq)
      | exact mem_cosInterval (ih I' heq)
      | exact IntervalRat.mem_sinhComputable (ih I' heq) 10
      | exact IntervalRat.mem_coshComputable (ih I' heq) 10
      | exact mem_tanhInterval (ih I' heq)
      | exact mem_atanInterval (ih I' heq)
      | exact mem_arsinhInterval (ih I' heq)
      | exact IntervalRat.mem_sqrtInterval' (ih I' heq)

/-! ### Checked API with diagnostics -/

/-- Diagnose the first partial-domain failure after `evalInterval?` returned
`none`. This function is deliberately separate from the trusted computation:
soundness depends only on successful `evalInterval?`, while diagnostics may be
refined without changing the correctness theorem. -/
def diagnoseEvalIntervalFailure (e : Expr) (ρ : IntervalEnv) : EvalError :=
  match e with
  | .add e₁ e₂ | .mul e₁ e₂ =>
      if evalInterval? e₁ ρ = none then
        .nestedFailure "left operand" (diagnoseEvalIntervalFailure e₁ ρ)
      else
        .nestedFailure "right operand" (diagnoseEvalIntervalFailure e₂ ρ)
  | .neg e | .exp e | .sin e | .cos e | .atan e | .arsinh e | .sinc e |
      .erf e | .sinh e | .cosh e | .tanh e | .sqrt e =>
      .nestedFailure "unary operand" (diagnoseEvalIntervalFailure e ρ)
  | .inv e =>
      match evalInterval? e ρ with
      | some I => .reciprocalContainsZero I
      | none => .nestedFailure "reciprocal operand" (diagnoseEvalIntervalFailure e ρ)
  | .log e =>
      match evalInterval? e ρ with
      | some I => .logNonpositive I
      | none => .nestedFailure "logarithm operand" (diagnoseEvalIntervalFailure e ρ)
  | .atanh e =>
      match evalInterval? e ρ with
      | some I => .atanhOutsideUnitBall I
      | none => .nestedFailure "atanh operand" (diagnoseEvalIntervalFailure e ρ)
  | .const _ | .var _ | .namedConst _ =>
      .unsupportedBackend "internal: total expression unexpectedly failed"
termination_by e

/-- Checked rational evaluator. Every successful result is a certified finite
enclosure; domain-invalid expressions return a structured error. -/
def evalIntervalChecked (e : Expr) (ρ : IntervalEnv) : EvalResult IntervalRat :=
  match evalInterval? e ρ with
  | some I => .ok I
  | none => .error (diagnoseEvalIntervalFailure e ρ)

/-- Success of `evalIntervalChecked` is sufficient for enclosure correctness
for every expression constructor. -/
theorem evalIntervalChecked_correct (e : Expr) (ρ_int : IntervalEnv) (I : IntervalRat)
    (hsuccess : evalIntervalChecked e ρ_int = .ok I)
    (ρ_real : Nat → ℝ) (hρ : envMem ρ_real ρ_int) :
    Expr.eval ρ_real e ∈ I := by
  cases heval : evalInterval? e ρ_int with
  | none =>
    rw [evalIntervalChecked, heval] at hsuccess
    contradiction
  | some J =>
    rw [evalIntervalChecked, heval] at hsuccess
    injection hsuccess with hJI
    subst I
    exact evalInterval?_correct e ρ_int J heval ρ_real hρ

/-- Checked Rational evaluation with a tight path for the verified computable
core. Unsupported syntax or a failed core-domain check falls back to the
general checked evaluator, preserving its structured domain errors. -/
def evalIntervalTightChecked (e : Expr) (ρ : IntervalEnv)
    (cfg : EvalConfig := {}) : EvalResult IntervalRat :=
  if e.checkSupportedCore && checkDomainValid e ρ cfg then
    .ok (LeanCert.Internal.Rational.evalTotalCore e ρ cfg)
  else
    evalIntervalChecked e ρ

/-- Every successful tight checked Rational evaluation encloses the expression
value. The core branch uses the core correctness theorem; the fallback uses
the general checked evaluator theorem. -/
theorem evalIntervalTightChecked_correct (e : Expr) (ρ_int : IntervalEnv)
    (cfg : EvalConfig) (I : IntervalRat)
    (hsuccess : evalIntervalTightChecked e ρ_int cfg = .ok I)
    (ρ_real : Nat → ℝ) (hρ : envMem ρ_real ρ_int) :
    Expr.eval ρ_real e ∈ I := by
  by_cases hsupp : e.checkSupportedCore = true
  · by_cases hdom : checkDomainValid e ρ_int cfg = true
    · have hsupp' := Expr.checkSupportedCore_correct hsupp
      have hdom' := checkDomainValid_correct e ρ_int cfg hdom
      have hmem := evalIntervalCore_correct e hsupp' ρ_real ρ_int hρ cfg hdom'
      simp only [ExceptT.stM_eq, evalIntervalTightChecked, hsupp, hdom, Bool.and_self, ↓reduceIte,
        Except.ok.injEq] at hsuccess
      subst I
      exact hmem
    · have hfallback :
          evalIntervalTightChecked e ρ_int cfg = evalIntervalChecked e ρ_int := by
        simp [evalIntervalTightChecked, hsupp, hdom]
      rw [hfallback] at hsuccess
      exact evalIntervalChecked_correct e ρ_int I hsuccess ρ_real hρ
  · have hfallback :
        evalIntervalTightChecked e ρ_int cfg = evalIntervalChecked e ρ_int := by
      simp [evalIntervalTightChecked, hsupp]
    rw [hfallback] at hsuccess
    exact evalIntervalChecked_correct e ρ_int I hsuccess ρ_real hρ

/-- Single-variable version of evalInterval? -/
def evalInterval?1 (e : Expr) (I : IntervalRat) : Option IntervalRat :=
  evalInterval? e (fun _ => I)

/-- Correctness for single-variable partial evaluation -/
theorem evalInterval?1_correct (e : Expr)
    (I : IntervalRat) (J : IntervalRat)
    (hsome : evalInterval?1 e I = some J)
    (x : ℝ) (hx : x ∈ I) :
    Expr.eval (fun _ => x) e ∈ J :=
  evalInterval?_correct e _ J hsome _ (fun _ => hx)

/-- When evalInterval? succeeds, we get bounds -/
theorem evalInterval?_le_of_hi (e : Expr)
    (I : IntervalRat) (J : IntervalRat) (c : ℚ)
    (hsome : evalInterval?1 e I = some J)
    (hhi : J.hi ≤ c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have hmem := evalInterval?1_correct e I J hsome x hx
  simp only [IntervalRat.mem_def] at hmem
  have heval_le_hi : Expr.eval (fun _ => x) e ≤ J.hi := hmem.2
  have hhi_le_c : (J.hi : ℝ) ≤ c := by exact_mod_cast hhi
  exact le_trans heval_le_hi hhi_le_c

/-- When evalInterval? succeeds, we get lower bounds -/
theorem evalInterval?_ge_of_lo (e : Expr)
    (I : IntervalRat) (J : IntervalRat) (c : ℚ)
    (hsome : evalInterval?1 e I = some J)
    (hlo : c ≤ J.lo) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalInterval?1_correct e I J hsome x hx
  simp only [IntervalRat.mem_def] at hmem
  have hlo_le_eval : J.lo ≤ Expr.eval (fun _ => x) e := hmem.1
  have hc_le_lo : (c : ℝ) ≤ J.lo := by exact_mod_cast hlo
  exact le_trans hc_le_lo hlo_le_eval

end LeanCert.Engine
