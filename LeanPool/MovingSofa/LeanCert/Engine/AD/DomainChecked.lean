/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Engine.AD.Computable
public import LeanPool.MovingSofa.LeanCert.Engine.Eval.Result
/-!
# Computable domain-aware automatic differentiation

This module extends LeanCert's computable forward-mode AD path with checked
reciprocal and logarithm nodes.  The existing `ADSupported` fragment remains
the domain-free fast path.  Here, successful evaluation itself certifies both
syntactic support and every partial-domain side condition.
-/

@[expose] public section

namespace LeanCert.Engine

open LeanCert.Core

/-- The computable domain-aware AD fragment.  Unlike `ADSupported`, this is a
box-dependent check because reciprocal and logarithm have partial domains. -/
def checkADDomain (e : Expr) (ρ : DualEnv) (cfg : EvalConfig := {}) : Bool :=
  match e with
  | .const _ | .var _ => true
  | .add a b | .mul a b => checkADDomain a ρ cfg && checkADDomain b ρ cfg
  | .neg a | .exp a | .sin a | .cos a => checkADDomain a ρ cfg
  | .inv a =>
      checkADDomain a ρ cfg &&
        decide (¬IntervalRat.containsZero
          (LeanCert.Internal.AD.evalTotalCore a ρ cfg).val)
  | .log a =>
      checkADDomain a ρ cfg &&
        decide (IntervalRat.isPositive
          (LeanCert.Internal.AD.evalTotalCore a ρ cfg).val)
  | _ => false

/-- Best-effort structured explanation for a failed domain-aware AD check. -/
def diagnoseADDomainFailure (e : Expr) (ρ : DualEnv) (cfg : EvalConfig := {}) : EvalError :=
  match e with
  | .add a b | .mul a b =>
      if checkADDomain a ρ cfg then
        .nestedFailure "right operand" (diagnoseADDomainFailure b ρ cfg)
      else
        .nestedFailure "left operand" (diagnoseADDomainFailure a ρ cfg)
  | .neg a | .exp a | .sin a | .cos a =>
      .nestedFailure "unary operand" (diagnoseADDomainFailure a ρ cfg)
  | .inv a =>
      if checkADDomain a ρ cfg then
        .reciprocalContainsZero (LeanCert.Internal.AD.evalTotalCore a ρ cfg).val
      else
        .nestedFailure "reciprocal operand" (diagnoseADDomainFailure a ρ cfg)
  | .log a =>
      if checkADDomain a ρ cfg then
        .logNonpositive (LeanCert.Internal.AD.evalTotalCore a ρ cfg).val
      else
        .nestedFailure "logarithm operand" (diagnoseADDomainFailure a ρ cfg)
  | .const _ | .var _ => .invalidConfiguration "successful AD expression diagnosed as failure"
  | _ => .unsupportedFeature "domain-aware automatic differentiation"

/-- Computable checked dual evaluation.  No finite derivative enclosure is
returned unless every reciprocal denominator excludes zero and every logarithm
argument is strictly positive on the input box. -/
def evalDualChecked (e : Expr) (ρ : DualEnv) (cfg : EvalConfig := {}) :
    EvalResult DualInterval :=
  if checkADDomain e ρ cfg then
    .ok (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
  else
    .error (diagnoseADDomainFailure e ρ cfg)

/-- Checked value-and-derivative evaluation along coordinate `idx`. -/
def evalWithDerivChecked (e : Expr) (ρ : IntervalEnv) (idx : Nat)
    (cfg : EvalConfig := {}) : EvalResult DualInterval :=
  evalDualChecked e (mkDualEnv ρ idx) cfg

/-- Checked derivative enclosure along coordinate `idx`. -/
def derivIntervalChecked (e : Expr) (ρ : IntervalEnv) (idx : Nat)
    (cfg : EvalConfig := {}) : EvalResult IntervalRat :=
  return (← evalWithDerivChecked e ρ idx cfg).der

/-- Checked derivative enclosure for a single-variable expression. -/
def derivIntervalChecked1 (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) :
    EvalResult IntervalRat :=
  derivIntervalChecked e (fun _ => I) 0 cfg

private theorem checkADDomain_of_evalDualChecked_ok {e : Expr} {ρ : DualEnv}
    {cfg : EvalConfig} {D : DualInterval} (h : evalDualChecked e ρ cfg = .ok D) :
    checkADDomain e ρ cfg = true := by
  simp only [evalDualChecked] at h
  split at h
  · assumption
  · contradiction

private theorem evalDualChecked_ok_eq {e : Expr} {ρ : DualEnv}
    {cfg : EvalConfig} {D : DualInterval} (h : evalDualChecked e ρ cfg = .ok D) :
    D = LeanCert.Internal.AD.evalTotalCore e ρ cfg := by
  simp only [evalDualChecked] at h
  split at h
  · exact (Except.ok.inj h).symm
  · contradiction

private theorem not_containsZero_cases {I : IntervalRat}
    (h : ¬IntervalRat.containsZero I) : I.lo > 0 ∨ I.hi < 0 := by
  simp only [IntervalRat.containsZero, not_and_or, not_le] at h
  exact h

private theorem evalTotalCore_val_correct_of_check (e : Expr)
    (ρReal : Nat → ℝ) (ρDual : DualEnv) (cfg : EvalConfig)
    (hρ : ∀ i, ρReal i ∈ (ρDual i).val)
    (hcheck : checkADDomain e ρDual cfg = true) :
    Expr.eval ρReal e ∈ (LeanCert.Internal.AD.evalTotalCore e ρDual cfg).val := by
  induction e with
  | const q =>
      exact IntervalRat.mem_singleton q
  | var i =>
      exact hρ i
  | add a b iha ihb =>
      simp only [checkADDomain, Bool.and_eq_true] at hcheck
      simp only [Expr.eval_add, LeanCert.Internal.AD.evalTotalCore, DualInterval.add]
      exact IntervalRat.mem_add (iha hcheck.1) (ihb hcheck.2)
  | mul a b iha ihb =>
      simp only [checkADDomain, Bool.and_eq_true] at hcheck
      simp only [Expr.eval_mul, LeanCert.Internal.AD.evalTotalCore, DualInterval.mul]
      exact IntervalRat.mem_mul (iha hcheck.1) (ihb hcheck.2)
  | neg a ih =>
      simp only [checkADDomain] at hcheck
      exact IntervalRat.mem_neg (ih hcheck)
  | inv a ih =>
      simp only [checkADDomain, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      simp only [Expr.eval_inv, LeanCert.Internal.AD.evalTotalCore, DualInterval.inv]
      exact mem_invInterval_nonzero (ih hcheck.1) (not_containsZero_cases hcheck.2)
  | exp a ih =>
      simp only [checkADDomain] at hcheck
      exact IntervalRat.mem_expComputable (ih hcheck) cfg.taylorDepth
  | sin a ih =>
      simp only [checkADDomain] at hcheck
      exact IntervalRat.mem_sinComputable (ih hcheck) cfg.taylorDepth
  | cos a ih =>
      simp only [checkADDomain] at hcheck
      exact IntervalRat.mem_cosComputable (ih hcheck) cfg.taylorDepth
  | log a ih =>
      simp only [checkADDomain, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      exact IntervalRat.mem_logComputable (ih hcheck.1) hcheck.2 cfg.taylorDepth
  | atan | arsinh | atanh | sinc | erf | sinh | cosh | tanh | sqrt | namedConst =>
      simp [checkADDomain] at hcheck

/-- Successful checked dual evaluation encloses the expression value for every
real environment represented by the dual environment. -/
theorem evalDualChecked_val_correct (e : Expr)
    (ρReal : Nat → ℝ) (ρDual : DualEnv) (cfg : EvalConfig) (D : DualInterval)
    (hρ : ∀ i, ρReal i ∈ (ρDual i).val)
    (hok : evalDualChecked e ρDual cfg = .ok D) :
    Expr.eval ρReal e ∈ D.val := by
  rw [evalDualChecked_ok_eq hok]
  exact evalTotalCore_val_correct_of_check e ρReal ρDual cfg hρ
    (checkADDomain_of_evalDualChecked_ok hok)

private theorem evalAlong_differentiableAt_of_check (e : Expr)
    (ρReal : Nat → ℝ) (ρInt : IntervalEnv) (idx : Nat) (cfg : EvalConfig)
    (x : ℝ) (hx : x ∈ ρInt idx) (hρ : ∀ i, ρReal i ∈ ρInt i)
    (hcheck : checkADDomain e (mkDualEnv ρInt idx) cfg = true) :
    DifferentiableAt ℝ (Expr.evalAlong e ρReal idx) x := by
  have hmem : ∀ i, Expr.updateVar ρReal idx x i ∈ (mkDualEnv ρInt idx i).val :=
    updateVar_mem_mkDualEnv_val ρReal ρInt idx x hx hρ
  induction e with
  | const => exact differentiableAt_const _
  | var i =>
      by_cases hi : i = idx
      · subst i
        simpa only [Expr.evalAlong_var_active] using differentiableAt_id
      · simpa only [Expr.evalAlong_var_passive _ _ _ hi] using differentiableAt_const (c := ρReal i)
  | add a b iha ihb =>
      simp only [checkADDomain, Bool.and_eq_true] at hcheck
      simpa only [Expr.evalAlong_add_pi] using (iha hcheck.1).add (ihb hcheck.2)
  | mul a b iha ihb =>
      simp only [checkADDomain, Bool.and_eq_true] at hcheck
      simpa only [Expr.evalAlong_mul_pi] using (iha hcheck.1).mul (ihb hcheck.2)
  | neg a ih =>
      simp only [checkADDomain] at hcheck
      simpa only [Expr.evalAlong_neg_pi] using (ih hcheck).neg
  | inv a ih =>
      simp only [checkADDomain, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      have hval := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck.1
      have hne : Expr.evalAlong a ρReal idx x ≠ 0 := by
        rw [Expr.evalAlong_eq]
        intro hz
        rw [hz] at hval
        exact hcheck.2 ⟨by exact_mod_cast hval.1, by exact_mod_cast hval.2⟩
      exact DifferentiableAt.inv (ih hcheck.1) hne
  | exp a ih =>
      simp only [checkADDomain] at hcheck
      exact Real.differentiableAt_exp.comp x (ih hcheck)
  | sin a ih =>
      simp only [checkADDomain] at hcheck
      exact Real.differentiableAt_sin.comp x (ih hcheck)
  | cos a ih =>
      simp only [checkADDomain] at hcheck
      exact Real.differentiableAt_cos.comp x (ih hcheck)
  | log a ih =>
      simp only [checkADDomain, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      have hval := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck.1
      have hpos : 0 < Expr.evalAlong a ρReal idx x := by
        rw [Expr.evalAlong_eq]
        exact lt_of_lt_of_le (by exact_mod_cast hcheck.2) hval.1
      exact (Real.differentiableAt_log (ne_of_gt hpos)).comp x (ih hcheck.1)
  | atan | arsinh | atanh | sinc | erf | sinh | cosh | tanh | sqrt | namedConst =>
      simp [checkADDomain] at hcheck

/-- A successful checked evaluation proves differentiability at every point in
the input box along the selected coordinate. -/
theorem evalWithDerivChecked_differentiableAt (e : Expr)
    (ρReal : Nat → ℝ) (ρInt : IntervalEnv) (idx : Nat) (cfg : EvalConfig)
    (D : DualInterval) (x : ℝ) (hx : x ∈ ρInt idx)
    (hρ : ∀ i, ρReal i ∈ ρInt i)
    (hok : evalWithDerivChecked e ρInt idx cfg = .ok D) :
    DifferentiableAt ℝ (Expr.evalAlong e ρReal idx) x := by
  exact evalAlong_differentiableAt_of_check e ρReal ρInt idx cfg x hx hρ
    (checkADDomain_of_evalDualChecked_ok hok)

private theorem evalTotalCore_der_correct_idx_of_check (e : Expr)
    (ρReal : Nat → ℝ) (ρInt : IntervalEnv) (idx : Nat) (cfg : EvalConfig)
    (x : ℝ) (hx : x ∈ ρInt idx) (hρ : ∀ i, ρReal i ∈ ρInt i)
    (hcheck : checkADDomain e (mkDualEnv ρInt idx) cfg = true) :
    deriv (Expr.evalAlong e ρReal idx) x ∈
      (LeanCert.Internal.AD.evalTotalCore e (mkDualEnv ρInt idx) cfg).der := by
  have hmem : ∀ i, Expr.updateVar ρReal idx x i ∈ (mkDualEnv ρInt idx i).val :=
    updateVar_mem_mkDualEnv_val ρReal ρInt idx x hx hρ
  induction e with
  | const q =>
      simp only [Expr.evalAlong_const', deriv_const, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.const]
      exact_mod_cast IntervalRat.mem_singleton 0
  | var i =>
      by_cases hi : i = idx
      · subst i
        simp only [Expr.evalAlong_var_active, deriv_id, LeanCert.Internal.AD.evalTotalCore,
          mkDualEnv, ↓reduceIte, DualInterval.varActive]
        exact_mod_cast IntervalRat.mem_singleton 1
      · simp only [Expr.evalAlong_var_passive _ _ _ hi, deriv_const,
          LeanCert.Internal.AD.evalTotalCore, mkDualEnv, ite_eq_right hi, DualInterval.varPassive]
        exact_mod_cast IntervalRat.mem_singleton 0
  | add a b iha ihb =>
      simp only [checkADDomain, Bool.and_eq_true] at hcheck
      have hda := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck.1
      have hdb := evalAlong_differentiableAt_of_check b ρReal ρInt idx cfg x hx hρ hcheck.2
      simp only [Expr.evalAlong_add_pi, deriv_add hda hdb, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.add]
      exact IntervalRat.mem_add (iha hcheck.1) (ihb hcheck.2)
  | mul a b iha ihb =>
      simp only [checkADDomain, Bool.and_eq_true] at hcheck
      have hda := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck.1
      have hdb := evalAlong_differentiableAt_of_check b ρReal ρInt idx cfg x hx hρ hcheck.2
      simp only [Expr.evalAlong_mul_pi, deriv_mul hda hdb, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.mul]
      have hva := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck.1
      have hvb := evalTotalCore_val_correct_of_check b (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck.2
      exact IntervalRat.mem_add (IntervalRat.mem_mul (iha hcheck.1) hvb)
        (IntervalRat.mem_mul hva (ihb hcheck.2))
  | neg a ih =>
      simp only [checkADDomain] at hcheck
      have hd := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck
      simp only [Expr.evalAlong_neg_pi, deriv.neg, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.neg]
      exact IntervalRat.mem_neg (ih hcheck)
  | inv a ih =>
      simp only [checkADDomain, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      have hval := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck.1
      have hval' : Expr.evalAlong a ρReal idx x ∈
          (LeanCert.Internal.AD.evalTotalCore a (mkDualEnv ρInt idx) cfg).val := by
        simpa only [Expr.evalAlong_eq] using hval
      have hne : Expr.evalAlong a ρReal idx x ≠ 0 := by
        intro hz
        rw [hz] at hval'
        exact hcheck.2 ⟨by exact_mod_cast hval'.1, by exact_mod_cast hval'.2⟩
      have hd := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck.1
      rw [Expr.evalAlong_inv]
      have hcomp : (fun t => (Expr.evalAlong a ρReal idx t)⁻¹) =
          (fun y : ℝ => y⁻¹) ∘ Expr.evalAlong a ρReal idx := rfl
      rw [hcomp, deriv_comp x (hasDerivAt_inv hne).differentiableAt hd]
      simp only [(hasDerivAt_inv hne).deriv, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.inv]
      have hder := ih hcheck.1
      have hinv := mem_invInterval_nonzero hval' (not_containsZero_cases hcheck.2)
      have hneg := IntervalRat.mem_neg
        (IntervalRat.mem_mul hder (IntervalRat.mem_mul hinv hinv))
      convert hneg using 1
      field_simp
  | exp a ih =>
      simp only [checkADDomain] at hcheck
      have hd := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck
      simp only [Expr.evalAlong_exp, deriv_exp hd, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.expCore]
      have hval := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck
      exact IntervalRat.mem_mul (IntervalRat.mem_expComputable hval cfg.taylorDepth) (ih hcheck)
  | sin a ih =>
      simp only [checkADDomain] at hcheck
      have hd := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck
      simp only [Expr.evalAlong_sin, deriv_sin hd, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.sinCore]
      have hval := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck
      exact IntervalRat.mem_mul (IntervalRat.mem_cosComputable hval cfg.taylorDepth) (ih hcheck)
  | cos a ih =>
      simp only [checkADDomain] at hcheck
      have hd := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck
      simp only [Expr.evalAlong_cos, deriv_cos hd, LeanCert.Internal.AD.evalTotalCore,
        DualInterval.cosCore]
      have hval := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck
      exact IntervalRat.mem_mul
        (IntervalRat.mem_neg (IntervalRat.mem_sinComputable hval cfg.taylorDepth)) (ih hcheck)
  | log a ih =>
      simp only [checkADDomain, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      have hval := evalTotalCore_val_correct_of_check a (Expr.updateVar ρReal idx x)
        (mkDualEnv ρInt idx) cfg hmem hcheck.1
      have hval' : Expr.evalAlong a ρReal idx x ∈
          (LeanCert.Internal.AD.evalTotalCore a (mkDualEnv ρInt idx) cfg).val := by
        simpa only [Expr.evalAlong_eq] using hval
      have hpos : 0 < Expr.evalAlong a ρReal idx x :=
        lt_of_lt_of_le (by exact_mod_cast hcheck.2) hval'.1
      have hd := evalAlong_differentiableAt_of_check a ρReal ρInt idx cfg x hx hρ hcheck.1
      rw [Expr.evalAlong_log]
      have hcomp : (fun t => Real.log (Expr.evalAlong a ρReal idx t)) =
          Real.log ∘ Expr.evalAlong a ρReal idx := rfl
      rw [hcomp, deriv_comp x (Real.differentiableAt_log (ne_of_gt hpos)) hd]
      simp only [Real.deriv_log, LeanCert.Internal.AD.evalTotalCore, DualInterval.logCore]
      have hder := ih hcheck.1
      have hnz : ¬IntervalRat.containsZero
          (LeanCert.Internal.AD.evalTotalCore a (mkDualEnv ρInt idx) cfg).val := by
        intro hz
        exact (not_lt_of_ge hz.1) hcheck.2
      have hinv := mem_invInterval_nonzero hval' (not_containsZero_cases hnz)
      exact IntervalRat.mem_mul hinv hder
  | atan | arsinh | atanh | sinc | erf | sinh | cosh | tanh | sqrt | namedConst =>
      simp [checkADDomain] at hcheck

/-- Successful checked indexed AD encloses the true partial derivative. -/
theorem evalWithDerivChecked_der_correct (e : Expr)
    (ρReal : Nat → ℝ) (ρInt : IntervalEnv) (idx : Nat) (cfg : EvalConfig)
    (D : DualInterval) (x : ℝ) (hx : x ∈ ρInt idx)
    (hρ : ∀ i, ρReal i ∈ ρInt i)
    (hok : evalWithDerivChecked e ρInt idx cfg = .ok D) :
    deriv (Expr.evalAlong e ρReal idx) x ∈ D.der := by
  rw [evalDualChecked_ok_eq hok]
  exact evalTotalCore_der_correct_idx_of_check e ρReal ρInt idx cfg x hx hρ
    (checkADDomain_of_evalDualChecked_ok hok)

/-- Golden soundness theorem for the checked derivative-only API. -/
theorem derivIntervalChecked_correct (e : Expr)
    (ρReal : Nat → ℝ) (ρInt : IntervalEnv) (idx : Nat) (cfg : EvalConfig)
    (dI : IntervalRat) (x : ℝ) (hx : x ∈ ρInt idx)
    (hρ : ∀ i, ρReal i ∈ ρInt i)
    (hok : derivIntervalChecked e ρInt idx cfg = .ok dI) :
    deriv (Expr.evalAlong e ρReal idx) x ∈ dI := by
  simp only [derivIntervalChecked, bind, Except.bind] at hok
  cases hdual : evalWithDerivChecked e ρInt idx cfg with
  | error err => simp [hdual] at hok
  | ok D =>
      rw [hdual] at hok
      simp only [pure, Except.pure, Except.ok.injEq] at hok
      subst dI
      exact evalWithDerivChecked_der_correct e ρReal ρInt idx cfg D x hx hρ hdual

end LeanCert.Engine
