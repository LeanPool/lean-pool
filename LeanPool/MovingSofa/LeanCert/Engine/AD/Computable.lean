/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Engine.AD.Correctness
/-!
# Automatic Differentiation - Computable Evaluators

This file provides computable dual evaluators using Taylor-based approximations
for transcendental functions. This enables `native_decide` for derivative-based
bound checking.

## Main definitions

* `DualInterval.expCore`, `sinCore`, `cosCore` - Taylor-based dual functions
* `DualInterval.sinhCore`, `coshCore`, `tanhCore` - Hyperbolic Taylor-based duals
* `LeanCert.Internal.AD.evalTotalCore` - Computable dual evaluator for ExprSupportedCore
* `derivIntervalCore` - Computable single-variable derivative interval

## Main theorems

* `LeanCert.Engine.evalDualTotalCore_val_correct` - Value component is correct
* `LeanCert.Engine.evalDualTotalCore_der_correct` - Derivative component is correct
* `derivIntervalCore_correct` - Derivative interval correctness
* `strictMonoOn_of_derivIntervalCore_pos` - Monotonicity from positive derivative
* `strictAntiOn_of_derivIntervalCore_neg` - Antitonicity from negative derivative
-/

/-! ### Computable Dual Evaluation for ExprSupportedCore

This section provides a fully computable dual evaluator that uses Taylor-based
approximations for transcendental functions. This enables `native_decide` for
derivative-based bound checking.
-/

@[expose] public section

namespace LeanCert.Engine

open LeanCert.Core Filter
open scoped Topology

namespace DualInterval

/-- Computable dual for exp using Taylor series (chain rule: d(exp f) = exp(f) * f') -/
def expCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  let expVal := IntervalRat.expComputable d.val n
  { val := expVal
    der := IntervalRat.mul expVal d.der }

/-- Computable dual for sin using Taylor series -/
def sinCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  { val := IntervalRat.sinComputable d.val n
    der := IntervalRat.mul (IntervalRat.cosComputable d.val n) d.der }

/-- Computable dual for cos using Taylor series -/
def cosCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  { val := IntervalRat.cosComputable d.val n
    der := IntervalRat.mul (IntervalRat.neg (IntervalRat.sinComputable d.val n)) d.der }

/-- Computable dual for log using Taylor series via atanh reduction.
    Chain rule: d(log f) = f' / f -/
def logCore (d : DualInterval) (n : ℕ := 20) : DualInterval :=
  { val := IntervalRat.logComputable d.val n
    -- der = d.der / d.val = d.der * (1/d.val)
    der := IntervalRat.mul (invInterval d.val) d.der }

/-- Computable dual for sinh using Taylor series (chain rule: d(sinh f) = cosh(f) * f') -/
def sinhCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  { val := IntervalRat.sinhComputable d.val n
    der := IntervalRat.mul (IntervalRat.coshComputable d.val n) d.der }

/-- Computable dual for cosh using Taylor series (chain rule: d(cosh f) = sinh(f) * f') -/
def coshCore (d : DualInterval) (n : ℕ := 10) : DualInterval :=
  { val := IntervalRat.coshComputable d.val n
    der := IntervalRat.mul (IntervalRat.sinhComputable d.val n) d.der }

/-- Computable dual for tanh (chain rule: d(tanh f) = sech²(f) * f')
    Since sech²(x) ∈ (0, 1], we use [0, 1] as a conservative bound. -/
def tanhCore (d : DualInterval) (_n : ℕ := 10) : DualInterval :=
  { val := tanhInterval d.val
    -- tanh'(x) = sech²(x) ∈ (0, 1], use [0, 1] as bound
    der := IntervalRat.mul d.der ⟨0, 1, by norm_num⟩ }

end DualInterval

end LeanCert.Engine

namespace LeanCert.Internal.AD

open LeanCert.Core LeanCert.Engine

/-- Computable dual interval evaluator for ExprSupportedCore expressions.

    This uses Taylor series approximations for transcendental functions,
    making it fully computable and usable with `native_decide`.

    For `inv` and `log`, use `evalDualChecked` or the bounded-denominator
    `evalDualDyadicChecked`; they validate the actual input box before exposing
    this total kernel's result. Correctness is not claimed for unchecked
    partial-operation branches here. -/
def evalTotalCore (e : Expr) (ρ : DualEnv) (cfg : EvalConfig := {}) : DualInterval :=
  match e with
  | Expr.const q => DualInterval.const q
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ => DualInterval.add (LeanCert.Internal.AD.evalTotalCore e₁ ρ cfg)
    (LeanCert.Internal.AD.evalTotalCore e₂ ρ cfg)
  | Expr.mul e₁ e₂ => DualInterval.mul (LeanCert.Internal.AD.evalTotalCore e₁ ρ cfg)
    (LeanCert.Internal.AD.evalTotalCore e₂ ρ cfg)
  | Expr.neg e => DualInterval.neg (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
  | Expr.inv e => DualInterval.inv (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
  | Expr.exp e => DualInterval.expCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg) cfg.taylorDepth
  | Expr.sin e => DualInterval.sinCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg) cfg.taylorDepth
  | Expr.cos e => DualInterval.cosCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg) cfg.taylorDepth
  | Expr.log e => DualInterval.logCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg) cfg.taylorDepth
  | Expr.atan e => DualInterval.atan (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
  | Expr.arsinh e => DualInterval.arsinh (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
  | Expr.atanh _ => default
  | Expr.sinc e => DualInterval.sinc (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
  | Expr.erf e => DualInterval.erfCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg) cfg.taylorDepth
  | Expr.sinh e => DualInterval.sinhCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
    cfg.taylorDepth
  | Expr.cosh e => DualInterval.coshCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
    cfg.taylorDepth
  | Expr.tanh e => DualInterval.tanhCore (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
    cfg.taylorDepth
  | Expr.sqrt e => DualInterval.sqrt (LeanCert.Internal.AD.evalTotalCore e ρ cfg)
  | Expr.namedConst c => DualInterval.ofMathConst c

end LeanCert.Internal.AD

namespace LeanCert.Engine

open LeanCert.Core Filter
open scoped Topology

/-- Computable single-variable derivative interval -/
def derivIntervalCore (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  (LeanCert.Internal.AD.evalTotalCore e (fun _ => DualInterval.varActive I) cfg).der

/-- Domain validity for dual evaluation.
    This is defined directly in terms of LeanCert.Internal.AD.evalTotalCore to ensure compatibility.
    For log, we require the argument interval to have positive lower bound. -/
def evalDomainValidDual (e : Expr) (ρ : DualEnv) (cfg : EvalConfig := {}) : Prop :=
  match e with
  | Expr.const _ => True
  | Expr.var _ => True
  | Expr.add e₁ e₂ => evalDomainValidDual e₁ ρ cfg ∧ evalDomainValidDual e₂ ρ cfg
  | Expr.mul e₁ e₂ => evalDomainValidDual e₁ ρ cfg ∧ evalDomainValidDual e₂ ρ cfg
  | Expr.neg e => evalDomainValidDual e ρ cfg
  | Expr.inv e => evalDomainValidDual e ρ cfg
  | Expr.exp e => evalDomainValidDual e ρ cfg
  | Expr.sin e => evalDomainValidDual e ρ cfg
  | Expr.cos e => evalDomainValidDual e ρ cfg
  | Expr.log e => evalDomainValidDual e ρ cfg ∧ (LeanCert.Internal.AD.evalTotalCore e ρ
    cfg).val.lo > 0
  | Expr.atan e => evalDomainValidDual e ρ cfg
  | Expr.arsinh e => evalDomainValidDual e ρ cfg
  | Expr.atanh e => evalDomainValidDual e ρ cfg
  | Expr.sinc e => evalDomainValidDual e ρ cfg
  | Expr.erf e => evalDomainValidDual e ρ cfg
  | Expr.sinh e => evalDomainValidDual e ρ cfg
  | Expr.cosh e => evalDomainValidDual e ρ cfg
  | Expr.tanh e => evalDomainValidDual e ρ cfg
  | Expr.sqrt e => evalDomainValidDual e ρ cfg
  | Expr.namedConst _ => True

/-- Correctness theorem for computable dual value component.

    Note: Requires domain validity for log (positive argument interval). -/
theorem evalDualTotalCore_val_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (ρ_real : Nat → ℝ) (ρ_dual : DualEnv) (cfg : EvalConfig)
    (hρ : ∀ i, ρ_real i ∈ (ρ_dual i).val)
    (hdom : evalDomainValidDual e ρ_dual cfg) :
    Expr.eval ρ_real e ∈ (LeanCert.Internal.AD.evalTotalCore e ρ_dual cfg).val := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, LeanCert.Internal.AD.evalTotalCore, DualInterval.const]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [Expr.eval_var, LeanCert.Internal.AD.evalTotalCore]
    exact hρ idx
  | add _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_add, LeanCert.Internal.AD.evalTotalCore, DualInterval.add]
    exact IntervalRat.mem_add (ih₁ hdom.1) (ih₂ hdom.2)
  | mul _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_mul, LeanCert.Internal.AD.evalTotalCore, DualInterval.mul]
    exact IntervalRat.mem_mul (ih₁ hdom.1) (ih₂ hdom.2)
  | neg _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_neg, LeanCert.Internal.AD.evalTotalCore, DualInterval.neg]
    exact IntervalRat.mem_neg (ih hdom)
  | sin _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_sin, LeanCert.Internal.AD.evalTotalCore, DualInterval.sinCore]
    exact IntervalRat.mem_sinComputable (ih hdom) cfg.taylorDepth
  | cos _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_cos, LeanCert.Internal.AD.evalTotalCore, DualInterval.cosCore]
    exact IntervalRat.mem_cosComputable (ih hdom) cfg.taylorDepth
  | exp _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_exp, LeanCert.Internal.AD.evalTotalCore, DualInterval.expCore]
    exact IntervalRat.mem_expComputable (ih hdom) cfg.taylorDepth
  | sqrt _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_sqrt, LeanCert.Internal.AD.evalTotalCore, DualInterval.sqrt]
    exact IntervalRat.mem_sqrtInterval' (ih hdom)
  | sinh _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_sinh, LeanCert.Internal.AD.evalTotalCore, DualInterval.sinhCore]
    exact IntervalRat.mem_sinhComputable (ih hdom) cfg.taylorDepth
  | cosh _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_cosh, LeanCert.Internal.AD.evalTotalCore, DualInterval.coshCore]
    exact IntervalRat.mem_coshComputable (ih hdom) cfg.taylorDepth
  | tanh _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_tanh, LeanCert.Internal.AD.evalTotalCore, DualInterval.tanhCore]
    exact mem_tanhInterval (ih hdom)
  | erf _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_erf, LeanCert.Internal.AD.evalTotalCore, DualInterval.erfCore]
    simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
    exact Real.erf_mem_Icc _
  | log _ ih =>
    simp only [evalDomainValidDual] at hdom
    simp only [Expr.eval_log, LeanCert.Internal.AD.evalTotalCore, DualInterval.logCore]
    exact IntervalRat.mem_logComputable (ih hdom.1) hdom.2 cfg.taylorDepth
  | namedConst c =>
    simp only [Expr.eval_namedConst, LeanCert.Internal.AD.evalTotalCore, DualInterval.ofMathConst]
    exact c.mem_interval

/-- For ADSupported expressions (which exclude log), domain validity is trivially true.
    This is because ADSupported has no log constructor. -/
theorem evalDomainValidDual_of_ExprSupported (e : Expr) (hsupp : ADSupported e)
    (ρ : DualEnv) (cfg : EvalConfig) : evalDomainValidDual e ρ cfg := by
  induction hsupp with
  | const _ => trivial
  | var _ => trivial
  | add _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | mul _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | neg _ ih => exact ih
  | sin _ ih => exact ih
  | cos _ ih => exact ih
  | exp _ ih => exact ih

/-- Correctness theorem for computable dual derivative component.
    Uses ADSupported since derivative correctness requires differentiability. -/
theorem evalDualTotalCore_der_correct (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) (cfg : EvalConfig) :
    deriv (evalFunc1 e) x ∈ (LeanCert.Internal.AD.evalTotalCore e (fun _ => DualInterval.varActive
      I) cfg).der := by
  induction hsupp generalizing x with
  | const q =>
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.const, evalFunc1_const, deriv_const]
    convert IntervalRat.mem_singleton 0 using 1
    norm_cast
  | var _ =>
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.varActive, evalFunc1_var]
    rw [deriv_id]
    convert IntervalRat.mem_singleton 1 using 1
    norm_cast
  | add h₁ h₂ ih₁ ih₂ =>
    have hd₁ := evalFunc1_differentiable _ h₁
    have hd₂ := evalFunc1_differentiable _ h₂
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.add, evalFunc1_add_pi, deriv_add
      (hd₁ x) (hd₂ x)]
    exact IntervalRat.mem_add (ih₁ x hx) (ih₂ x hx)
  | mul h₁ h₂ ih₁ ih₂ =>
    have hd₁ := evalFunc1_differentiable _ h₁
    have hd₂ := evalFunc1_differentiable _ h₂
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.mul, evalFunc1_mul_pi, deriv_mul
      (hd₁ x) (hd₂ x)]
    have hdom₁ := evalDomainValidDual_of_ExprSupported _ h₁ (fun _ => DualInterval.varActive I) cfg
    have hdom₂ := evalDomainValidDual_of_ExprSupported _ h₂ (fun _ => DualInterval.varActive I) cfg
    have hval₁ := LeanCert.Engine.evalDualTotalCore_val_correct _ h₁.toCore (fun _ => x)
      (fun _ => DualInterval.varActive I) cfg (fun _ => hx) hdom₁
    have hval₂ := LeanCert.Engine.evalDualTotalCore_val_correct _ h₂.toCore (fun _ => x)
      (fun _ => DualInterval.varActive I) cfg (fun _ => hx) hdom₂
    exact IntervalRat.mem_add (IntervalRat.mem_mul (ih₁ x hx) hval₂) (IntervalRat.mem_mul hval₁
      (ih₂ x hx))
  | neg hs ih =>
    have hd := evalFunc1_differentiable _ hs
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.neg, evalFunc1_neg_pi, deriv.neg]
    exact IntervalRat.mem_neg (ih x hx)
  | @sin e' hs ih =>
    have hd := evalFunc1_differentiable e' hs
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.sinCore, evalFunc1_sin]
    rw [deriv_sin (hd.differentiableAt)]
    have hdom := evalDomainValidDual_of_ExprSupported e' hs (fun _ => DualInterval.varActive I) cfg
    have hval := LeanCert.Engine.evalDualTotalCore_val_correct e' hs.toCore (fun _ => x)
      (fun _ => DualInterval.varActive I) cfg (fun _ => hx) hdom
    have hcos := IntervalRat.mem_cosComputable hval cfg.taylorDepth
    exact IntervalRat.mem_mul hcos (ih x hx)
  | @cos e' hs ih =>
    have hd := evalFunc1_differentiable e' hs
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.cosCore, evalFunc1_cos]
    rw [deriv_cos (hd.differentiableAt)]
    have hdom := evalDomainValidDual_of_ExprSupported e' hs (fun _ => DualInterval.varActive I) cfg
    have hval := LeanCert.Engine.evalDualTotalCore_val_correct e' hs.toCore (fun _ => x)
      (fun _ => DualInterval.varActive I) cfg (fun _ => hx) hdom
    have hsin := IntervalRat.mem_sinComputable hval cfg.taylorDepth
    have hnegsin := IntervalRat.mem_neg hsin
    exact IntervalRat.mem_mul hnegsin (ih x hx)
  | @exp e' hs ih =>
    have hd := evalFunc1_differentiable e' hs
    simp only [LeanCert.Internal.AD.evalTotalCore, DualInterval.expCore, evalFunc1_exp]
    rw [deriv_exp (hd.differentiableAt)]
    have hdom := evalDomainValidDual_of_ExprSupported e' hs (fun _ => DualInterval.varActive I) cfg
    have hval := LeanCert.Engine.evalDualTotalCore_val_correct e' hs.toCore (fun _ => x)
      (fun _ => DualInterval.varActive I) cfg (fun _ => hx) hdom
    have hexp := IntervalRat.mem_expComputable hval cfg.taylorDepth
    exact IntervalRat.mem_mul hexp (ih x hx)

/-- Convenience theorem: derivIntervalCore correctness -/
theorem derivIntervalCore_correct (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) (cfg : EvalConfig) :
    deriv (evalFunc1 e) x ∈ derivIntervalCore e I cfg :=
  LeanCert.Engine.evalDualTotalCore_der_correct e hsupp I x hx cfg

/-- If derivIntervalCore doesn't contain zero, the derivative is nonzero everywhere on I.
    This is a key theorem for Newton contraction analysis. -/
theorem derivIntervalCore_nonzero_implies_deriv_nonzero (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h : ¬(derivIntervalCore e I cfg).containsZero) :
    ∀ x ∈ I, deriv (evalFunc1 e) x ≠ 0 := by
  intro x hx hcontra
  have hmem := derivIntervalCore_correct e hsupp I x hx cfg
  simp only [IntervalRat.mem_def] at hmem
  simp only [IntervalRat.containsZero, not_and_or, not_le] at h
  rw [hcontra] at hmem
  rcases h with hlo | hhi
  · exact absurd hmem.1 (not_le.mpr (by exact_mod_cast hlo))
  · exact absurd hmem.2 (not_le.mpr (by exact_mod_cast hhi))

/-- If derivIntervalCore.lo > 0, then the derivative is positive everywhere on I. -/
theorem derivIntervalCore_pos_implies_deriv_pos (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h : 0 < (derivIntervalCore e I cfg).lo) :
    ∀ x ∈ I, 0 < deriv (evalFunc1 e) x := by
  intro x hx
  have hmem := derivIntervalCore_correct e hsupp I x hx cfg
  simp only [IntervalRat.mem_def] at hmem
  calc (0 : ℝ) < (derivIntervalCore e I cfg).lo := by exact_mod_cast h
    _ ≤ deriv (evalFunc1 e) x := hmem.1

/-- If derivIntervalCore.hi < 0, then the derivative is negative everywhere on I. -/
theorem derivIntervalCore_neg_implies_deriv_neg (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h : (derivIntervalCore e I cfg).hi < 0) :
    ∀ x ∈ I, deriv (evalFunc1 e) x < 0 := by
  intro x hx
  have hmem := derivIntervalCore_correct e hsupp I x hx cfg
  simp only [IntervalRat.mem_def] at hmem
  calc deriv (evalFunc1 e) x ≤ (derivIntervalCore e I cfg).hi := hmem.2
    _ < 0 := by exact_mod_cast h

/-- Strictly positive derivative (via Core bounds) implies strict monotonicity -/
theorem strictMonoOn_of_derivIntervalCore_pos (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hpos : 0 < (derivIntervalCore e I cfg).lo) :
    StrictMonoOn (evalFunc1 e) (Set.Icc (I.lo : ℝ) (I.hi : ℝ)) := by
  have hdiff := evalFunc1_differentiable e hsupp
  have hderiv_pos := derivIntervalCore_pos_implies_deriv_pos e hsupp I cfg hpos
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx_mem : x ∈ I := by
      simp only [IntervalRat.mem_def]
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact hderiv_pos x hx_mem

/-- Strictly negative derivative (via Core bounds) implies strict antitonicity -/
theorem strictAntiOn_of_derivIntervalCore_neg (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hneg : (derivIntervalCore e I cfg).hi < 0) :
    StrictAntiOn (evalFunc1 e) (Set.Icc (I.lo : ℝ) (I.hi : ℝ)) := by
  have hdiff := evalFunc1_differentiable e hsupp
  have hderiv_neg := derivIntervalCore_neg_implies_deriv_neg e hsupp I cfg hneg
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hx_mem : x ∈ I := by
      simp only [IntervalRat.mem_def]
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact hderiv_neg x hx_mem

end LeanCert.Engine
