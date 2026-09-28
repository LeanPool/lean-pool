/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Engine.AD.Correctness
public import LeanPool.MovingSofa.LeanCert.Contrib.Sinc
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!
# Automatic Differentiation - Partial Correctness Theorems

This file proves the correctness of the partial dual evaluator `evalDual?`
which handles expressions with inv, log, and other domain-restricted functions.

## Main theorems

* `evalDual?_val_correct` - Value component is correct when evalDual? returns some
* `evalDual?1_val_correct` - Single-variable version
* `evalFunc1_differentiableAt_of_evalDual?` - Differentiability when evalDual? succeeds
* `evalDual?_der_correct` - Derivative component is correct
* `evalDual?1_correct` - Combined correctness theorem

## Design notes

All theorems are FULLY PROVED with no sorry or axioms.
The key insight is that when evalDual? returns `some`, the domain
constraints (nonzero for inv, positive for log) are satisfied.
-/

/-! ### Correctness of partial dual evaluator -/

@[expose] public section

namespace LeanCert.Engine

open LeanCert.Core Filter
open scoped Topology

/-- The value component of evalDual? is correct when it returns some.
    This theorem extends to expressions with inv. -/
theorem evalDual?_val_correct (e : Expr)
    (ρ_real : Nat → ℝ) (ρ_dual : DualEnv) (D : DualInterval)
    (hsome : evalDual? e ρ_dual = some D)
    (hρ : ∀ i, ρ_real i ∈ (ρ_dual i).val) :
    Expr.eval ρ_real e ∈ D.val := by
  induction e generalizing D with
  | const q =>
    simp only [evalDual?, Option.some.injEq] at hsome
    rw [← hsome]
    simp only [Expr.eval_const, DualInterval.const]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [evalDual?, Option.some.injEq] at hsome
    rw [← hsome]
    exact hρ idx
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [evalDual?] at hsome
    cases heq₁ : evalDual? e₁ ρ_dual with
    | none => simp only [heq₁, reduceCtorEq] at hsome
    | some d₁ =>
      cases heq₂ : evalDual? e₂ ρ_dual with
      | none => simp only [heq₁, heq₂, reduceCtorEq] at hsome
      | some d₂ =>
        simp only [heq₁, heq₂, Option.some.injEq] at hsome
        rw [← hsome]
        simp only [Expr.eval_add, DualInterval.add]
        exact IntervalRat.mem_add (ih₁ d₁ heq₁) (ih₂ d₂ heq₂)
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [evalDual?] at hsome
    cases heq₁ : evalDual? e₁ ρ_dual with
    | none => simp only [heq₁, reduceCtorEq] at hsome
    | some d₁ =>
      cases heq₂ : evalDual? e₂ ρ_dual with
      | none => simp only [heq₁, heq₂, reduceCtorEq] at hsome
      | some d₂ =>
        simp only [heq₁, heq₂, Option.some.injEq] at hsome
        rw [← hsome]
        simp only [Expr.eval_mul, DualInterval.mul]
        exact IntervalRat.mem_mul (ih₁ d₁ heq₁) (ih₂ d₂ heq₂)
  | neg e' ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_neg, DualInterval.neg]
      exact IntervalRat.mem_neg (ih d heq)
  | inv e' ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, DualInterval.inv?] at hsome
      split at hsome
      · simp at hsome
      · next hnotzero =>
        simp only [Option.some.injEq] at hsome
        rw [← hsome]
        simp only [Expr.eval_inv]
        have hmem := ih d heq
        -- The denominator is nonzero because d.val doesn't contain zero and eval ∈ d.val
        have heval_ne : Expr.eval ρ_real e' ≠ 0 := by
          intro heq_zero
          rw [heq_zero] at hmem
          simp only [IntervalRat.mem_def] at hmem
          simp only [IntervalRat.containsZero, not_and, not_le] at hnotzero
          rcases le_or_gt d.val.lo 0 with hlo | hlo
          · have hhi_nonneg : (0 : ℚ) ≤ d.val.hi := by
              have h : (0 : ℝ) ≤ d.val.hi := hmem.2
              exact_mod_cast h
            exact absurd (hnotzero hlo) (not_lt.mpr hhi_nonneg)
          · have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hlo
            exact absurd hmem.1 (not_le.mpr hlo_pos)
        exact IntervalRat.mem_invNonzero hmem heval_ne
  | sin e' ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_sin, DualInterval.sin]
      exact mem_sinInterval (ih d heq)
  | cos e' ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_cos, DualInterval.cos]
      exact mem_cosInterval (ih d heq)
  | exp e' ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_exp, DualInterval.exp]
      exact IntervalRat.mem_expInterval (ih d heq)
  | sinh e' ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_sinh, DualInterval.sinh, sinhInterval]
      exact IntervalRat.mem_sinhComputable (ih d heq) 10
  | cosh e' ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_cosh, DualInterval.cosh, coshInterval]
      exact IntervalRat.mem_coshComputable (ih d heq) 10
  | tanh _ _ =>
    simp only [evalDual?] at hsome
    cases hsome
  | log e' ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, DualInterval.log?] at hsome
      split at hsome
      · rename_i hpos
        simp only [Option.some.injEq] at hsome
        rw [← hsome]
        simp only [Expr.eval_log]
        have hJ_mem := ih d heq
        exact IntervalRat.mem_logInterval hJ_mem
      · contradiction
  | atan e' ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_atan, DualInterval.atan]
      exact mem_atanInterval (ih d heq)
  | arsinh e' ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_arsinh, DualInterval.arsinh]
      exact mem_arsinhInterval (ih d heq)
  | atanh _ _ =>
    -- evalDual? returns none for atanh, so hsome : none = some D is a contradiction
    simp only [evalDual?] at hsome
    contradiction
  | sinc e' ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_sinc, DualInterval.sinc]
      simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
      exact Real.sinc_mem_Icc _
  | erf e' ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [Expr.eval_erf, DualInterval.erf]
      simp only [IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
      exact Real.erf_mem_Icc _
  | sqrt e' ih =>
    simp only [evalDual?] at hsome
    cases heq : evalDual? e' ρ_dual with
    | none => simp only [heq, reduceCtorEq] at hsome
    | some d =>
      simp only [heq] at hsome
      -- hsome : DualInterval.sqrt? d = some D
      simp only [DualInterval.sqrt?] at hsome
      split at hsome
      · next hpos =>
        simp only [Option.some.injEq] at hsome
        rw [← hsome]
        simp only [Expr.eval_sqrt]
        exact IntervalRat.mem_sqrtInterval' (ih d heq)
      · exact absurd hsome (by simp)
  | namedConst c =>
    simp only [evalDual?, Option.some.injEq] at hsome
    rw [← hsome]
    simp only [Expr.eval_namedConst, DualInterval.ofMathConst]
    exact c.mem_interval

/-- Single-variable version of evalDual?_val_correct -/
theorem evalDual?1_val_correct (e : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDual?1 e I = some D) :
    Expr.eval (fun _ => x) e ∈ D.val := by
  apply evalDual?_val_correct e (fun _ => x) (fun _ => DualInterval.varActive I)
  · exact hsome
  · intro _; exact hx

/-- Helper lemma: evalFunc1 for inv unfolds correctly -/
theorem evalFunc1_inv (e : Expr) :
    evalFunc1 (Expr.inv e) = fun t => (evalFunc1 e t)⁻¹ := rfl

/-- Expressions with inv are differentiable when the denominator is nonzero. -/
theorem evalFunc1_differentiableAt_of_evalDual? (e : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDual?1 e I = some D) :
    DifferentiableAt ℝ (evalFunc1 e) x := by
  induction e generalizing D with
  | const q => exact differentiableAt_const _
  | var _ => exact differentiableAt_id
  | add e₁ e₂ ih₁ ih₂ =>
    unfold evalDual?1 evalDual? at hsome
    cases heq₁ : evalDual? e₁ _ with
    | none => rw [heq₁] at hsome; exact absurd hsome (by simp)
    | some d₁ =>
      cases heq₂ : evalDual? e₂ _ with
      | none => rw [heq₁, heq₂] at hsome; exact absurd hsome (by simp)
      | some d₂ =>
        exact DifferentiableAt.add (ih₁ d₁ heq₁) (ih₂ d₂ heq₂)
  | mul e₁ e₂ ih₁ ih₂ =>
    unfold evalDual?1 evalDual? at hsome
    cases heq₁ : evalDual? e₁ _ with
    | none => rw [heq₁] at hsome; exact absurd hsome (by simp)
    | some d₁ =>
      cases heq₂ : evalDual? e₂ _ with
      | none => rw [heq₁, heq₂] at hsome; exact absurd hsome (by simp)
      | some d₂ =>
        exact DifferentiableAt.mul (ih₁ d₁ heq₁) (ih₂ d₂ heq₂)
  | neg e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact DifferentiableAt.neg (ih d heq)
  | inv e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq] at hsome
      simp only [DualInterval.inv?] at hsome
      split at hsome
      · exact absurd hsome (by simp)
      · next hnotzero =>
        simp only [Option.some.injEq] at hsome
        have hval := evalDual?1_val_correct e' I d x hx heq
        -- Denominator is nonzero
        have hne : evalFunc1 e' x ≠ 0 := by
          intro heq_zero
          -- hval has type: Expr.eval (fun x_1 => x) e' ∈ d.val
          -- need to convert to: evalFunc1 e' x = 0
          have hval' : evalFunc1 e' x ∈ d.val := hval
          rw [heq_zero] at hval'
          simp only [IntervalRat.mem_def] at hval'
          simp only [IntervalRat.containsZero, not_and, not_le] at hnotzero
          rcases le_or_gt d.val.lo 0 with hlo | hlo
          · have hhi_nonneg : (0 : ℚ) ≤ d.val.hi := by
              have h : (0 : ℝ) ≤ d.val.hi := hval'.2
              exact_mod_cast h
            exact absurd (hnotzero hlo) (not_lt.mpr hhi_nonneg)
          · have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hlo
            exact absurd hval'.1 (not_le.mpr hlo_pos)
        exact DifferentiableAt.inv (ih d heq) hne
  | sin e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact Real.differentiableAt_sin.comp x (ih d heq)
  | cos e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact Real.differentiableAt_cos.comp x (ih d heq)
  | exp e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact Real.differentiableAt_exp.comp x (ih d heq)
  | sinh e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact (ih d heq).sinh
  | cosh e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact (ih d heq).cosh
  | tanh _ _ =>
    unfold evalDual?1 evalDual? at hsome
    contradiction
  | log e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq] at hsome
      simp only [DualInterval.log?] at hsome
      split at hsome
      · next hpos =>
        simp only [Option.some.injEq] at hsome
        have hval := evalDual?1_val_correct e' I d x hx heq
        -- The argument is positive, so log is differentiable
        have hpos_x : 0 < evalFunc1 e' x := by
          have hval' : evalFunc1 e' x ∈ d.val := hval
          simp only [IntervalRat.mem_def] at hval'
          simp only [IntervalRat.isPositive] at hpos
          have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hpos
          exact lt_of_lt_of_le hlo_pos hval'.1
        exact Real.differentiableAt_log (ne_of_gt hpos_x) |>.comp x (ih d heq)
      · exact absurd hsome (by simp)
  | atan e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact (Real.differentiable_arctan _).comp x (ih d heq)
  | arsinh e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      exact (Real.differentiable_arsinh _).comp x (ih d heq)
  | atanh _ _ =>
    -- evalDual? returns none for atanh, so hsome is a contradiction
    simp only [evalDual?1, evalDual?] at hsome
    contradiction
  | sinc e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      -- sinc is differentiable everywhere
      -- sinc = dslope sin 0, which is differentiable:
      -- - At x ≠ 0: sinc x = sin x / x is differentiable
      -- - At x = 0: sinc is differentiable with derivative 0 (from sin's Taylor series)
      have hsinc_diff : Differentiable ℝ Real.sinc := Real.differentiable_sinc
      exact hsinc_diff.differentiableAt.comp x (ih d heq)
  | erf e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      -- erf is differentiable everywhere using FTC
      -- erf(x) = (2/√π) * ∫₀ˣ exp(-t²) dt
      -- By FTC, the integral of a continuous function is differentiable
      have herf_diff : Differentiable ℝ Real.erf := by
        unfold Real.erf
        apply Differentiable.const_mul
        -- Use FTC: for continuous f, ∫ t in a..x, f t is differentiable in x
        intro y
        have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
          Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
        exact (hcont.integral_hasStrictDerivAt 0 y).hasStrictFDerivAt.differentiableAt
      exact herf_diff.differentiableAt.comp x (ih d heq)
  | sqrt e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq] at hsome
      simp only [DualInterval.sqrt?] at hsome
      split at hsome
      · next hpos =>
        simp only [Option.some.injEq] at hsome
        have hval := evalDual?1_val_correct e' I d x hx heq
        -- The argument is positive, so sqrt is differentiable
        have hpos_x : 0 < evalFunc1 e' x := by
          have hval' : evalFunc1 e' x ∈ d.val := hval
          simp only [IntervalRat.mem_def] at hval'
          simp only [IntervalRat.isPositive] at hpos
          have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hpos
          exact lt_of_lt_of_le hlo_pos hval'.1
        -- sqrt is differentiable at nonzero points
        have hne : evalFunc1 e' x ≠ 0 := ne_of_gt hpos_x
        exact (Real.hasDerivAt_sqrt hne).differentiableAt.comp x (ih d heq)
      · exact absurd hsome (by simp)
  | namedConst _ => exact differentiableAt_const _

/-- The derivative component of evalDual? is correct when it returns some.
    For a supported expression (with inv) evaluated at a point x in the interval I,
    the derivative of the expression lies in the computed derivative interval.

    This extends the AD correctness theorem to expressions with inv. -/
private theorem evalDual?_der_correct_inv (e' : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDual?1 (Expr.inv e') I = some D)
    (ih : ∀ D, evalDual?1 e' I = some D → deriv (evalFunc1 e') x ∈ D.der) :
    deriv (evalFunc1 (Expr.inv e')) x ∈ D.der := by
  unfold evalDual?1 evalDual? at hsome
  cases heq : evalDual? e' _ with
  | none => rw [heq] at hsome; exact absurd hsome (by simp)
  | some d =>
    rw [heq] at hsome
    simp only [DualInterval.inv?] at hsome
    split at hsome
    · exact absurd hsome (by simp)
    · next hnotzero =>
      simp only [Option.some.injEq] at hsome
      rw [← hsome]
      -- d(1/f) = -f'/f² = -f' * (1/f)²
      have hval := evalDual?1_val_correct e' I d x hx heq
      have hval' : evalFunc1 e' x ∈ d.val := hval
      have hne : evalFunc1 e' x ≠ 0 := by
        intro heq_zero
        rw [heq_zero] at hval'
        simp only [IntervalRat.mem_def] at hval'
        simp only [IntervalRat.containsZero, not_and, not_le] at hnotzero
        rcases le_or_gt d.val.lo 0 with hlo | hlo
        · have hhi_nonneg : (0 : ℚ) ≤ d.val.hi := by
            have h : (0 : ℝ) ≤ d.val.hi := hval'.2
            exact_mod_cast h
          exact absurd (hnotzero hlo) (not_lt.mpr hhi_nonneg)
        · have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hlo
          exact absurd hval'.1 (not_le.mpr hlo_pos)
      have hd := evalFunc1_differentiableAt_of_evalDual? e' I d x hx heq
      -- deriv (1/f) = deriv(f⁻¹ ∘ f) = -(f')/(f²) using chain rule
      -- We use: deriv (fun y => y⁻¹) (f x) * deriv f x = -(f x)⁻² * f'(x)
      rw [evalFunc1_inv]
      -- The goal is: deriv (fun t => (evalFunc1 e' t)⁻¹) x ∈ ...
      -- First show this equals the composition derivative
      have heq_fun : (fun t => (evalFunc1 e' t)⁻¹) = (fun y => y⁻¹) ∘ evalFunc1 e' := rfl
      rw [heq_fun, deriv_comp x (hasDerivAt_inv hne).differentiableAt hd]
      simp only [hasDerivAt_inv hne |>.deriv]
      -- Now goal is: -(evalFunc1 e' x ^ 2)⁻¹ * deriv (evalFunc1 e') x ∈ ...
      -- Which equals: -(deriv f * (1/f)²)
      have hder := ih d heq
      -- Construct the nonzero interval
      let I_nz : IntervalRat.IntervalRatNonzero := ⟨d.val, hnotzero⟩
      have hinv := IntervalRat.mem_invNonzero (I := I_nz) hval' hne
      have hinv_sq := IntervalRat.mem_mul hinv hinv
      have hprod := IntervalRat.mem_mul hder hinv_sq
      have hneg := IntervalRat.mem_neg hprod
      -- hneg : -(deriv (evalFunc1 e') x * ((evalFunc1 e' x)⁻¹ * (evalFunc1 e' x)⁻¹)) ∈ ...
      -- goal : -(evalFunc1 e' x ^ 2)⁻¹ * deriv (evalFunc1 e') x ∈ ...
      -- These are equal: -(a ^ 2)⁻¹ * b = -(b * (a⁻¹ * a⁻¹))
      have heq_val : -(evalFunc1 e' x ^ 2)⁻¹ * deriv (evalFunc1 e') x =
                     -(deriv (evalFunc1 e') x * ((evalFunc1 e' x)⁻¹ * (evalFunc1 e' x)⁻¹)) := by
        have h1 : (evalFunc1 e' x ^ 2)⁻¹ = (evalFunc1 e' x)⁻¹ * (evalFunc1 e' x)⁻¹ := by
          rw [sq, mul_inv]
        rw [h1]
        ring
      rw [heq_val]
      exact hneg

private theorem evalDual?_der_correct_log (e' : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDual?1 (Expr.log e') I = some D)
    (ih : ∀ D, evalDual?1 e' I = some D → deriv (evalFunc1 e') x ∈ D.der) :
    deriv (evalFunc1 (Expr.log e')) x ∈ D.der := by
  unfold evalDual?1 evalDual? at hsome
  cases heq : evalDual? e' _ with
  | none => rw [heq] at hsome; exact absurd hsome (by simp)
  | some d =>
    rw [heq] at hsome
    simp only [DualInterval.log?] at hsome
    split at hsome
    · next hpos =>
      simp only [Option.some.injEq] at hsome
      rw [← hsome]
      -- d(log f)/dx = f'/f
      have hval := evalDual?1_val_correct e' I d x hx heq
      have hval' : evalFunc1 e' x ∈ d.val := hval
      have hpos_x : 0 < evalFunc1 e' x := by
        simp only [IntervalRat.mem_def] at hval'
        simp only [IntervalRat.isPositive] at hpos
        have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hpos
        exact lt_of_lt_of_le hlo_pos hval'.1
      have hne_x : evalFunc1 e' x ≠ 0 := ne_of_gt hpos_x
      have hd := evalFunc1_differentiableAt_of_evalDual? e' I d x hx heq
      rw [evalFunc1_log]
      have heq_fun : (fun t => Real.log (evalFunc1 e' t)) = Real.log ∘ evalFunc1 e' := rfl
      rw [heq_fun, deriv_comp x (Real.differentiableAt_log hne_x) hd]
      simp only [Real.deriv_log (evalFunc1 e' x)]
      -- Goal: (evalFunc1 e' x)⁻¹ * deriv (evalFunc1 e') x ∈ ...
      -- From DualInterval.log?: der' := d.der * invNonzero d.val
      have hder := ih d heq
      -- Build the nonzero interval from the positive interval
      have hnotzero : ¬IntervalRat.containsZero d.val := by
        simp only [IntervalRat.containsZero, IntervalRat.isPositive] at hpos ⊢
        intro ⟨hle, _⟩
        exact absurd hpos (not_lt.mpr hle)
      let I_nz : IntervalRat.IntervalRatNonzero := ⟨d.val, hnotzero⟩
      have hinv := IntervalRat.mem_invNonzero (I := I_nz) hval' hne_x
      -- Need to show: (evalFunc1 e' x)⁻¹ * deriv (evalFunc1 e') x ∈ d.der * invNonzero d.val
      -- But mem_mul expects the arguments in different order, so use commutativity
      have hmul := IntervalRat.mem_mul hder hinv
      convert hmul using 1
      ring
    · exact absurd hsome (by simp)

private theorem evalDual?_der_correct_erf (e' : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDual?1 (Expr.erf e') I = some D)
    (ih : ∀ D, evalDual?1 e' I = some D → deriv (evalFunc1 e') x ∈ D.der) :
    deriv (evalFunc1 (Expr.erf e')) x ∈ D.der := by
  unfold evalDual?1 evalDual? at hsome
  cases heq : evalDual? e' _ with
  | none => rw [heq] at hsome; exact absurd hsome (by simp)
  | some d =>
    rw [heq, Option.some.injEq] at hsome
    rw [← hsome]
    simp only [DualInterval.erf]
    -- The derivative of erf ∘ f is (2/√π) * exp(-f(x)²) * f'(x)
    have hd_inner := evalFunc1_differentiableAt_of_evalDual? e' I d x hx heq
    have herf_diff : Differentiable ℝ Real.erf := by
      unfold Real.erf
      apply Differentiable.const_mul
      intro y
      have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
        Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
      exact (hcont.integral_hasStrictDerivAt 0 y).hasStrictFDerivAt.differentiableAt
    have heq_comp : (fun t => Real.erf (evalFunc1 e' t)) = Real.erf ∘ evalFunc1 e' := rfl
    rw [evalFunc1_erf, heq_comp, deriv_comp x herf_diff.differentiableAt hd_inner]
    -- deriv erf y = (2/√π) * exp(-y²) by FTC
    have hderiv_erf : ∀ y, deriv Real.erf y = (2 / Real.sqrt Real.pi) * Real.exp (-(y^2)) := by
      intro y
      unfold Real.erf
      rw [deriv_const_mul]
      · have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
          Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
        rw [(hcont.integral_hasStrictDerivAt 0 y).hasDerivAt.deriv]
      · have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
          Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
        exact (hcont.integral_hasStrictDerivAt 0 y).hasStrictFDerivAt.differentiableAt
    rw [hderiv_erf]
    -- Now goal: (2/√π) * exp(-(f(x))²) * f'(x) ∈ twoDivSqrtPi * expInterval(-val²) * der
    -- Factor: (2/√π) ∈ twoDivSqrtPi
    -- 2/√π ≈ 1.1284, twoDivSqrtPi = [1.128, 1.129]
    have hfactor : 2 / Real.sqrt Real.pi ∈ DualInterval.twoDivSqrtPi := by
      simp only [DualInterval.twoDivSqrtPi, IntervalRat.mem_def]
      -- From π bounds: 3.1415 < π < 3.1416 (Real.pi_gt_d4, Real.pi_lt_d4)
      -- So √π is between √3.1415 ≈ 1.7724 and √3.1416 ≈ 1.7724
      -- Thus 2/√π is between 2/1.7725 ≈ 1.1283 and 2/1.7723 ≈ 1.1285
      have hpi_lo : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
      have hpi_hi : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
      have hsqrt_lo : (1.7724 : ℝ) < Real.sqrt Real.pi := by
        have h1 : (1.7724 : ℝ) ^ 2 < Real.pi := by
          have : (1.7724 : ℝ) ^ 2 = 3.14140176 := by ring
          linarith
        have h2 : (0 : ℝ) ≤ 1.7724 := by norm_num
        have h3 : (0 : ℝ) ≤ 1.7724 ^ 2 := by positivity
        calc (1.7724 : ℝ) = Real.sqrt (1.7724 ^ 2) := (Real.sqrt_sq h2).symm
          _ < Real.sqrt Real.pi := Real.sqrt_lt_sqrt h3 h1
      have hsqrt_hi : Real.sqrt Real.pi < (1.7725 : ℝ) := by
        have h1 : Real.pi < (1.7725 : ℝ) ^ 2 := by
          have : (1.7725 : ℝ) ^ 2 = 3.14175625 := by ring
          linarith
        have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
        rw [← Real.sqrt_sq (le_of_lt (by norm_num : (0 : ℝ) < 1.7725))]
        exact Real.sqrt_lt_sqrt (le_of_lt hpi_pos) h1
      constructor
      · -- Goal: ↑(1128 / 1000) ≤ 2 / √π
        have h1 : ((1128 / 1000 : ℚ) : ℝ) < 2 / 1.7725 := by norm_num
        have h2 : (2 : ℝ) / 1.7725 < 2 / Real.sqrt Real.pi := by
          apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2)
          · exact Real.sqrt_pos.mpr Real.pi_pos
          · exact hsqrt_hi
        exact le_of_lt (lt_trans h1 h2)
      · -- Goal: 2 / √π ≤ ↑(1129 / 1000)
        have h1 : 2 / Real.sqrt Real.pi < (2 : ℝ) / 1.7724 := by
          apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2)
          · norm_num
          · exact hsqrt_lo
        have h2 : (2 : ℝ) / 1.7724 < ((1129 / 1000 : ℚ) : ℝ) := by norm_num
        exact le_of_lt (lt_trans h1 h2)
    -- exp(-(f(x))²) ∈ expInterval(-val²)
    have hval := evalDual?1_val_correct e' I d x hx heq
    have hval_sq := IntervalRat.mem_mul hval hval
    have hneg_val_sq := IntervalRat.mem_neg hval_sq
    have hexp := IntervalRat.mem_expInterval hneg_val_sq
    -- f'(x) ∈ d.der
    have hder := ih d heq
    -- Combine: (2/√π) * exp(-f(x)²) ∈ twoDivSqrtPi * expInterval(-val²)
    have hprod1 := IntervalRat.mem_mul hfactor hexp
    -- Full product: ((2/√π) * exp(-f(x)²)) * f'(x) ∈ (twoDivSqrtPi * expInterval(-val²)) * der
    have hprod2 := IntervalRat.mem_mul hprod1 hder
    convert hprod2 using 1
    ring_nf

private theorem evalDual?_der_correct_sqrt (e' : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDual?1 (Expr.sqrt e') I = some D)
    (ih : ∀ D, evalDual?1 e' I = some D → deriv (evalFunc1 e') x ∈ D.der) :
    deriv (evalFunc1 (Expr.sqrt e')) x ∈ D.der := by
  unfold evalDual?1 evalDual? at hsome
  cases heq : evalDual? e' _ with
  | none => rw [heq] at hsome; exact absurd hsome (by simp)
  | some d =>
    rw [heq] at hsome
    simp only [DualInterval.sqrt?] at hsome
    split at hsome
    · next hpos =>
      simp only [Option.some.injEq] at hsome
      rw [← hsome]
      -- d(sqrt f)/dx = f'/(2*sqrt(f))
      have hval := evalDual?1_val_correct e' I d x hx heq
      have hval' : evalFunc1 e' x ∈ d.val := hval
      have hpos_x : 0 < evalFunc1 e' x := by
        simp only [IntervalRat.mem_def] at hval'
        simp only [IntervalRat.isPositive] at hpos
        have hlo_pos : (0 : ℝ) < d.val.lo := by exact_mod_cast hpos
        exact lt_of_lt_of_le hlo_pos hval'.1
      have hne_x : evalFunc1 e' x ≠ 0 := ne_of_gt hpos_x
      have hd := evalFunc1_differentiableAt_of_evalDual? e' I d x hx heq
      rw [evalFunc1_sqrt]
      have heq_fun : (fun t => Real.sqrt (evalFunc1 e' t)) = Real.sqrt ∘ evalFunc1 e' := rfl
      rw [heq_fun, deriv_comp x (Real.hasDerivAt_sqrt hne_x).differentiableAt hd]
      rw [(Real.hasDerivAt_sqrt hne_x).deriv]
      -- Goal: deriv (evalFunc1 e') x / (2 * √(evalFunc1 e' x)) ∈ d.der * sqrtDerivCoefBound
      have hder := ih d heq
      -- Show 1/(2*sqrt(f(x))) is in sqrtDerivCoefBound
      have hlo_le_val : (d.val.lo : ℝ) ≤ evalFunc1 e' x := by
        simp only [IntervalRat.mem_def] at hval'
        exact hval'.1
      have hlo_pos_real : (0 : ℝ) < (d.val.lo : ℚ) := by
        simp only [IntervalRat.isPositive] at hpos
        exact_mod_cast hpos
      -- Use our sqrtDerivCoef_bound theorem
      have hcoef_bound := DualInterval.sqrtDerivCoef_bound hlo_pos_real hlo_le_val
      -- The coefficient 1/(2*sqrt(f(x))) is positive and bounded
      have hcoef_pos : 0 ≤ 1 / (2 * Real.sqrt (evalFunc1 e' x)) := by
        apply div_nonneg (by norm_num)
        apply mul_nonneg (by norm_num)
        exact le_of_lt (Real.sqrt_pos.mpr hpos_x)
      have hcoef_mem : 1 / (2 * Real.sqrt (evalFunc1 e' x)) ∈ DualInterval.sqrtDerivCoefBound
        d.val.lo hpos := by
        simp only [DualInterval.sqrtDerivCoefBound, IntervalRat.mem_def]
        split
        · -- d.val.lo ≤ 1
          next hle_one =>
          constructor
          · simp only [Rat.cast_zero]
            exact hcoef_pos
          · -- Show 1/(2*sqrt(f(x))) ≤ 1/(2*lo)
            have hle_real : (d.val.lo : ℝ) ≤ 1 := by exact_mod_cast hle_one
            have h1 : max (1 / (2 * (d.val.lo : ℝ))) (1 / 2) = 1 / (2 * (d.val.lo : ℝ)) := by
              apply max_eq_left
              -- 1/2 ≤ 1/(2*lo) when lo ≤ 1
              apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
              calc 2 * (d.val.lo : ℝ) ≤ 2 * 1 := by nlinarith
                _ = 2 := by ring
            calc 1 / (2 * Real.sqrt (evalFunc1 e' x))
                ≤ max (1 / (2 * (d.val.lo : ℝ))) (1 / 2) := hcoef_bound
              _ = 1 / (2 * (d.val.lo : ℝ)) := h1
              _ = ↑(1 / (2 * d.val.lo)) := by push_cast; ring
        · -- d.val.lo > 1
          next hgt_one =>
          push Not at hgt_one
          constructor
          · simp only [Rat.cast_zero]
            exact hcoef_pos
          · -- Show 1/(2*sqrt(f(x))) ≤ 1/2
            have hgt_real : 1 < (d.val.lo : ℝ) := by exact_mod_cast hgt_one
            have h1 : max (1 / (2 * (d.val.lo : ℝ))) (1 / 2) = 1 / 2 := by
              apply max_eq_right
              -- 1/(2*lo) ≤ 1/2 when lo > 1
              apply div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0:ℝ) < 2)
              calc (2 : ℝ) = 2 * 1 := by ring
                _ ≤ 2 * d.val.lo := by nlinarith
            calc 1 / (2 * Real.sqrt (evalFunc1 e' x))
                ≤ max (1 / (2 * (d.val.lo : ℝ))) (1 / 2) := hcoef_bound
              _ = 1 / 2 := h1
              _ = ↑(1 / 2 : ℚ) := by norm_num
      -- Combine: f'(x)/(2*sqrt(f(x))) = f'(x) * (1/(2*sqrt(f(x)))) ∈ d.der * sqrtDerivCoefBound
      have hmul := IntervalRat.mem_mul hder hcoef_mem
      convert hmul using 1
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hpos_x)]
    · exact absurd hsome (by simp)

theorem evalDual?_der_correct (e : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDual?1 e I = some D) :
    deriv (evalFunc1 e) x ∈ D.der := by
  induction e generalizing D with
  | const q =>
    simp only [evalDual?1, evalDual?, Option.some.injEq] at hsome
    rw [← hsome]
    simp only [evalFunc1_const, deriv_const, DualInterval.const]
    convert IntervalRat.mem_singleton 0 using 1
    norm_cast
  | var _ =>
    simp only [evalDual?1, evalDual?, Option.some.injEq] at hsome
    rw [← hsome]
    simp only [evalFunc1_var, deriv_id, DualInterval.varActive]
    convert IntervalRat.mem_singleton 1 using 1
    norm_cast
  | add e₁ e₂ ih₁ ih₂ =>
    unfold evalDual?1 evalDual? at hsome
    cases heq₁ : evalDual? e₁ _ with
    | none => rw [heq₁] at hsome; exact absurd hsome (by simp)
    | some d₁ =>
      cases heq₂ : evalDual? e₂ _ with
      | none => rw [heq₁, heq₂] at hsome; exact absurd hsome (by simp)
      | some d₂ =>
        rw [heq₁, heq₂, Option.some.injEq] at hsome
        rw [← hsome]
        simp only [DualInterval.add]
        have hd₁ := evalFunc1_differentiableAt_of_evalDual? e₁ I d₁ x hx heq₁
        have hd₂ := evalFunc1_differentiableAt_of_evalDual? e₂ I d₂ x hx heq₂
        simp only [evalFunc1_add_pi, deriv_add hd₁ hd₂]
        exact IntervalRat.mem_add (ih₁ d₁ heq₁) (ih₂ d₂ heq₂)
  | mul e₁ e₂ ih₁ ih₂ =>
    unfold evalDual?1 evalDual? at hsome
    cases heq₁ : evalDual? e₁ _ with
    | none => rw [heq₁] at hsome; exact absurd hsome (by simp)
    | some d₁ =>
      cases heq₂ : evalDual? e₂ _ with
      | none => rw [heq₁, heq₂] at hsome; exact absurd hsome (by simp)
      | some d₂ =>
        rw [heq₁, heq₂, Option.some.injEq] at hsome
        rw [← hsome]
        simp only [DualInterval.mul]
        have hd₁ := evalFunc1_differentiableAt_of_evalDual? e₁ I d₁ x hx heq₁
        have hd₂ := evalFunc1_differentiableAt_of_evalDual? e₂ I d₂ x hx heq₂
        simp only [evalFunc1_mul_pi, deriv_mul hd₁ hd₂]
        have hval₁ := evalDual?1_val_correct e₁ I d₁ x hx heq₁
        have hval₂ := evalDual?1_val_correct e₂ I d₂ x hx heq₂
        exact IntervalRat.mem_add (IntervalRat.mem_mul (ih₁ d₁ heq₁) hval₂)
                                  (IntervalRat.mem_mul hval₁ (ih₂ d₂ heq₂))
  | neg e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.neg, evalFunc1_neg_pi, deriv.neg]
      exact IntervalRat.mem_neg (ih d heq)
  | inv e' ih => exact evalDual?_der_correct_inv e' I D x hx hsome ih
  | sin e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.sin]
      have hd := evalFunc1_differentiableAt_of_evalDual? e' I d x hx heq
      rw [evalFunc1_sin, deriv_sin hd]
      exact IntervalRat.mem_mul (cos_mem_cosInterval_of_any _ _) (ih d heq)
  | cos e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.cos]
      have hd := evalFunc1_differentiableAt_of_evalDual? e' I d x hx heq
      rw [evalFunc1_cos, deriv_cos hd]
      exact IntervalRat.mem_mul (neg_sin_mem_neg_sinInterval _ _) (ih d heq)
  | exp e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.exp]
      have hd := evalFunc1_differentiableAt_of_evalDual? e' I d x hx heq
      rw [evalFunc1_exp, deriv_exp hd]
      have hval := evalDual?1_val_correct e' I d x hx heq
      have hexp := IntervalRat.mem_expInterval hval
      exact IntervalRat.mem_mul hexp (ih d heq)
  | sinh e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.sinh, coshInterval]
      have hd := evalFunc1_differentiableAt_of_evalDual? e' I d x hx heq
      change deriv (fun t => Real.sinh (evalFunc1 e' t)) x ∈
        IntervalRat.mul (IntervalRat.coshComputable d.val 10) d.der
      have hder :
          HasDerivAt (fun t => Real.sinh (evalFunc1 e' t))
            (Real.cosh (evalFunc1 e' x) * deriv (evalFunc1 e') x) x :=
        (Real.hasDerivAt_sinh (evalFunc1 e' x)).comp x hd.hasDerivAt
      rw [hder.deriv]
      have hval := evalDual?1_val_correct e' I d x hx heq
      have hcosh := IntervalRat.mem_coshComputable hval 10
      exact IntervalRat.mem_mul hcosh (ih d heq)
  | cosh e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.cosh, sinhInterval]
      have hd := evalFunc1_differentiableAt_of_evalDual? e' I d x hx heq
      change deriv (fun t => Real.cosh (evalFunc1 e' t)) x ∈
        IntervalRat.mul (IntervalRat.sinhComputable d.val 10) d.der
      have hder :
          HasDerivAt (fun t => Real.cosh (evalFunc1 e' t))
            (Real.sinh (evalFunc1 e' x) * deriv (evalFunc1 e') x) x :=
        (Real.hasDerivAt_cosh (evalFunc1 e' x)).comp x hd.hasDerivAt
      rw [hder.deriv]
      have hval := evalDual?1_val_correct e' I d x hx heq
      have hsinh := IntervalRat.mem_sinhComputable hval 10
      exact IntervalRat.mem_mul hsinh (ih d heq)
  | tanh _ _ =>
    unfold evalDual?1 evalDual? at hsome
    contradiction
  | log e' ih => exact evalDual?_der_correct_log e' I D x hx hsome ih
  | atan e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.atan]
      have hd := evalFunc1_differentiableAt_of_evalDual? e' I d x hx heq
      rw [evalFunc1_atan]
      -- deriv (arctan ∘ f) x = (1 / (1 + f(x)²)) * f'(x)
      have heq_deriv := HasDerivAt.arctan (hd.hasDerivAt)
      rw [heq_deriv.deriv, mul_comm]
      -- The factor 1/(1+f(x)²) is in unitInterval
      have hfactor := DualInterval.arctan_deriv_factor_mem_unitInterval (evalFunc1 e' x)
      exact IntervalRat.mem_mul (ih d heq) hfactor
  | arsinh e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.arsinh]
      have hd := evalFunc1_differentiableAt_of_evalDual? e' I d x hx heq
      rw [evalFunc1_arsinh]
      -- deriv (arsinh ∘ f) x = (√(1 + f(x)²))⁻¹ • f'(x)
      have heq_deriv := HasDerivAt.arsinh (hd.hasDerivAt)
      rw [heq_deriv.deriv, smul_eq_mul, mul_comm]
      -- The factor 1/√(1+f(x)²) is in unitInterval
      have hfactor := DualInterval.arsinh_deriv_factor_mem_unitInterval (evalFunc1 e' x)
      exact IntervalRat.mem_mul (ih d heq) hfactor
  | atanh _ _ =>
    -- evalDual? returns none for atanh, so hsome is a contradiction
    simp only [evalDual?1, evalDual?] at hsome
    contradiction
  | sinc e' ih =>
    unfold evalDual?1 evalDual? at hsome
    cases heq : evalDual? e' _ with
    | none => rw [heq] at hsome; exact absurd hsome (by simp)
    | some d =>
      rw [heq, Option.some.injEq] at hsome
      rw [← hsome]
      simp only [DualInterval.sinc]
      -- The derivative of sinc ∘ f is sinc'(f(x)) * f'(x)
      -- sinc'(y) ∈ [-1, 1] for all y, and f'(x) ∈ d.der
      have hd_inner := evalFunc1_differentiableAt_of_evalDual? e' I d x hx heq
      have heq_comp : (fun t => Real.sinc (evalFunc1 e' t)) = Real.sinc ∘ evalFunc1 e' := rfl
      rw [evalFunc1_sinc, heq_comp, deriv_comp x Real.differentiable_sinc.differentiableAt hd_inner]
      -- deriv sinc (evalFunc1 e' x) * deriv (evalFunc1 e') x ∈ sincDerivBound * d.der
      have hsinc_bound : deriv Real.sinc (evalFunc1 e' x) ∈ DualInterval.sincDerivBound := by
        simp only [DualInterval.sincDerivBound, IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
        exact Real.deriv_sinc_mem_Icc (evalFunc1 e' x)
      have hder := ih d heq
      exact IntervalRat.mem_mul hsinc_bound hder
  | erf e' ih => exact evalDual?_der_correct_erf e' I D x hx hsome ih
  | sqrt e' ih => exact evalDual?_der_correct_sqrt e' I D x hx hsome ih
  | namedConst c =>
    simp only [evalDual?1, evalDual?, Option.some.injEq] at hsome
    rw [← hsome]
    simp only [evalFunc1_namedConst, deriv_const, DualInterval.ofMathConst]
    convert IntervalRat.mem_singleton 0 using 1
    norm_cast

/-- Combined correctness theorem for evalDual?1 -/
theorem evalDual?1_correct (e : Expr)
    (I : IntervalRat) (D : DualInterval) (x : ℝ) (hx : x ∈ I)
    (hsome : evalDual?1 e I = some D) :
    Expr.eval (fun _ => x) e ∈ D.val ∧ deriv (evalFunc1 e) x ∈ D.der :=
  ⟨evalDual?1_val_correct e I D x hx hsome, evalDual?_der_correct e I D x hx hsome⟩

end LeanCert.Engine
