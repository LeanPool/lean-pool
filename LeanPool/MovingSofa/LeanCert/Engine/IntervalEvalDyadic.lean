/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Core.Expr
public import LeanPool.MovingSofa.LeanCert.Core.IntervalDyadic
public import LeanPool.MovingSofa.LeanCert.Engine.IntervalEval
/-!
# High-Performance Dyadic Interval Evaluator

This evaluator replaces `Rat` with `Dyadic` to prevent denominator explosion.
It is designed for complex expressions where the standard evaluator becomes slow.

## Main definitions

* `DyadicConfig` - Configuration for precision and Taylor depth
* `LeanCert.Internal.Dyadic.evalUnchecked` - Dyadic interval evaluator for expressions
* `evalIntervalDyadic_correct` - Correctness theorem

## Performance

In v1.0, every `Rat` multiplication required GCD normalization. For deep
expressions (e.g., Taylor series with 20+ terms, or optimization with 100+
iterations), denominators grow exponentially, causing timeouts.

In v1.1, Dyadic arithmetic uses bit-shifts instead of GCD. With `roundOut`,
we can enforce a maximum precision after each operation, keeping computation
bounded regardless of expression depth.

## Example

Consider computing `sin(sin(sin(x)))` with 15-term Taylor series:
- v1.0 (Rat): ~500ms per call, denominators grow to millions of digits
- v1.1 (Dyadic): ~5ms per call, precision stays at 53 bits

## Design notes

For transcendental functions (sin, cos, exp), we delegate to the existing
`IntervalRat` implementation with Taylor series, then convert the result
to `IntervalDyadic` with outward rounding. This reuses verified code while
gaining the performance benefits of Dyadic for polynomial operations.
-/

/-! ### Configuration -/

@[expose] public section

namespace LeanCert.Engine

open LeanCert.Core

/-- Configuration for Dyadic interval evaluation.

* `precision` - Minimum exponent for outward rounding. A value of -53 gives
  IEEE double-like precision (~15 decimal digits). Use -100 for higher precision.
* `taylorDepth` - Number of Taylor terms for transcendental functions.
-/
structure DyadicConfig where
  /-- Minimum exponent (higher = coarser). -53 ≈ IEEE double precision. -/
  precision : Int := -53
  /-- Number of Taylor series terms for transcendental functions -/
  taylorDepth : Nat := 10
  deriving Repr, DecidableEq

/-- Default configuration with IEEE double-like precision -/
instance : Inhabited DyadicConfig := ⟨{}⟩

/-- High-precision configuration for critical calculations -/
def DyadicConfig.highPrecision : DyadicConfig :=
  { precision := -100, taylorDepth := 20 }

/-- Fast configuration for rapid evaluation (lower precision) -/
def DyadicConfig.fast : DyadicConfig :=
  { precision := -30, taylorDepth := 8 }

/-! ### Variable Environment -/

/-- Variable assignment as Dyadic intervals -/
abbrev IntervalDyadicEnv := Nat → IntervalDyadic

/-- Convert a rational interval environment to Dyadic -/
def toDyadicEnv (ρ : IntervalEnv) (prec : Int := -53) : IntervalDyadicEnv :=
  fun i => IntervalDyadic.ofIntervalRat (ρ i) prec

/-! ### Transcendental Function Wrappers -/

/-- Compute sin interval using rational Taylor series, convert to Dyadic -/
def sinIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.sinComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- Compute cos interval using rational Taylor series, convert to Dyadic -/
def cosIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.cosComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- Compute exp interval using rational Taylor series, convert to Dyadic -/
def expIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.expComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- Compute sinh interval using rational Taylor series, convert to Dyadic -/
def sinhIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.sinhComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- Compute cosh interval using rational Taylor series, convert to Dyadic -/
def coshIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.coshComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- atan interval: global bound [-2, 2] -/
def atanIntervalDyadic (_I : IntervalDyadic) (_cfg : DyadicConfig) : IntervalDyadic :=
  let neg2 := Core.Dyadic.ofInt (-2)
  let pos2 := Core.Dyadic.ofInt 2
  ⟨neg2, pos2, by rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]; norm_num⟩

/-- tanh interval: global bound [-1, 1] -/
def tanhIntervalDyadic (_I : IntervalDyadic) (_cfg : DyadicConfig) : IntervalDyadic :=
  let neg1 := Core.Dyadic.ofInt (-1)
  let pos1 := Core.Dyadic.ofInt 1
  ⟨neg1, pos1, by rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]; norm_num⟩

/-- arsinh interval: wide box bound via rational arsinhInterval -/
def arsinhIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := arsinhInterval Irat
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- atanh interval: computable Taylor series via rational atanhComputable -/
def atanhIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.atanhComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- sinc interval: global bound [-1, 1] -/
def sincIntervalDyadic (_I : IntervalDyadic) (_cfg : DyadicConfig) : IntervalDyadic :=
  let neg1 := Core.Dyadic.ofInt (-1)
  let pos1 := Core.Dyadic.ofInt 1
  ⟨neg1, pos1, by rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]; norm_num⟩

/-- erf interval: global bound [-1, 1] -/
def erfIntervalDyadic (_I : IntervalDyadic) (_cfg : DyadicConfig) : IntervalDyadic :=
  let neg1 := Core.Dyadic.ofInt (-1)
  let pos1 := Core.Dyadic.ofInt 1
  ⟨neg1, pos1, by rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]; norm_num⟩

/-- Compute inv interval: convert to Rat, use invInterval, convert back to Dyadic -/
def invIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := invInterval Irat
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- sqrt interval: uses conservative bound [0, max(hi, 1)] -/
def sqrtIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.sqrt I cfg.precision

/-- log interval: conservative global bound.
    For any x > 0, log(x) ∈ (-∞, ∞), but we use a finite interval.
    For x ∈ [lo, hi] with lo > 0:
    - log is monotone, so log(x) ∈ [log(lo), log(hi)]
    - Legacy total-evaluator fallback; strict callers reject this domain -/
def logIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  -- Compute log using Taylor series via atanh reduction
  -- Convert to rational, compute, convert back with outward rounding
  let IRat := I.toIntervalRat
  if IRat.lo > 0 then
    let result := IntervalRat.logComputable IRat cfg.taylorDepth
    IntervalDyadic.ofIntervalRat result cfg.precision
  else
    -- Legacy heuristic sentinel for invalid input. It is not a sound log
    -- enclosure; `evalIntervalDyadicChecked` rejects this branch.
    ⟨Core.Dyadic.ofInt (-1000), Core.Dyadic.ofInt 1000, by simp [Dyadic.toRat_ofInt]⟩

/-- Real power from a cached logarithm interval.

    If `Real.log x ∈ logBase`, this computes an interval for
    `x ^ (p : ℝ)` as `exp(p * log x)` without recomputing `log x`.
    This is the hot-path primitive for cached finite sums with many terms of
    the form `x ^ q_k`. -/
def rpowFromCachedLogDyadic (logBase : IntervalDyadic) (p : ℚ)
    (cfg : DyadicConfig) : IntervalDyadic :=
  let pInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton p) cfg.precision
  let pLogBase := (IntervalDyadic.mul pInterval logBase).roundOut cfg.precision
  expIntervalDyadic pLogBase cfg

/-- Real power x^p for x > 0 and rational p, computed via exp(p * log(x)).

    For x ∈ [lo, hi] with lo > 0 and rational exponent p:
    - x^p = exp(p * log(x))
    - We compute log(x), multiply by p, then apply exp

    This is the key operation for BKLNW-style sums where terms are x^(1/k - 1/3). -/
def rpowIntervalDyadic (base : IntervalDyadic) (p : ℚ) (cfg : DyadicConfig) : IntervalDyadic :=
  -- x^p = exp(p * log(x)) for x > 0
  let logBase := logIntervalDyadic base cfg
  rpowFromCachedLogDyadic logBase p cfg

/-- Correctness of `rpowFromCachedLogDyadic`: a cached interval containing
    `Real.log x` is enough to enclose `x ^ p`. -/
theorem mem_rpowFromCachedLogDyadic {x : ℝ} {logBase : IntervalDyadic}
    (hlog : Real.log x ∈ logBase) (hx_pos : 0 < x)
    (p : ℚ) (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num) :
    x ^ (p : ℝ) ∈ rpowFromCachedLogDyadic logBase p cfg := by
  simp only [rpowFromCachedLogDyadic]
  rw [Real.rpow_def_of_pos hx_pos, mul_comm]
  have hp_mem : (p : ℝ) ∈
      IntervalDyadic.ofIntervalRat (IntervalRat.singleton p) cfg.precision := by
    apply IntervalDyadic.mem_ofIntervalRat
    · exact IntervalRat.mem_singleton p
    · exact hprec
  have hmul := IntervalDyadic.mem_mul hp_mem hlog
  have hmul_rounded := IntervalDyadic.roundOut_contains hmul cfg.precision
  simp only [expIntervalDyadic]
  have hrat := IntervalDyadic.mem_toIntervalRat.mp hmul_rounded
  have hexp := IntervalRat.mem_expComputable hrat cfg.taylorDepth
  exact IntervalDyadic.mem_ofIntervalRat hexp cfg.precision hprec

/-- Correctness of rpowIntervalDyadic: if x ∈ base and base.lo > 0, then x^p ∈ result -/
theorem mem_rpowIntervalDyadic {x : ℝ} {base : IntervalDyadic} (hx : x ∈ base)
    (hpos : base.toIntervalRat.lo > 0) (p : ℚ) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num) :
    x ^ (p : ℝ) ∈ rpowIntervalDyadic base p cfg := by
  simp only [rpowIntervalDyadic]
  have hx_pos : 0 < x := by
    have hlo := hx.1
    have hlo_pos : (0 : ℝ) < base.lo.toRat := by exact_mod_cast hpos
    linarith
  have hlog_mem : Real.log x ∈ logIntervalDyadic base cfg := by
    simp only [logIntervalDyadic, hpos, ↓reduceIte]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp hx
    have hlog := IntervalRat.mem_logComputable hrat hpos cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hlog cfg.precision hprec
  exact mem_rpowFromCachedLogDyadic hlog_mem hx_pos p cfg hprec

/-! ### Main Evaluator -/

end LeanCert.Engine

namespace LeanCert.Internal.Dyadic

open LeanCert.Core LeanCert.Engine

/-- High-performance Dyadic interval evaluator.

This is the core function for v1.1. It evaluates expressions using Dyadic
arithmetic for polynomial operations (add, mul, neg) and delegates to
rational Taylor series for transcendentals.

Returns an interval guaranteed to contain all possible values of the expression
when `ExprSupportedCore` holds. For other expressions, it computes conservative
fallbacks (e.g., inv/log), but the core correctness theorem does not apply. -/
def evalUnchecked (e : Expr) (ρ : IntervalDyadicEnv) (cfg : DyadicConfig := {}) : IntervalDyadic :=
  match e with
  | Expr.const q =>
      -- Convert rational constant to Dyadic interval with outward rounding
      IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) cfg.precision
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ =>
      let I₁ := LeanCert.Internal.Dyadic.evalUnchecked e₁ ρ cfg
      let I₂ := LeanCert.Internal.Dyadic.evalUnchecked e₂ ρ cfg
      (IntervalDyadic.add I₁ I₂).roundOut cfg.precision
  | Expr.mul e₁ e₂ =>
      let I₁ := LeanCert.Internal.Dyadic.evalUnchecked e₁ ρ cfg
      let I₂ := LeanCert.Internal.Dyadic.evalUnchecked e₂ ρ cfg
      (IntervalDyadic.mul I₁ I₂).roundOut cfg.precision
  | Expr.neg e =>
      let I := LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg
      IntervalDyadic.neg I  -- Negation doesn't increase precision
  | Expr.inv e => invIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.exp e => expIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.sin e => sinIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.cos e => cosIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.log e => logIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.atan e => atanIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.arsinh e => arsinhIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.atanh e => atanhIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.sinc e => sincIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.erf e => erfIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.sinh e => sinhIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.cosh e => coshIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.tanh e => tanhIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.sqrt e => sqrtIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg) cfg
  | Expr.namedConst c => IntervalDyadic.ofIntervalRat c.interval cfg.precision

end LeanCert.Internal.Dyadic

namespace LeanCert.Engine

open LeanCert.Core

/-! ### Correctness -/

/-- A real environment is contained in a Dyadic interval environment -/
def envMemDyadic (ρ_real : Nat → ℝ) (ρ_dyad : IntervalDyadicEnv) : Prop :=
  ∀ i, ρ_real i ∈ ρ_dyad i

/-- Domain validity for Dyadic evaluation.
    This is defined directly in terms of LeanCert.Internal.Dyadic.evalUnchecked to ensure
    compatibility.
    For log, we require the argument interval (converted to Rat) to have positive lower bound. -/
def evalDomainValidDyadic (e : Expr) (ρ : IntervalDyadicEnv) (cfg : DyadicConfig := {}) : Prop :=
  match e with
  | Expr.const _ => True
  | Expr.var _ => True
  | Expr.add e₁ e₂ => evalDomainValidDyadic e₁ ρ cfg ∧ evalDomainValidDyadic e₂ ρ cfg
  | Expr.mul e₁ e₂ => evalDomainValidDyadic e₁ ρ cfg ∧ evalDomainValidDyadic e₂ ρ cfg
  | Expr.neg e => evalDomainValidDyadic e ρ cfg
  | Expr.inv e => evalDomainValidDyadic e ρ cfg ∧
      ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.lo > 0 ∨
       (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.hi < 0)
  | Expr.exp e => evalDomainValidDyadic e ρ cfg
  | Expr.sin e => evalDomainValidDyadic e ρ cfg
  | Expr.cos e => evalDomainValidDyadic e ρ cfg
  | Expr.log e => evalDomainValidDyadic e ρ cfg ∧ (LeanCert.Internal.Dyadic.evalUnchecked e ρ
    cfg).toIntervalRat.lo > 0
  | Expr.atan e => evalDomainValidDyadic e ρ cfg
  | Expr.arsinh e => evalDomainValidDyadic e ρ cfg
  | Expr.atanh e => evalDomainValidDyadic e ρ cfg ∧
      (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.lo > -1 ∧
      (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.hi < 1
  | Expr.sinc e => evalDomainValidDyadic e ρ cfg
  | Expr.erf e => evalDomainValidDyadic e ρ cfg
  | Expr.sinh e => evalDomainValidDyadic e ρ cfg
  | Expr.cosh e => evalDomainValidDyadic e ρ cfg
  | Expr.tanh e => evalDomainValidDyadic e ρ cfg
  | Expr.sqrt e => evalDomainValidDyadic e ρ cfg
  | Expr.namedConst _ => True

/-- Computable (Bool) domain validity check for Dyadic evaluation. -/
def checkDomainValidDyadic (e : Expr) (ρ : IntervalDyadicEnv) (cfg : DyadicConfig := {}) : Bool :=
  match e with
  | Expr.const _ => true
  | Expr.var _ => true
  | Expr.add e₁ e₂ => checkDomainValidDyadic e₁ ρ cfg && checkDomainValidDyadic e₂ ρ cfg
  | Expr.mul e₁ e₂ => checkDomainValidDyadic e₁ ρ cfg && checkDomainValidDyadic e₂ ρ cfg
  | Expr.neg e => checkDomainValidDyadic e ρ cfg
  | Expr.inv e => checkDomainValidDyadic e ρ cfg &&
      (decide ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.lo > 0) ||
       decide ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.hi < 0))
  | Expr.exp e => checkDomainValidDyadic e ρ cfg
  | Expr.sin e => checkDomainValidDyadic e ρ cfg
  | Expr.cos e => checkDomainValidDyadic e ρ cfg
  | Expr.log e => checkDomainValidDyadic e ρ cfg &&
      decide ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.lo > 0)
  | Expr.atan e => checkDomainValidDyadic e ρ cfg
  | Expr.arsinh e => checkDomainValidDyadic e ρ cfg
  | Expr.atanh e => checkDomainValidDyadic e ρ cfg &&
      decide ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.lo > -1) &&
      decide ((LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat.hi < 1)
  | Expr.sinc e => checkDomainValidDyadic e ρ cfg
  | Expr.erf e => checkDomainValidDyadic e ρ cfg
  | Expr.sinh e => checkDomainValidDyadic e ρ cfg
  | Expr.cosh e => checkDomainValidDyadic e ρ cfg
  | Expr.tanh e => checkDomainValidDyadic e ρ cfg
  | Expr.sqrt e => checkDomainValidDyadic e ρ cfg
  | Expr.namedConst _ => true

theorem checkDomainValidDyadic_correct (e : Expr) (ρ : IntervalDyadicEnv) (cfg : DyadicConfig) :
    checkDomainValidDyadic e ρ cfg = true → evalDomainValidDyadic e ρ cfg := by
  induction e with
  | const _ => intro; trivial
  | var _ => intro; trivial
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [checkDomainValidDyadic, Bool.and_eq_true, evalDomainValidDyadic]
    intro ⟨h1, h2⟩; exact ⟨ih₁ h1, ih₂ h2⟩
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [checkDomainValidDyadic, Bool.and_eq_true, evalDomainValidDyadic]
    intro ⟨h1, h2⟩; exact ⟨ih₁ h1, ih₂ h2⟩
  | neg e ih =>
    simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | inv e ih =>
    simp only [checkDomainValidDyadic, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, evalDomainValidDyadic]
    intro ⟨h1, h2⟩; exact ⟨ih h1, h2⟩
  | exp e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | sin e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | cos e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | log e ih =>
    simp only [checkDomainValidDyadic, Bool.and_eq_true, decide_eq_true_eq, evalDomainValidDyadic]
    intro ⟨h1, h2⟩; exact ⟨ih h1, h2⟩
  | atan e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | arsinh e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | atanh e ih =>
    simp only [checkDomainValidDyadic, Bool.and_eq_true, decide_eq_true_eq, evalDomainValidDyadic]
    intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨ih h1, h2, h3⟩
  | sinc e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | erf e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | sinh e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | cosh e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | tanh e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | sqrt e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | namedConst _ => intro; trivial

end LeanCert.Engine

namespace LeanCert.Internal.Dyadic

open LeanCert.Core LeanCert.Engine

/-- Static data prepared once for repeated Dyadic evaluation.

The context is operation-independent: logarithm, exponential, trigonometric,
and inverse-hyperbolic kernels share certified constants and coefficient
families without changing the public evaluator configuration. -/
structure PreparedContext where
  /-- Precision and rounding settings shared by prepared interval computations. -/
  cfg : DyadicConfig
  /-- A precomputed rational enclosure of the natural logarithm of two. -/
  ln2 : IntervalRat
  /-- Precomputed rational coefficients for the exponential Taylor polynomial. -/
  expCoeffs : List ℚ
  /-- Precomputed rational coefficients for the sine Taylor polynomial. -/
  sinCoeffs : List ℚ
  /-- Precomputed rational coefficients for the cosine Taylor polynomial. -/
  cosCoeffs : List ℚ
  /-- Precomputed rational coefficients for the inverse hyperbolic tangent expansion. -/
  atanhCoeffs : List ℚ
  deriving Repr

/-- Deterministically prepare all configuration-dependent numerical data. -/
def prepareContext (cfg : DyadicConfig) : PreparedContext :=
  { cfg
    ln2 := IntervalRat.ln2Computable cfg.taylorDepth
    expCoeffs := IntervalRat.expTaylorCoeffs cfg.taylorDepth
    sinCoeffs := IntervalRat.sinTaylorCoeffs cfg.taylorDepth
    cosCoeffs := IntervalRat.cosTaylorCoeffs cfg.taylorDepth
    atanhCoeffs := IntervalRat.atanhTaylorCoeffs cfg.taylorDepth }

@[simp] theorem prepareContext_cfg (cfg : DyadicConfig) :
    (prepareContext cfg).cfg = cfg := rfl

/-- Logarithm kernel using the context's prepared certified constants. -/
def logIntervalPrepared (I : IntervalDyadic) (ctx : PreparedContext) : IntervalDyadic :=
  let IRat := I.toIntervalRat
  if IRat.lo > 0 then
    let result := IntervalRat.logComputablePrepared IRat ctx.cfg.taylorDepth ctx.ln2
      ctx.atanhCoeffs
    IntervalDyadic.ofIntervalRat result ctx.cfg.precision
  else
    ⟨Core.Dyadic.ofInt (-1000), Core.Dyadic.ofInt 1000, by simp [Dyadic.toRat_ofInt]⟩

theorem logIntervalPrepared_prepareContext (I : IntervalDyadic) (cfg : DyadicConfig) :
    logIntervalPrepared I (prepareContext cfg) = logIntervalDyadic I cfg := by
  simp [logIntervalPrepared, prepareContext, logIntervalDyadic,
    IntervalRat.logComputablePrepared_eq]

/-- Exponential kernel using the context's prepared Taylor coefficients. -/
def expIntervalPrepared (I : IntervalDyadic) (ctx : PreparedContext) : IntervalDyadic :=
  let result := IntervalRat.expComputableWithCoeffs I.toIntervalRat ctx.cfg.taylorDepth
    ctx.expCoeffs
  IntervalDyadic.ofIntervalRat result ctx.cfg.precision

theorem expIntervalPrepared_prepareContext (I : IntervalDyadic) (cfg : DyadicConfig) :
    expIntervalPrepared I (prepareContext cfg) = expIntervalDyadic I cfg := by
  simp [expIntervalPrepared, prepareContext, expIntervalDyadic,
    IntervalRat.expComputableWithCoeffs_eq]

/-- Sine kernel using the context's prepared Taylor coefficients. -/
def sinIntervalPrepared (I : IntervalDyadic) (ctx : PreparedContext) : IntervalDyadic :=
  let result := IntervalRat.sinComputableWithCoeffs I.toIntervalRat ctx.cfg.taylorDepth
    ctx.sinCoeffs
  IntervalDyadic.ofIntervalRat result ctx.cfg.precision

theorem sinIntervalPrepared_prepareContext (I : IntervalDyadic) (cfg : DyadicConfig) :
    sinIntervalPrepared I (prepareContext cfg) = sinIntervalDyadic I cfg := by
  simp [sinIntervalPrepared, prepareContext, sinIntervalDyadic,
    IntervalRat.sinComputableWithCoeffs_eq]

/-- Cosine kernel using the context's prepared Taylor coefficients. -/
def cosIntervalPrepared (I : IntervalDyadic) (ctx : PreparedContext) : IntervalDyadic :=
  let result := IntervalRat.cosComputableWithCoeffs I.toIntervalRat ctx.cfg.taylorDepth
    ctx.cosCoeffs
  IntervalDyadic.ofIntervalRat result ctx.cfg.precision

theorem cosIntervalPrepared_prepareContext (I : IntervalDyadic) (cfg : DyadicConfig) :
    cosIntervalPrepared I (prepareContext cfg) = cosIntervalDyadic I cfg := by
  simp [cosIntervalPrepared, prepareContext, cosIntervalDyadic,
    IntervalRat.cosComputableWithCoeffs_eq]

/-- Inverse-hyperbolic-tangent kernel using prepared Taylor coefficients. -/
def atanhIntervalPrepared (I : IntervalDyadic) (ctx : PreparedContext) : IntervalDyadic :=
  let result := IntervalRat.atanhComputableWithCoeffs I.toIntervalRat ctx.cfg.taylorDepth
    ctx.atanhCoeffs
  IntervalDyadic.ofIntervalRat result ctx.cfg.precision

theorem atanhIntervalPrepared_prepareContext (I : IntervalDyadic) (cfg : DyadicConfig) :
    atanhIntervalPrepared I (prepareContext cfg) = atanhIntervalDyadic I cfg := by
  simp [atanhIntervalPrepared, prepareContext, atanhIntervalDyadic,
    IntervalRat.atanhComputableWithCoeffs_eq]

/-- Evaluate an expression and its domain-validity bit in one traversal.
The value component is exactly `LeanCert.Internal.Dyadic.evalUnchecked`; the validity component is
exactly `checkDomainValidDyadic`. -/
def evalCached (e : Expr) (ρ : IntervalDyadicEnv)
    (cfg : DyadicConfig := {}) : IntervalDyadic × Bool :=
  match e with
  | .const q =>
      (IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) cfg.precision, true)
  | .var idx => (ρ idx, true)
  | .add e₁ e₂ =>
      let r₁ := LeanCert.Internal.Dyadic.evalCached e₁ ρ cfg
      let r₂ := LeanCert.Internal.Dyadic.evalCached e₂ ρ cfg
      ((IntervalDyadic.add r₁.1 r₂.1).roundOut cfg.precision, r₁.2 && r₂.2)
  | .mul e₁ e₂ =>
      let r₁ := LeanCert.Internal.Dyadic.evalCached e₁ ρ cfg
      let r₂ := LeanCert.Internal.Dyadic.evalCached e₂ ρ cfg
      ((IntervalDyadic.mul r₁.1 r₂.1).roundOut cfg.precision, r₁.2 && r₂.2)
  | .neg e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (IntervalDyadic.neg r.1, r.2)
  | .inv e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      let I := r.1.toIntervalRat
      (invIntervalDyadic r.1 cfg, r.2 && (decide (I.lo > 0) || decide (I.hi < 0)))
  | .exp e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (expIntervalDyadic r.1 cfg, r.2)
  | .sin e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (sinIntervalDyadic r.1 cfg, r.2)
  | .cos e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (cosIntervalDyadic r.1 cfg, r.2)
  | .log e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (logIntervalDyadic r.1 cfg, r.2 && decide (r.1.toIntervalRat.lo > 0))
  | .atan e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (atanIntervalDyadic r.1 cfg, r.2)
  | .arsinh e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (arsinhIntervalDyadic r.1 cfg, r.2)
  | .atanh e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      let I := r.1.toIntervalRat
      (atanhIntervalDyadic r.1 cfg,
        r.2 && decide (I.lo > -1) && decide (I.hi < 1))
  | .sinc e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (sincIntervalDyadic r.1 cfg, r.2)
  | .erf e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (erfIntervalDyadic r.1 cfg, r.2)
  | .sinh e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (sinhIntervalDyadic r.1 cfg, r.2)
  | .cosh e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (coshIntervalDyadic r.1 cfg, r.2)
  | .tanh e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (tanhIntervalDyadic r.1 cfg, r.2)
  | .sqrt e =>
      let r := LeanCert.Internal.Dyadic.evalCached e ρ cfg
      (sqrtIntervalDyadic r.1 cfg, r.2)
  | .namedConst c => (IntervalDyadic.ofIntervalRat c.interval cfg.precision, true)

/-- Prepared evaluator: identical certificate semantics to `evalCached`, but
configuration-dependent data is shared across every evaluation. -/
def evalPreparedCached (e : Expr) (ρ : IntervalDyadicEnv)
    (ctx : PreparedContext) : IntervalDyadic × Bool :=
  match e with
  | .const q =>
      (IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) ctx.cfg.precision, true)
  | .var idx => (ρ idx, true)
  | .add e₁ e₂ =>
      let r₁ := evalPreparedCached e₁ ρ ctx
      let r₂ := evalPreparedCached e₂ ρ ctx
      ((IntervalDyadic.add r₁.1 r₂.1).roundOut ctx.cfg.precision, r₁.2 && r₂.2)
  | .mul e₁ e₂ =>
      let r₁ := evalPreparedCached e₁ ρ ctx
      let r₂ := evalPreparedCached e₂ ρ ctx
      ((IntervalDyadic.mul r₁.1 r₂.1).roundOut ctx.cfg.precision, r₁.2 && r₂.2)
  | .neg e =>
      let r := evalPreparedCached e ρ ctx
      (IntervalDyadic.neg r.1, r.2)
  | .inv e =>
      let r := evalPreparedCached e ρ ctx
      let I := r.1.toIntervalRat
      (invIntervalDyadic r.1 ctx.cfg, r.2 && (decide (I.lo > 0) || decide (I.hi < 0)))
  | .exp e =>
      let r := evalPreparedCached e ρ ctx
      (expIntervalPrepared r.1 ctx, r.2)
  | .sin e =>
      let r := evalPreparedCached e ρ ctx
      (sinIntervalPrepared r.1 ctx, r.2)
  | .cos e =>
      let r := evalPreparedCached e ρ ctx
      (cosIntervalPrepared r.1 ctx, r.2)
  | .log e =>
      let r := evalPreparedCached e ρ ctx
      (logIntervalPrepared r.1 ctx, r.2 && decide (r.1.toIntervalRat.lo > 0))
  | .atan e =>
      let r := evalPreparedCached e ρ ctx
      (atanIntervalDyadic r.1 ctx.cfg, r.2)
  | .arsinh e =>
      let r := evalPreparedCached e ρ ctx
      (arsinhIntervalDyadic r.1 ctx.cfg, r.2)
  | .atanh e =>
      let r := evalPreparedCached e ρ ctx
      let I := r.1.toIntervalRat
      (atanhIntervalPrepared r.1 ctx,
        r.2 && decide (I.lo > -1) && decide (I.hi < 1))
  | .sinc e =>
      let r := evalPreparedCached e ρ ctx
      (sincIntervalDyadic r.1 ctx.cfg, r.2)
  | .erf e =>
      let r := evalPreparedCached e ρ ctx
      (erfIntervalDyadic r.1 ctx.cfg, r.2)
  | .sinh e =>
      let r := evalPreparedCached e ρ ctx
      (sinhIntervalDyadic r.1 ctx.cfg, r.2)
  | .cosh e =>
      let r := evalPreparedCached e ρ ctx
      (coshIntervalDyadic r.1 ctx.cfg, r.2)
  | .tanh e =>
      let r := evalPreparedCached e ρ ctx
      (tanhIntervalDyadic r.1 ctx.cfg, r.2)
  | .sqrt e =>
      let r := evalPreparedCached e ρ ctx
      (sqrtIntervalDyadic r.1 ctx.cfg, r.2)
  | .namedConst c =>
      (IntervalDyadic.ofIntervalRat c.interval ctx.cfg.precision, true)

end LeanCert.Internal.Dyadic

namespace LeanCert.Engine

open LeanCert.Core

theorem evalIntervalDyadicCached_fst (e : Expr) (ρ : IntervalDyadicEnv)
    (cfg : DyadicConfig := {}) :
    (LeanCert.Internal.Dyadic.evalCached e ρ cfg).1 = LeanCert.Internal.Dyadic.evalUnchecked e ρ
      cfg := by
  induction e <;> simp [LeanCert.Internal.Dyadic.evalCached,
    LeanCert.Internal.Dyadic.evalUnchecked, *]

theorem evalIntervalDyadicCached_snd (e : Expr) (ρ : IntervalDyadicEnv)
    (cfg : DyadicConfig := {}) :
    (LeanCert.Internal.Dyadic.evalCached e ρ cfg).2 = checkDomainValidDyadic e ρ cfg := by
  induction e <;>
    simp [LeanCert.Internal.Dyadic.evalCached, checkDomainValidDyadic,
      evalIntervalDyadicCached_fst, *]

theorem evalIntervalDyadicPreparedCached_fst (e : Expr) (ρ : IntervalDyadicEnv)
    (cfg : DyadicConfig := {}) :
    (LeanCert.Internal.Dyadic.evalPreparedCached e ρ
      (LeanCert.Internal.Dyadic.prepareContext cfg)).1 =
      LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg := by
  induction e <;>
    simp [LeanCert.Internal.Dyadic.evalPreparedCached,
      LeanCert.Internal.Dyadic.evalUnchecked,
      LeanCert.Internal.Dyadic.logIntervalPrepared_prepareContext,
      LeanCert.Internal.Dyadic.expIntervalPrepared_prepareContext,
      LeanCert.Internal.Dyadic.sinIntervalPrepared_prepareContext,
      LeanCert.Internal.Dyadic.cosIntervalPrepared_prepareContext,
      LeanCert.Internal.Dyadic.atanhIntervalPrepared_prepareContext, *]

theorem evalIntervalDyadicPreparedCached_snd (e : Expr) (ρ : IntervalDyadicEnv)
    (cfg : DyadicConfig := {}) :
    (LeanCert.Internal.Dyadic.evalPreparedCached e ρ
      (LeanCert.Internal.Dyadic.prepareContext cfg)).2 =
      checkDomainValidDyadic e ρ cfg := by
  induction e <;>
    simp [LeanCert.Internal.Dyadic.evalPreparedCached,
      checkDomainValidDyadic,
      evalIntervalDyadicPreparedCached_fst, *]

/-- Diagnose the first failed Dyadic domain check. -/
def diagnoseEvalIntervalDyadicFailure (e : Expr) (ρ : IntervalDyadicEnv)
    (cfg : DyadicConfig := {}) : EvalError :=
  match e with
  | .add e₁ e₂ | .mul e₁ e₂ =>
      if checkDomainValidDyadic e₁ ρ cfg then
        .nestedFailure "right operand" (diagnoseEvalIntervalDyadicFailure e₂ ρ cfg)
      else
        .nestedFailure "left operand" (diagnoseEvalIntervalDyadicFailure e₁ ρ cfg)
  | .neg e | .exp e | .sin e | .cos e | .atan e | .arsinh e | .sinc e |
      .erf e | .sinh e | .cosh e | .tanh e | .sqrt e =>
      .nestedFailure "unary operand" (diagnoseEvalIntervalDyadicFailure e ρ cfg)
  | .inv e =>
      if checkDomainValidDyadic e ρ cfg then
        .reciprocalContainsZero (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat
      else
        .nestedFailure "reciprocal operand" (diagnoseEvalIntervalDyadicFailure e ρ cfg)
  | .log e =>
      if checkDomainValidDyadic e ρ cfg then
        .logNonpositive (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat
      else
        .nestedFailure "logarithm operand" (diagnoseEvalIntervalDyadicFailure e ρ cfg)
  | .atanh e =>
      if checkDomainValidDyadic e ρ cfg then
        .atanhOutsideUnitBall (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).toIntervalRat
      else
        .nestedFailure "atanh operand" (diagnoseEvalIntervalDyadicFailure e ρ cfg)
  | .const _ | .var _ | .namedConst _ =>
      .unsupportedBackend "internal: total Dyadic expression unexpectedly failed"
termination_by e

/-- Checked Dyadic evaluator. The finite fallback branches of the legacy total
evaluator are never exposed after a failed domain check. -/
def evalIntervalDyadicChecked (e : Expr) (ρ : IntervalDyadicEnv)
    (cfg : DyadicConfig := {}) : EvalResult IntervalDyadic :=
  let cached := LeanCert.Internal.Dyadic.evalCached e ρ cfg
  if cached.2 then
    .ok cached.1
  else
    .error (diagnoseEvalIntervalDyadicFailure e ρ cfg)

/-- Domain validity is trivially true for ADSupported expressions (which exclude log). -/
theorem evalDomainValidDyadic_of_ExprSupported {e : Expr} (hsupp : ADSupported e)
    (ρ : IntervalDyadicEnv) (cfg : DyadicConfig := {}) : evalDomainValidDyadic e ρ cfg := by
  induction hsupp with
  | const _ => trivial
  | var _ => trivial
  | add _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | mul _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | neg _ ih => exact ih
  | sin _ ih => exact ih
  | cos _ ih => exact ih
  | exp _ ih => exact ih

/-- Fundamental correctness theorem for Dyadic evaluation.

This theorem states that for any supported expression and any real values
within the input intervals, the result of evaluating the expression is
contained in the computed Dyadic interval.

The proof follows the same structure as `evalIntervalCore_correct`, but
with additional steps for handling Dyadic ↔ Rat conversions and rounding.
Requires cfg.precision ≤ 0 (the default -53 satisfies this).

Note: Requires domain validity for log (positive argument interval). -/
theorem evalIntervalDyadic_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (ρ_real : Nat → ℝ) (ρ_dyad : IntervalDyadicEnv)
    (hρ : envMemDyadic ρ_real ρ_dyad) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic e ρ_dyad cfg) :
    Expr.eval ρ_real e ∈ LeanCert.Internal.Dyadic.evalUnchecked e ρ_dyad cfg := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, LeanCert.Internal.Dyadic.evalUnchecked]
    apply IntervalDyadic.mem_ofIntervalRat
    · exact IntervalRat.mem_singleton q
    · exact hprec
  | var idx =>
    simp only [Expr.eval_var, LeanCert.Internal.Dyadic.evalUnchecked]
    exact hρ idx
  | add _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_add, LeanCert.Internal.Dyadic.evalUnchecked]
    have h := IntervalDyadic.mem_add (ih₁ hdom.1) (ih₂ hdom.2)
    exact IntervalDyadic.roundOut_contains h cfg.precision
  | mul _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_mul, LeanCert.Internal.Dyadic.evalUnchecked]
    have h := IntervalDyadic.mem_mul (ih₁ hdom.1) (ih₂ hdom.2)
    exact IntervalDyadic.roundOut_contains h cfg.precision
  | neg _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_neg, LeanCert.Internal.Dyadic.evalUnchecked]
    exact IntervalDyadic.mem_neg (ih hdom)
  | sin _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sin, LeanCert.Internal.Dyadic.evalUnchecked, sinIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hsin := IntervalRat.mem_sinComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hsin cfg.precision hprec
  | cos _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_cos, LeanCert.Internal.Dyadic.evalUnchecked, cosIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hcos := IntervalRat.mem_cosComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hcos cfg.precision hprec
  | exp _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_exp, LeanCert.Internal.Dyadic.evalUnchecked, expIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hexp := IntervalRat.mem_expComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hexp cfg.precision hprec
  | sqrt _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sqrt, LeanCert.Internal.Dyadic.evalUnchecked, sqrtIntervalDyadic]
    exact IntervalDyadic.mem_sqrt' (ih hdom) cfg.precision
  | sinh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sinh, LeanCert.Internal.Dyadic.evalUnchecked, sinhIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hsinh := IntervalRat.mem_sinhComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hsinh cfg.precision hprec
  | cosh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_cosh, LeanCert.Internal.Dyadic.evalUnchecked, coshIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hcosh := IntervalRat.mem_coshComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hcosh cfg.precision hprec
  | @tanh e' _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_tanh, LeanCert.Internal.Dyadic.evalUnchecked, tanhIntervalDyadic]
    -- tanh x ∈ [-1, 1] for all x
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one]
    set x := Expr.eval ρ_real e' with hx
    constructor
    -- tanh x ≥ -1: use tanh = sinh/cosh, cosh > 0, and -cosh ≤ sinh
    · rw [Real.tanh_eq_sinh_div_cosh]
      have hcosh : Real.cosh x > 0 := Real.cosh_pos x
      rw [le_div_iff₀ hcosh, neg_one_mul]
      rw [Real.sinh_eq, Real.cosh_eq]
      have h1 : Real.exp x > 0 := Real.exp_pos x
      linarith
    -- tanh x ≤ 1: use sinh ≤ cosh (since exp(-x) > 0)
    · rw [Real.tanh_eq_sinh_div_cosh]
      have hcosh : Real.cosh x > 0 := Real.cosh_pos x
      rw [div_le_one₀ hcosh]
      rw [Real.sinh_eq, Real.cosh_eq]
      have h2 : Real.exp (-x) > 0 := Real.exp_pos (-x)
      linarith
  | @erf e' _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_erf, LeanCert.Internal.Dyadic.evalUnchecked, erfIntervalDyadic]
    -- erf x ∈ [-1, 1] for all x
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one]
    exact Real.erf_mem_Icc _
  | log _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_log, LeanCert.Internal.Dyadic.evalUnchecked, logIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom.1)
    -- hdom.2 gives us the positivity condition: IRat.lo > 0
    -- This makes the if-condition true, so we take the positive branch
    have hpos : (LeanCert.Internal.Dyadic.evalUnchecked _ ρ_dyad cfg).toIntervalRat.lo > 0 := hdom.2
    simp only [hpos, ↓reduceIte]
    have hlog := IntervalRat.mem_logComputable hrat hpos cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hlog cfg.precision hprec
  | namedConst c =>
    simp only [Expr.eval_namedConst, LeanCert.Internal.Dyadic.evalUnchecked]
    exact IntervalDyadic.mem_ofIntervalRat c.mem_interval cfg.precision hprec

/-- Correctness of Dyadic evaluation for every expression whose recursively
checked domain conditions hold. -/
theorem evalIntervalDyadic_correct_of_domain (e : Expr)
    (ρ_real : Nat → ℝ) (ρ_dyad : IntervalDyadicEnv)
    (hρ : envMemDyadic ρ_real ρ_dyad) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic e ρ_dyad cfg) :
    Expr.eval ρ_real e ∈ LeanCert.Internal.Dyadic.evalUnchecked e ρ_dyad cfg := by
  induction e with
  | const q =>
    simp only [Expr.eval_const, LeanCert.Internal.Dyadic.evalUnchecked]
    apply IntervalDyadic.mem_ofIntervalRat
    · exact IntervalRat.mem_singleton q
    · exact hprec
  | var idx =>
    simp only [Expr.eval_var, LeanCert.Internal.Dyadic.evalUnchecked]
    exact hρ idx
  | add _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_add, LeanCert.Internal.Dyadic.evalUnchecked]
    have h := IntervalDyadic.mem_add (ih₁ hdom.1) (ih₂ hdom.2)
    exact IntervalDyadic.roundOut_contains h cfg.precision
  | mul _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_mul, LeanCert.Internal.Dyadic.evalUnchecked]
    have h := IntervalDyadic.mem_mul (ih₁ hdom.1) (ih₂ hdom.2)
    exact IntervalDyadic.roundOut_contains h cfg.precision
  | neg _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_neg, LeanCert.Internal.Dyadic.evalUnchecked]
    exact IntervalDyadic.mem_neg (ih hdom)
  | inv _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_inv, LeanCert.Internal.Dyadic.evalUnchecked, invIntervalDyadic]
    have hinner := ih hdom.1
    have hrat := IntervalDyadic.mem_toIntervalRat.mp hinner
    have hinv := mem_invInterval_nonzero hrat hdom.2
    exact IntervalDyadic.mem_ofIntervalRat hinv cfg.precision hprec
  | exp _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_exp, LeanCert.Internal.Dyadic.evalUnchecked, expIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hexp := IntervalRat.mem_expComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hexp cfg.precision hprec
  | sin _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sin, LeanCert.Internal.Dyadic.evalUnchecked, sinIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hsin := IntervalRat.mem_sinComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hsin cfg.precision hprec
  | cos _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_cos, LeanCert.Internal.Dyadic.evalUnchecked, cosIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hcos := IntervalRat.mem_cosComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hcos cfg.precision hprec
  | log _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_log, LeanCert.Internal.Dyadic.evalUnchecked, logIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom.1)
    have hpos : (LeanCert.Internal.Dyadic.evalUnchecked _ ρ_dyad cfg).toIntervalRat.lo > 0 := hdom.2
    simp only [hpos, ↓reduceIte]
    have hlog := IntervalRat.mem_logComputable hrat hpos cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hlog cfg.precision hprec
  | sinh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sinh, LeanCert.Internal.Dyadic.evalUnchecked, sinhIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hsinh := IntervalRat.mem_sinhComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hsinh cfg.precision hprec
  | cosh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_cosh, LeanCert.Internal.Dyadic.evalUnchecked, coshIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hcosh := IntervalRat.mem_coshComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hcosh cfg.precision hprec
  | tanh e' ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_tanh, LeanCert.Internal.Dyadic.evalUnchecked, tanhIntervalDyadic]
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one]
    set x := Expr.eval ρ_real e' with hx
    constructor
    · rw [Real.tanh_eq_sinh_div_cosh]
      have hcosh : Real.cosh x > 0 := Real.cosh_pos x
      rw [le_div_iff₀ hcosh, neg_one_mul]
      rw [Real.sinh_eq, Real.cosh_eq]
      have h1 : Real.exp x > 0 := Real.exp_pos x
      linarith
    · rw [Real.tanh_eq_sinh_div_cosh]
      have hcosh : Real.cosh x > 0 := Real.cosh_pos x
      rw [div_le_one₀ hcosh]
      rw [Real.sinh_eq, Real.cosh_eq]
      have h2 : Real.exp (-x) > 0 := Real.exp_pos (-x)
      linarith
  | atan e' ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_atan, LeanCert.Internal.Dyadic.evalUnchecked, atanIntervalDyadic]
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_ofNat, Rat.cast_neg, Rat.cast_ofNat]
    set x := Expr.eval ρ_real e' with hx
    constructor
    · linarith [Real.neg_pi_div_two_lt_arctan x, Real.pi_lt_four]
    · linarith [Real.arctan_lt_pi_div_two x, Real.pi_lt_four]
  | sinc _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sinc, LeanCert.Internal.Dyadic.evalUnchecked, sincIntervalDyadic]
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one]
    exact Real.sinc_mem_Icc _
  | arsinh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_arsinh, LeanCert.Internal.Dyadic.evalUnchecked, arsinhIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have harsinh := mem_arsinhInterval hrat
    exact IntervalDyadic.mem_ofIntervalRat harsinh cfg.precision hprec
  | atanh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    obtain ⟨hdom_sub, hlo_gt, hhi_lt⟩ := hdom
    simp only [Expr.eval_atanh, LeanCert.Internal.Dyadic.evalUnchecked, atanhIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom_sub)
    have hatanh := IntervalRat.mem_atanhComputable hrat hlo_gt hhi_lt cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hatanh cfg.precision hprec
  | erf _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_erf, LeanCert.Internal.Dyadic.evalUnchecked, erfIntervalDyadic]
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one]
    exact Real.erf_mem_Icc _
  | sqrt _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sqrt, LeanCert.Internal.Dyadic.evalUnchecked, sqrtIntervalDyadic]
    exact IntervalDyadic.mem_sqrt' (ih hdom) cfg.precision
  | namedConst c =>
    simp only [Expr.eval_namedConst, LeanCert.Internal.Dyadic.evalUnchecked]
    exact IntervalDyadic.mem_ofIntervalRat c.mem_interval cfg.precision hprec

/-- Successful checked Dyadic evaluation encloses the true value for every
expression, provided outward-rounding precision is nonpositive. -/
theorem evalIntervalDyadicChecked_correct (e : Expr)
    (ρ_real : Nat → ℝ) (ρ_dyad : IntervalDyadicEnv)
    (hρ : envMemDyadic ρ_real ρ_dyad) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (result : IntervalDyadic)
    (hsuccess : evalIntervalDyadicChecked e ρ_dyad cfg = .ok result) :
    Expr.eval ρ_real e ∈ result := by
  unfold evalIntervalDyadicChecked at hsuccess
  let cached := LeanCert.Internal.Dyadic.evalCached e ρ_dyad cfg
  cases hvalid : cached.2 with
  | false =>
    have : Except.error (diagnoseEvalIntervalDyadicFailure e ρ_dyad cfg) =
        Except.ok result := by
      simp [cached, hvalid] at hsuccess
    contradiction
  | true =>
    have hsuccess' : (Except.ok cached.1 : EvalResult IntervalDyadic) = Except.ok result := by
      simpa [cached, hvalid] using hsuccess
    injection hsuccess' with hresult
    subst result
    have hcheck : checkDomainValidDyadic e ρ_dyad cfg = true := by
      calc
        checkDomainValidDyadic e ρ_dyad cfg =
            (LeanCert.Internal.Dyadic.evalCached e ρ_dyad cfg).2 :=
          (evalIntervalDyadicCached_snd e ρ_dyad cfg).symm
        _ = cached.2 := rfl
        _ = true := hvalid
    have hsound := evalIntervalDyadic_correct_of_domain e
      ρ_real ρ_dyad hρ cfg hprec (checkDomainValidDyadic_correct e ρ_dyad cfg hcheck)
    change Expr.eval ρ_real e ∈ (LeanCert.Internal.Dyadic.evalCached e ρ_dyad cfg).1
    rw [evalIntervalDyadicCached_fst e ρ_dyad cfg]
    exact hsound

/-! ### Verification Checkers -/

/-- Check if expression is bounded above by q -/
def checkUpperBoundDyadic (e : Expr) (ρ : IntervalDyadicEnv) (q : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).upperBoundedBy q

/-- Check if expression is bounded below by q -/
def checkLowerBoundDyadic (e : Expr) (ρ : IntervalDyadicEnv) (q : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  (LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg).lowerBoundedBy q

/-- Check if expression is bounded in interval [lo, hi] -/
def checkBoundsDyadic (e : Expr) (ρ : IntervalDyadicEnv) (lo hi : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  let result := LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg
  result.lowerBoundedBy lo && result.upperBoundedBy hi

end LeanCert.Engine
