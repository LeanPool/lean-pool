/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Basic.Real.Sign
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Sharpe ratio and Kelly criterion

Two classical performance and money-management identities:

* **Sharpe ratio** `S(μ, r_f, σ) = (μ - r_f) / σ` measures excess return per unit
  of risk. Under iid time aggregation, `L_T ~ N(T·μ, T·σ²)`, so the Sharpe ratio
  scales as `√T`.
* **Kelly fraction** `f*(p, b) = (p·b - q) / b` (with `q = 1 - p`) is the
  *critical point* (`g'(f*) = 0`, the first-order condition — what is proved
  here as `kellyGrowth_deriv_at_kelly`) of the expected log-growth
  `g(f) = p · log(1 + f·b) + q · log(1 - f)` under a binary bet with
  win-probability `p` and payoff ratio `b`. It is the maximizer because `g` is
  concave — concavity is not formalized here.

## Main definitions

* `sharpeRatio`: the Sharpe ratio `(μ − r_f) / σ`.
* `kellyFraction`: the Kelly fraction `f* = (p·b − (1 − p)) / b`.
* `kellyGrowth`: the expected log-growth of a binary bet at fraction `f`,
  `p · log(1 + f·b) + (1 − p) · log(1 − f)`.

## Main results

* `sharpeRatio_scale_invariant`: `S(λμ, λr_f, λσ) = S(μ, r_f, σ)` for `λ ≠ 0`.
* `sharpeRatio_translation_invariant`: shift cancels in the excess return.
* `sharpeRatio_affine_invariant`: full affine invariance, scale + shift.
* `sharpeRatio_affine_signed`: with `|c|`-volatility convention, the Sharpe
  ratio picks up `sign(c)` under `X ↦ c·X + d`.
* `sharpeRatio_scaleT`: `S_T = √T · S_1` for iid time aggregation.
* `kellyGrowth_deriv_at_kelly`: first-order optimality `g'(f*) = 0`.

## References

* [K. Bodie and Marcus, *Investments*][BodieKaneMarcus], Ch 10; Ch 5.5
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], Ch 14
* [J. L. Kelly, *A new interpretation of information rate*][Kelly1956]
* [Sharpe (1966)][Sharpe1966]
* [Thorp (2006)][Thorp2006]

## Tags

Sharpe ratio, Kelly criterion, excess return per risk, time aggregation, money management,
log-growth, MSC 91G10, JEL G11
-/

@[expose] public section

namespace MathFin

open Real

/-- **The "ratio scale invariance" algebraic master**: `(c·a − c·b) / (c·d) =
(a − b) / d` for `c ≠ 0`.

The same identity drives the scale invariance of every "difference-over-stdev"
performance ratio: `Sharpe`, `Sortino`, `Treynor`, `Information ratio` are
all instances. Naming the algebraic fact factors the work — each ratio's
`*_scale_invariant` lemma is a one-line application. -/
lemma diff_div_scale_invariant {c : ℝ} (hc : c ≠ 0) (a b d : ℝ) :
    (c * a - c * b) / (c * d) = (a - b) / d := by
  by_cases hd : d = 0
  · subst hd; simp
  · field_simp

/-- Sharpe ratio `(μ - r_f) / σ`. -/
noncomputable def sharpeRatio (μ r_f σ : ℝ) : ℝ := (μ - r_f) / σ

/-- **Scale invariance**: the Sharpe ratio is invariant under uniform scaling
of mean, risk-free rate, and volatility. One-line consequence of the
`diff_div_scale_invariant` master. -/
lemma sharpeRatio_scale_invariant {c : ℝ} (hc : c ≠ 0) (μ r_f σ : ℝ) :
    sharpeRatio (c * μ) (c * r_f) (c * σ) = sharpeRatio μ r_f σ := by
  unfold sharpeRatio
  exact diff_div_scale_invariant hc μ r_f σ

/-- **The "affine ratio invariance" algebraic master**: the ratio
`(c·a + d − (c·b + d)) / (c·e)` collapses to `(a − b) / e` for `c ≠ 0`.
The shift `d` cancels in the numerator; the scale `c` cancels between
numerator and denominator. -/
lemma diff_div_affine_invariant {c : ℝ} (hc : c ≠ 0) (a b d e : ℝ) :
    (c * a + d - (c * b + d)) / (c * e) = (a - b) / e := by
  rw [show c * a + d - (c * b + d) = c * a - c * b from by ring]
  exact diff_div_scale_invariant hc a b e

/-- **Signed affine invariance algebraic master**: when the denominator
scales as `|c|` (the natural scaling of a standard deviation under
`X ↦ c·X + d`, since `Var(cX + d) = c² · Var(X)`), the ratio picks up
`sign(c)`. -/
lemma diff_div_affine_signed {c : ℝ} (hc : c ≠ 0) (a b d e : ℝ) :
    (c * a + d - (c * b + d)) / (|c| * e) = Real.sign c * ((a - b) / e) := by
  rw [show c * a + d - (c * b + d) = c * (a - b) from by ring]
  by_cases he : e = 0
  · subst he; simp
  · rcases lt_trichotomy c 0 with hc_neg | hc_zero | hc_pos
    · rw [abs_of_neg hc_neg, Real.sign_of_neg hc_neg]
      field_simp
    · exact absurd hc_zero hc
    · rw [abs_of_pos hc_pos, Real.sign_of_pos hc_pos]
      field_simp

/-- **Translation invariance of the Sharpe ratio**: shifting the mean and
risk-free rate by the same additive constant preserves `S = (μ − r_f)/σ`,
since the shift cancels in the excess return. -/
lemma sharpeRatio_translation_invariant (μ r_f σ b : ℝ) :
    sharpeRatio (μ + b) (r_f + b) σ = sharpeRatio μ r_f σ := by
  unfold sharpeRatio; ring_nf

/-- **Full affine invariance of the Sharpe ratio (signed-σ convention)**:
under the joint substitution `μ → c·μ + d`, `r_f → c·r_f + d`, `σ → c·σ`,
the Sharpe ratio is invariant for any `c ≠ 0`. The shift cancels in the
excess, and the scale cancels in the ratio. -/
lemma sharpeRatio_affine_invariant {c : ℝ} (hc : c ≠ 0) (μ r_f σ d : ℝ) :
    sharpeRatio (c * μ + d) (c * r_f + d) (c * σ) = sharpeRatio μ r_f σ := by
  unfold sharpeRatio
  exact diff_div_affine_invariant hc μ r_f d σ

/-- **Sign-aware affine invariance** (natural `|c|`-volatility convention):
since `StDev(cX + d) = |c| · StDev(X)`, the Sharpe ratio under the joint
substitution flips sign when `c < 0`. -/
lemma sharpeRatio_affine_signed {c : ℝ} (hc : c ≠ 0) (μ r_f σ d : ℝ) :
    sharpeRatio (c * μ + d) (c * r_f + d) (|c| * σ) =
      Real.sign c * sharpeRatio μ r_f σ := by
  unfold sharpeRatio
  exact diff_div_affine_signed hc μ r_f d σ

/-- **Sharpe `√T`-scaling**: under iid time aggregation, `L_T ~ N(T·μ, T·σ²)`,
so the Sharpe ratio at horizon `T` equals `√T` times the unit-horizon Sharpe
ratio. -/
lemma sharpeRatio_scaleT {μ r_f σ T : ℝ} (hT : 0 < T) (hσ : σ ≠ 0) :
    sharpeRatio (T * μ) (T * r_f) (σ * Real.sqrt T) =
      Real.sqrt T * sharpeRatio μ r_f σ := by
  unfold sharpeRatio
  have h_sqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_sqrtT_ne : Real.sqrt T ≠ 0 := h_sqrtT_pos.ne'
  have h_T_eq : T = Real.sqrt T * Real.sqrt T := by
    rw [← Real.sqrt_mul hT.le, Real.sqrt_mul_self hT.le]
  -- Rewrite the LHS numerator using T = √T · √T
  rw [show T * μ - T * r_f =
      Real.sqrt T * Real.sqrt T * (μ - r_f) from by rw [← h_T_eq]; ring]
  field_simp

/-- Kelly fraction `f* = (p·b - q) / b`, where `q = 1 - p`. -/
noncomputable def kellyFraction (p b : ℝ) : ℝ := (p * b - (1 - p)) / b

/-- Expected log-growth of a binary bet at fraction `f`:
`p · log(1 + f·b) + (1 - p) · log(1 - f)`. -/
noncomputable def kellyGrowth (p b f : ℝ) : ℝ :=
  p * Real.log (1 + f * b) + (1 - p) * Real.log (1 - f)

/-- **Kelly first-order condition**: at the Kelly fraction `f* = (p·b − q)/b`,
the derivative of the expected log-growth vanishes. -/
lemma kellyGrowth_deriv_at_kelly {p b : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hb : 0 < b) :
    HasDerivAt (fun f ↦ kellyGrowth p b f) 0 (kellyFraction p b) := by
  unfold kellyGrowth kellyFraction
  set f₀ : ℝ := (p * b - (1 - p)) / b with hf₀_def
  have hb_ne : b ≠ 0 := hb.ne'
  -- 1 + f₀·b = p·(b + 1)
  have h_1_add : 1 + f₀ * b = p * (b + 1) := by
    rw [hf₀_def]; field_simp; ring
  -- 1 - f₀ = (1 - p)·(b + 1)/b
  have h_1_sub : 1 - f₀ = (1 - p) * (b + 1) / b := by
    rw [hf₀_def]; field_simp; ring
  have h_b1_pos : 0 < b + 1 := by linarith
  have h_q : 0 < 1 - p := by linarith
  have h_1_add_pos : 0 < 1 + f₀ * b := by rw [h_1_add]; positivity
  have h_1_add_ne : 1 + f₀ * b ≠ 0 := h_1_add_pos.ne'
  have h_1_sub_pos : 0 < 1 - f₀ := by rw [h_1_sub]; positivity
  have h_1_sub_ne : 1 - f₀ ≠ 0 := h_1_sub_pos.ne'
  -- Derivative of f ↦ log(1 + f·b) at f₀: b / (1 + f₀·b)
  have h1 : HasDerivAt (fun f ↦ Real.log (1 + f * b))
      (b / (1 + f₀ * b)) f₀ := by
    have hbase : HasDerivAt (fun f : ℝ ↦ 1 + f * b) b f₀ := by
      have := (hasDerivAt_id f₀).mul_const b
      simpa using this.const_add 1
    simpa [div_eq_mul_inv] using hbase.log h_1_add_ne
  -- Derivative of f ↦ log(1 - f) at f₀: -1 / (1 - f₀)
  have h2 : HasDerivAt (fun f ↦ Real.log (1 - f))
      (-1 / (1 - f₀)) f₀ := by
    have hbase : HasDerivAt (fun f : ℝ ↦ 1 - f) (-1) f₀ := by
      simpa using (hasDerivAt_id f₀).const_sub 1
    simpa [div_eq_mul_inv] using hbase.log h_1_sub_ne
  -- Combine
  have h := (h1.const_mul p).add (h2.const_mul (1 - p))
  have h_bp_ne : b + 1 ≠ 0 := h_b1_pos.ne'
  convert h using 1; rw [h_1_add, h_1_sub]; field_simp; ring

end MathFin
