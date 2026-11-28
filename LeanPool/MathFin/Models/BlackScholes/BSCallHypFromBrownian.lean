/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.Call
public import LeanPool.MathFin.Models.Bachelier.Bachelier
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# `BSCallHyp` / `BachelierHyp` from a Brownian motion

The existing `BSCallHyp` and `BachelierHyp` hypotheses are stated at the
**marginal level**: `Z ~ N(0, 1)` under `Q` with `S_T = bsTerminal …(Z ω)`
(BS) or `S_T = S_0 + σ √T · Z(ω)` (Bachelier). This file shows that both
hypotheses are *consequences* of having a pre-Brownian motion `W : ℝ≥0 → Ω →
ℝ` (Mathlib's `IsPreBrownianReal W Q`), by setting

  `Z := W T.toNNReal / √T`,

which has `gaussianReal 0 1` law by Gaussian-scaling. This binds the BS /
Bachelier models to actual continuous-time process structure without
requiring any change to the existing closed-form pricing theorems, which
continue to consume the marginal hypothesis directly.

## Bridge content

The substantive new fact is `scaled_isPreBrownian_eval_law`:

  `IsPreBrownianReal W Q  ⟹  HasLaw (fun ω ↦ W T.toNNReal ω / √T) (gaussianReal 0 1) Q`.

It combines `IsPreBrownianReal.hasLaw_eval` (Brownian marginal `W_T ~ N(0, T)`)
with `Mathlib`'s `gaussianReal_div_const` (Gaussian scaling under `· / c`).
The variance arithmetic `T.toNNReal / NNReal.mk((√T)², _) = 1` collapses via
`Real.sq_sqrt` and `NNReal.div_self`.

The two `of_isPreBrownian` constructors are then one-line wrappers.

## Why this is a "bridge"

The `Foundations/` BM machinery (`BrownianMotion.Gaussian.BrownianMotion`,
`MathFin.Probability.Brownian.BrownianMartingale`, etc.) was previously
**structurally disconnected** from the pricing modules: pricing took
`Z ~ N(0,1)` as axiom and never invoked the BM construction. This file
makes the connection explicit — any BM construction (via `IsPreBrownianReal`)
discharges the BS / Bachelier hypothesis automatically.

## Main results

* `scaled_isPreBrownian_eval_law`: the core scaling identity for pre-
  Brownian motion under `· / √T`.
* `BSCallHyp.of_isPreBrownian`: BS hypothesis from a pre-Brownian motion.
* `BachelierHyp.of_isPreBrownian`: Bachelier hypothesis from a pre-Brownian
  motion (same scaled `Z`).

## Tags

Brownian motion, Gaussian scaling, Black–Scholes hypothesis, Bachelier model, pre-Brownian motion,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Core scaling identity**: if `W` is a pre-Brownian motion under `Q`,
then for any positive `T : ℝ`, the rescaled time-`T` value
`W T.toNNReal / √T` has `gaussianReal 0 1` law.

Combines `IsPreBrownianReal.hasLaw_eval` (BM marginal `W_T ~ N(0, T.toNNReal)`)
with `gaussianReal_div_const` (Gaussian scaling under `· / c`). The
variance computation `T.toNNReal / NNReal.mk((√T)², _) = 1` reduces to
`Real.sq_sqrt` + `NNReal.div_self`. -/
lemma scaled_isPreBrownian_eval_law
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω}
    (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W Q)
    {T : ℝ} (hT : 0 < T) :
    HasLaw (fun ω ↦ W T.toNNReal ω / Real.sqrt T) (gaussianReal 0 1) Q := by
  have h_eval : HasLaw (W T.toNNReal) (gaussianReal 0 T.toNNReal) Q :=
    hW.hasLaw_eval T.toNNReal
  have h_div := gaussianReal_div_const h_eval (Real.sqrt T)
  convert h_div using 2
  · rw [zero_div]
  · -- Variance: T.toNNReal / NNReal.mk((√T)², _) = 1
    have h_sqrt_sq :
        (NNReal.mk ((Real.sqrt T) ^ 2) (sq_nonneg _) : ℝ≥0) = T.toNNReal := by
      apply NNReal.eq
      simp only [NNReal.coe_mk]
      rw [Real.sq_sqrt hT.le]
      exact (Real.coe_toNNReal T hT.le).symm
    rw [h_sqrt_sq]
    exact (div_self (Real.toNNReal_pos.mpr hT).ne').symm

/-- **`BSCallHyp` from a pre-Brownian motion**. Given a pre-Brownian
process `W` under `Q` and positive parameters `(S_0, K, σ, T)`, the
rescaled `Z := W T.toNNReal / √T` satisfies the BS risk-neutral lognormal
hypothesis. -/
theorem BSCallHyp.of_isPreBrownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W Q)
    {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    BSCallHyp Q S_0 K r σ T (fun ω ↦ W T.toNNReal ω / Real.sqrt T) :=
  ⟨hS_0, hK, hσ, hT, scaled_isPreBrownian_eval_law W hW hT⟩

/-- **`BachelierHyp` from a pre-Brownian motion**. Same scaled `Z := W
T.toNNReal / √T` works for the Bachelier arithmetic-BM model (no
exponential), since both hypotheses share `Z_law : HasLaw Z (gaussianReal
0 1) Q`. -/
theorem BachelierHyp.of_isPreBrownian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W Q)
    {S_0 K σ T : ℝ}
    (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    BachelierHyp Q S_0 K σ T (fun ω ↦ W T.toNNReal ω / Real.sqrt T) :=
  ⟨hK, hσ, hT, scaled_isPreBrownian_eval_law W hW hT⟩

/-- **`bsTerminal` expressed in terms of Brownian motion**: substituting the
scaled `Z := W T.toNNReal / √T` into `bsTerminal` yields the *intrinsic*
GBM form

  `S_T(ω) = S_0 · exp((r − σ²/2) T + σ · W T.toNNReal(ω))`,

with the `√T` factor cancelling. This is the form most textbooks state
directly — the BS-formula derivation uses the standard-normal Z marginal
because that's algebraically convenient, but the *meaning* is the BM
exponential. -/
lemma bsTerminal_via_brownian
    {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) {S_0 r σ T : ℝ} (hT : 0 < T) (ω : Ω) :
    bsTerminal S_0 r σ T (W T.toNNReal ω / Real.sqrt T) =
      S_0 * Real.exp ((r - σ^2 / 2) * T + σ * W T.toNNReal ω) := by
  unfold bsTerminal
  have h_sqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_sqrt_ne : Real.sqrt T ≠ 0 := h_sqrt_pos.ne'
  congr 1
  field_simp

/-- **Bachelier terminal expressed in terms of Brownian motion**: the
arithmetic-BM model has

  `S_T(ω) = S_0 + σ · W T.toNNReal(ω)`

when `Z := W T.toNNReal / √T` is plugged into `S_0 + σ √T · Z`. -/
lemma bachelierTerminal_via_brownian
    {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) {S_0 σ T : ℝ} (hT : 0 < T) (ω : Ω) :
    S_0 + σ * Real.sqrt T * (W T.toNNReal ω / Real.sqrt T) =
      S_0 + σ * W T.toNNReal ω := by
  have h_sqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_sqrt_ne : Real.sqrt T ≠ 0 := h_sqrt_pos.ne'
  field_simp

end MathFin
