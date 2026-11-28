/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.VarianceSwapEquipartition

/-!
# Variance-swap QV limit theorem (phase 34)

Closes the QV chain: Phase 32 gave the per-increment identity, Phase 33
gave the finite-`n` equipartition-sum identity, and this file takes the
limit `n → ∞`:

  `lim_n E[Σ_{k=0}^{n} (X_{(k+1)T/(n+1)} − X_{kT/(n+1)})²] = σ²·T`,

the QV / realised-variance characterisation of the variance-swap fair
strike. The drift contribution `(r − σ²/2)² · T² / (n + 1)` vanishes as
`n → ∞` by standard `Tendsto` analysis
(`tendsto_one_div_add_atTop_nhds_zero_nat`).

## Main results

* `tendsto_expected_bsLogPrice_equipartition_sum`: the realised-variance
  expectation converges to `σ²·T` as the partition refines.

## Companion: the log-payoff form

The pre-existing `Models/ModelFree/VarianceSwap.lean` proves the Demeterfi-
Derman-Kamal log-payoff identity `(2/T) · E[log(F/S_T)] = σ²`. The two
characterisations of `σ²` (realised-variance / QV here, log-payoff
replication there) are different functionals of the same BS price process.

## Tags

variance swap, realized variance limit, quadratic variation, fair strike, partition refinement,
MSC 91G20, MSC 60J65, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ → Ω → ℝ}

/-- **QV limit theorem** (phase 34): under `BrownianQuadraticVariation`
hypothesis on `B` and a probability measure `μ`, the expected sum of
squared BS-log-price increments along the equipartition of `[0, T]`
converges to `σ² · T` as the partition refines:

  `lim_n E[Σ_{k=0}^{n} (X_{(k+1)T/(n+1)} − X_{kT/(n+1)})²] = σ² · T`.

Proof structure:
1. Build `Tendsto (fun _ ↦ σ²·T) atTop (𝓝 (σ²·T))` (constant).
2. Build `Tendsto (fun n ↦ drift² · T² / (n+1)) atTop (𝓝 0)` via
   `tendsto_one_div_add_atTop_nhds_zero_nat` + scaling.
3. Add the two via `Tendsto.add` ⟹ `Tendsto (σ²·T + drift²·T²/(n+1))
   atTop (𝓝 (σ²·T + 0)) = (𝓝 (σ²·T))`.
4. Apply `.congr` with Phase 33's per-`n` closed form to convert to the
   target functional. -/
theorem tendsto_expected_bsLogPrice_equipartition_sum
    [IsProbabilityMeasure μ]
    (hB : BrownianQuadraticVariation μ B) (S_0 r σ : ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ ω, ∑ k ∈ Finset.range (n + 1),
        (bsLogPrice S_0 r σ B (((k : ℝ) + 1) * T / ((n : ℝ) + 1)) ω -
         bsLogPrice S_0 r σ B ((k : ℝ) * T / ((n : ℝ) + 1)) ω) ^ 2 ∂μ)
      Filter.atTop (nhds (σ ^ 2 * T)) := by
  -- Step 1: drift contribution → 0 via 1/(n+1) → 0 + scaling.
  have h_one_div : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1))
      Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h_decay_mul : Filter.Tendsto
      (fun n : ℕ ↦ (r - σ ^ 2 / 2) ^ 2 * T ^ 2 * ((1 : ℝ) / ((n : ℝ) + 1)))
      Filter.atTop (nhds ((r - σ ^ 2 / 2) ^ 2 * T ^ 2 * 0)) :=
    h_one_div.const_mul _
  rw [mul_zero] at h_decay_mul
  have h_decay : Filter.Tendsto
      (fun n : ℕ ↦ (r - σ ^ 2 / 2) ^ 2 * T ^ 2 / ((n : ℝ) + 1))
      Filter.atTop (nhds (0 : ℝ)) := by
    refine h_decay_mul.congr ?_
    intro n
    rw [mul_one_div]
  -- Step 2: constant Tendsto for σ²·T.
  have h_const : Filter.Tendsto (fun _ : ℕ ↦ σ ^ 2 * T)
      Filter.atTop (nhds (σ ^ 2 * T)) :=
    tendsto_const_nhds
  -- Step 3: sum of two Tendsto, then simplify nhds(σ²·T + 0) = nhds(σ²·T).
  have h_sum :
      Filter.Tendsto
        (fun n : ℕ ↦ σ ^ 2 * T +
          (r - σ ^ 2 / 2) ^ 2 * T ^ 2 / ((n : ℝ) + 1))
        Filter.atTop (nhds (σ ^ 2 * T)) := by
    have := h_const.add h_decay
    rwa [add_zero] at this
  -- Step 4: rewrite target via Phase 33's closed form per `n`.
  have h_eq : ∀ n : ℕ,
      ∫ ω, ∑ k ∈ Finset.range (n + 1),
        (bsLogPrice S_0 r σ B (((k : ℝ) + 1) * T / ((n : ℝ) + 1)) ω -
         bsLogPrice S_0 r σ B ((k : ℝ) * T / ((n : ℝ) + 1)) ω) ^ 2 ∂μ
        = σ ^ 2 * T + (r - σ ^ 2 / 2) ^ 2 * T ^ 2 / ((n : ℝ) + 1) :=
    fun n ↦ expected_bsLogPrice_equipartition_sum hB S_0 r σ hT n
  exact h_sum.congr (fun n ↦ (h_eq n).symm)

end MathFin
