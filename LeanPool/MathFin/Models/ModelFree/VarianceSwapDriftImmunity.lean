/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Ito.ItoProcessQV

/-!
# Variance-swap fair strike is drift-immune: L² realized variance of GBM

A variance swap pays the realized variance of log-returns against a fixed
strike. Quoting the fair strike as `σ²` presupposes that the realized
variance of the price path identifies `σ²` — *and does so regardless of the
drift*, since the physical drift is unknown and the risk-neutral drift is a
modelling choice. This file proves exactly that, in the strong (mean-square)
sense:

for a geometric Brownian motion price
`S_t = S₀ · exp((μd − σ²/2)·t + σ·B_t)` with **arbitrary** drift parameter
`μd`, the realized variance of log-returns along the uniform `n`-partition
of `[0, T]` converges in `L²` to `σ²·T`:

  `E[(∑_k (log S_{t_{k+1}} − log S_{t_k})² − σ²T)²] → 0`.

The drift does not appear in the limit: realized variance is a
quadratic-variation functional, and `Probability/Brownian/Ito/ItoProcessQV.lean` shows the
(Lipschitz) drift contributes `O(1/n)` to it. Financially: the
variance-swap fair strike can be quoted as `σ²` without taking a stance on
the drift — the estimator the swap settles on concentrates at `σ²T` under
the physical measure and the risk-neutral measure alike.

## Relation to the existing variance-swap chain

* `Models/ModelFree/VarianceSwapLimit.lean` (phase 34) proves the
  *expectation-level* limit `E[Σ (Δ log S)²] → σ²T` for the risk-neutral BS
  log-price (drift pinned to `r − σ²/2`). This file strengthens it twice:
  convergence of the estimator itself in `L²` (concentration, not just
  unbiasedness in the limit), and for every drift.
* `Models/ModelFree/VarianceSwap.lean` proves the Demeterfi–Derman–Kamal
  log-payoff replication `(2/T)·E[log(F/S_T)] = σ²` — the static-hedge leg.
  Together: the floating leg the swap *measures* (here) and the option
  portfolio that *replicates* its strike (there) identify the same `σ²`.

## Main results

* `tendsto_realizedVariance_gbm_L2` — realized variance of GBM log-returns
  `→ σ²·T` in `L²` along the uniform partition, for every drift `μd`: the limit does not
  depend on it.

## References

* [Demeterfi et al., *More than you ever wanted to know about volatility
  swaps*][DemeterfiDermanKamalZou1999]

## Tags

variance swap, realized variance, fair strike, geometric Brownian motion, drift independence,
mean-square convergence, MSC 91G20, MSC 60J65, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory MathFin.QuadraticVariationL2 Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- **Variance-swap drift immunity.** For a GBM price
`S_t = S₀ · exp((μd − σ²/2)t + σ B_t)` with arbitrary drift `μd`, the
realized variance of log-returns along the uniform partition of `[0, T]`
converges in mean-square to `σ²·T`. The drift is absent from the limit:
the fair variance strike is a quadratic-variation functional, immune to
the (physical vs. risk-neutral) drift. -/
theorem tendsto_realizedVariance_gbm_L2 (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    {S : ℝ≥0 → Ω → ℝ} {S₀ μd σ : ℝ} (hS₀ : 0 < S₀)
    (hS : ∀ t ω, S t ω = S₀ * Real.exp ((μd - σ ^ 2 / 2) * (t : ℝ) + σ * B t ω)) :
    Tendsto (fun n : ℕ ↦ ∫ ω, (∑ k ∈ Finset.range n,
        (Real.log (S (unifPart T n (k + 1)) ω) - Real.log (S (unifPart T n k) ω)) ^ 2
          - σ ^ 2 * (T : ℝ)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  -- The log-price is an Itô process with constant-slope drift and diffusion σ·B.
  have hlog : ∀ (t : ℝ≥0) (ω : Ω), Real.log (S t ω)
      = (fun _ : Ω ↦ Real.log S₀) ω
        + (fun (t : ℝ≥0) (_ : Ω) ↦ (μd - σ ^ 2 / 2) * (t : ℝ)) t ω
        + σ * B t ω := by
    intro t ω
    rw [hS t ω, Real.log_mul hS₀.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  exact ItoProcessQV.tendsto_qv_ito_process hB hBmeas T
    (X := fun t ω ↦ Real.log (S t ω))
    (Ca := |μd - σ ^ 2 / 2|) (abs_nonneg _) hlog
    (fun t ↦ measurable_const)
    (fun s t hst ω ↦ by
      have hts : (s : ℝ) ≤ (t : ℝ) := NNReal.coe_le_coe.mpr hst
      rw [← mul_sub, abs_mul, abs_of_nonneg (sub_nonneg.mpr hts)])

end MathFin
