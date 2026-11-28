/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Binomial.Model

/-!
# Second Fundamental Theorem of Asset Pricing (single-period binomial form)

The First FTAP (existence of an equivalent martingale measure ↔ no-arbitrage)
has a corresponding **Second FTAP**: the EMM is *unique* if and only if the
market is *complete*.

In the single-period binomial model the second FTAP collapses to a clean
algebraic fact:

* **Completeness is automatic**: every contingent claim `(V_u, V_d)` is
  replicated by an explicit Δ/B portfolio (`replicating_portfolio_cost` in
  `Models.Binomial.Model`).
* **Uniqueness of the EMM**: the martingale condition `q·u + (1−q)·d = e^r`
  is a single linear equation in `q`, uniquely solvable when `u ≠ d`. Under
  no-arbitrage (`d < e^r < u`), the unique solution is the risk-neutral
  up-probability `crrUpProb u d r = (e^r − d) / (u − d)`.

So in the single-period binomial, no-arbitrage gives a unique EMM (`second_FTAP_single_period`)
and every claim is replicated (`replicating_portfolio_cost`).

## Main results

* `second_FTAP_single_period`: under `BinomialNoArb u d r`, the risk-neutral
  up-probability `q` is uniquely determined.

## References

* [J. M. Harrison and S. R. Pliska, *Martingales and stochastic integrals in the theory of
  continuous trading*][HarrisonPliska1981]

## Tags

second fundamental theorem, market completeness, unique martingale measure,
risk-neutral probability, replication, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Real

/-- **Second FTAP (single-period binomial form)**: under no-arbitrage
(`d < e^r < u`), the risk-neutral measure is uniquely characterised by the
martingale condition `q · u + (1 − q) · d = e^r`. The unique solution is
`crrUpProb u d r = (e^r − d) / (u − d)`. -/
theorem second_FTAP_single_period {u d r : ℝ} (h : BinomialNoArb u d r) :
    ∃! q : ℝ, q * u + (1 - q) * d = Real.exp r := by
  have h_ud : 0 < u - d := sub_pos.mpr h.d_lt_u
  have h_ud_ne : u - d ≠ 0 := h_ud.ne'
  refine ⟨crrUpProb u d r, ?_, ?_⟩
  · -- Existence: `crrUpProb` solves the equation.
    unfold crrUpProb
    field_simp
    ring
  · -- Uniqueness: any solution must equal `crrUpProb`.
    intro q hq
    -- `hq : q · u + (1−q) · d = e^r`  ↔  `q · (u − d) = e^r − d`  ↔  `q = (e^r − d)/(u − d)`.
    have h_solve : q * (u - d) = Real.exp r - d := by linarith
    unfold crrUpProb
    rw [eq_div_iff h_ud_ne]
    exact h_solve

end MathFin
