/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Binomial.Model
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Uniqueness of the binomial replicating portfolio, and the law of one price

`Models.Binomial.Model` exhibits a single-period replicating portfolio

  `Δ = (V_u − V_d) / (S₀ · (u − d))`,   `B = e^{−r} · (u · V_d − d · V_u) / (u − d)`,

which pays `V_u` in the up-state and `V_d` in the down-state (`replicating_payoff_up`,
`replicating_payoff_down`) and costs the risk-neutral price
`binomialOptionPriceOnePeriod u d r V_u V_d` (`replicating_portfolio_cost`). This file proves
that it is the only one: under no-arbitrage (`d < e^r < u`, so `u ≠ d`) and `S₀ > 0`, the
linear system

  `Δ · (S₀ · u) + B · e^r = V_u`,   `Δ · (S₀ · d) + B · e^r = V_d`

has exactly one solution, its determinant being `S₀ · (u − d) · e^r ≠ 0`. Consequently every
portfolio that replicates the claim costs the risk-neutral price: the law of one price in the
one-period binomial market.

Scope: one period, two states. The multi-period tree and the equivalence between uniqueness
of the martingale measure and completeness are not stated here (`Models.Binomial.SecondFTAP` proves
the one-period uniqueness of `q`; `Models.Binomial.BinomialFromFTAP` identifies the price with the
FTAP pricing kernel).

## Main results

* `binomial_replicatingPortfolio_unique`: the replicating portfolio `(Δ, B)` is uniquely
  determined by the target payoffs `(V_u, V_d)`.
* `binomial_replication_cost_eq_price`: any portfolio replicating `(V_u, V_d)` costs
  `binomialOptionPriceOnePeriod u d r V_u V_d`.

## Tags

replicating portfolio, law of one price, delta and bond, no arbitrage, one-period binomial,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

/-- **Uniqueness of the single-period binomial replicating portfolio**.

Under no-arbitrage (`d < e^r < u`, hence `u > d`) with positive spot `S₀ > 0`, the linear system

  `Δ · (S₀ · u) + B · e^r = V_u`,
  `Δ · (S₀ · d) + B · e^r = V_d`

has a unique solution `(Δ, B)`: the portfolio of `Models.Binomial.Model`,
`Δ = (V_u − V_d) / (S₀ · (u − d))`, `B = e^{−r} · (u · V_d − d · V_u) / (u − d)`.
Subtracting the equations gives `Δ · S₀ · (u − d) = V_u − V_d`, and `u · (down) − d · (up)`
gives `B · e^r · (u − d) = u · V_d − d · V_u`. -/
theorem binomial_replicatingPortfolio_unique
    {S₀ u d r V_u V_d : ℝ} (hS₀ : 0 < S₀) (h : BinomialNoArb u d r) :
    ∃! p : ℝ × ℝ,
      p.1 * (S₀ * u) + p.2 * Real.exp r = V_u ∧
      p.1 * (S₀ * d) + p.2 * Real.exp r = V_d := by
  refine ⟨((V_u - V_d) / (S₀ * (u - d)), Real.exp (-r) * (u * V_d - d * V_u) / (u - d)),
    ⟨replicating_payoff_up hS₀ h, replicating_payoff_down hS₀ h⟩, ?_⟩
  rintro ⟨Δ, B⟩ hp
  obtain ⟨h_up, h_down⟩ : Δ * (S₀ * u) + B * Real.exp r = V_u ∧
      Δ * (S₀ * d) + B * Real.exp r = V_d := hp
  have hud : u - d ≠ 0 := (sub_pos.mpr h.d_lt_u).ne'
  have hexp : Real.exp (-r) * Real.exp r = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  refine Prod.ext ?_ ?_
  · change Δ = (V_u - V_d) / (S₀ * (u - d))
    rw [eq_div_iff (mul_ne_zero hS₀.ne' hud)]
    linear_combination h_up - h_down
  · change B = Real.exp (-r) * (u * V_d - d * V_u) / (u - d)
    rw [eq_div_iff hud]
    linear_combination Real.exp (-r) * (u * h_down - d * h_up) - B * (u - d) * hexp

/-- **Law of one price in the one-period binomial market.** Under no-arbitrage and `S₀ > 0`,
every portfolio `(Δ, B)` that pays `V_u` in the up-state and `V_d` in the down-state costs
`Δ · S₀ + B = e^{−r} · (q · V_u + (1 − q) · V_d)`, the risk-neutral price. By uniqueness
(`binomial_replicatingPortfolio_unique`) it is the portfolio of `Models.Binomial.Model`, whose cost
is `replicating_portfolio_cost`. -/
theorem binomial_replication_cost_eq_price {S₀ u d r V_u V_d Δ B : ℝ} (hS₀ : 0 < S₀)
    (h : BinomialNoArb u d r) (h_up : Δ * (S₀ * u) + B * Real.exp r = V_u)
    (h_down : Δ * (S₀ * d) + B * Real.exp r = V_d) :
    Δ * S₀ + B = binomialOptionPriceOnePeriod u d r V_u V_d := by
  obtain ⟨p, -, hp⟩ := binomial_replicatingPortfolio_unique (V_u := V_u) (V_d := V_d) hS₀ h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj <| (hp (Δ, B) ⟨h_up, h_down⟩).trans
    (hp ((V_u - V_d) / (S₀ * (u - d)), Real.exp (-r) * (u * V_d - d * V_u) / (u - d))
      ⟨replicating_payoff_up hS₀ h, replicating_payoff_down hS₀ h⟩).symm
  exact replicating_portfolio_cost hS₀ h

end MathFin
