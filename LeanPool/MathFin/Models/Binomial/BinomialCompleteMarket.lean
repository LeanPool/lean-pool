/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Binomial.MultiPeriodFTAP
public import LeanPool.MathFin.Models.Binomial.Binomial

/-!
# The capital of the complete market's hedge is the contract's value

`isCompleteMarket_horizonSpot` (`Models/Binomial/MultiPeriodFTAP.lean`) says that in the `N`-period
tree
every claim on the first `N` flips is `x + ∑ φ_{t+1} (S_tilde_{t+1} − S_tilde_t)`
for some capital `x` and
predictable strategy `φ`, but it names neither: `x` is whatever the second fundamental theorem
returns. For the claim of a European contract the capital is determined, and it is the contract's
value (`Contract.value`, `Pricing/Value.lean`): the equivalent martingale measure of the tree
is `horizonMeasure N (crrUpProb u d ρ)`, it prices the gains at zero
(`IsEMM.integrable_and_integral_gains`), so replication prices the claim at `x`
(`integral_eq_of_replicates`), and that price is the value, the expectation of the contract's
discounted payoff over coin-flip paths.

* `Binomial.exists_hedge_eq_value` — under no-arbitrage, for a European contract maturing on step
  `N`, the market's replication of its discounted payoff, read on the `N` flips, starts from the
  value `Contract.value (coinFlipMeasure q)`.

It is the finite-market counterpart of `Binomial.pathPV_eq_value_add_gains`
(`Models/Binomial/Binomial.lean`), which gives the hedge on the infinite path space from the
tree's backward recursion: there the value is built into the hedge by construction, here the
completeness theorem produces some hedge and the pricing argument shows its capital is the value.

## Main results

* `exists_hedge_eq_value`: under no-arbitrage, `S₀ > 0`, `q = crrUpProb u d ρ` and `T / h = N`, for
  the European contract `Contract.pay T a` with `a.eval s = g (s () T)` and each `p ∈ (0, 1)`, there
  is a bounded predictable strategy `φ` in `horizonSpot N` such that the discounted payoff equals,
  almost surely under `horizonMeasure N p`, `Contract.value` under `coinFlipMeasure q` plus the
  martingale transform of `φ`. The strategy comes from completeness and is not given in closed form;
  only its capital is identified, as the contract's value.

## References

* [J. M. Harrison and S. R. Pliska, *Martingales and stochastic integrals in the theory of
  continuous trading*][HarrisonPliska1981]
* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  Section 5.4

## Tags

complete market, second fundamental theorem, replication, hedging portfolio,
martingale representation, MSC 91G20, MSC 60G42, JEL G13
-/

@[expose] public section

namespace MathFin.Contracts.Binomial

open MeasureTheory
open scoped NNReal

variable {S₀ u d ρ h : ℝ} {q : ℝ≥0}

/-- **In the complete tree the hedge's capital is the contract's value.** Under no-arbitrage and
`S₀ > 0`, take a European contract that pays `g` of the underlying at a time `T` falling on step
`N` (`T / h = N`). Its discounted payoff, as a claim on the first `N` flips (the path padded by
`false`, `padFlips`), is replicated, almost surely under any real-world law of i.i.d.
`Bernoulli(p)` flips with `0 < p < 1`, by a bounded predictable strategy `φ` in the discounted
spot `horizonSpot N`, from the initial capital `Contract.value` under the risk-neutral flips
`coinFlipMeasure q`, `q = crrUpProb u d ρ`. The strategy is not given in closed form: it comes
from the completeness of the market (`isCompleteMarket_horizonSpot`), and only its capital is
identified. -/
theorem exists_hedge_eq_value (hS₀ : 0 < S₀) (hna : BinomialNoArb u d ρ) {p : ℝ≥0} (hp0 : 0 < p)
    (hp1 : p < 1) (hq : q ≤ 1) (hqcrr : crrUpProb u d ρ = q) {T : ℝ≥0} {N : ℕ}
    (hTN : (T : ℝ) / h = N) {a : Payoff Unit} {g : ℝ → ℝ}
    (hg : ∀ s : Scenario Unit, a.eval s = g (s () T)) :
    ∃ φ : ℕ → (Fin N → Bool) → ℝ,
      (∀ t < N, StronglyMeasurable[horizonFiltration N t] (φ (t + 1))) ∧
      (∃ K : ℝ, ∀ n ≤ N, ∀ x, ‖φ n x‖ ≤ K) ∧
      (fun x ↦ (Contract.pay T a).pathPV (discount ρ h)
          (scenarioAt (assets S₀ u d h) (padFlips N x)))
        =ᵐ[horizonMeasure N p hp1.le] fun x ↦
          (Contract.pay T a).value (coinFlipMeasure q hq) (fun t _ ↦ discount ρ h t)
              (assets S₀ u d h)
            + martingaleTransform φ (horizonSpot N S₀ u d ρ) N x := by
  set H : (Fin N → Bool) → ℝ := fun x ↦ (Contract.pay T a).pathPV (discount ρ h)
    (scenarioAt (assets S₀ u d h) (padFlips N x)) with hH
  -- the claim is the contract's discounted payoff, a function of the first `N` flips
  have hflips (ω : ℕ → Bool) : H (flips N ω) = (Contract.pay T a).pathPV (discount ρ h)
      (scenarioAt (assets S₀ u d h) ω) := by
    simp only [hH, Contract.pathPV, Contract.cashflows, hg, scenarioAt, assets, hTN,
      Nat.floor_natCast, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [pathAdaptedAt_spotPath S₀ u d N (padFlips N (flips N ω)) ω fun i hi ↦ by
      simp [padFlips, flips, hi]]
  obtain ⟨x, φ, hpred, hbdd, hrep⟩ := isCompleteMarket_horizonSpot hS₀ hna hp0 hp1 H
    (by rw [horizonFiltration_horizon]; exact (measurable_of_countable H).stronglyMeasurable)
    (let ⟨C, hC⟩ := (Set.finite_range fun x ↦ |H x|).bddAbove; ⟨C, fun ω ↦ hC ⟨ω, rfl⟩⟩)
  refine ⟨φ, hpred, hbdd, ?_⟩
  -- the risk-neutral law prices the gains at zero, so the capital is `∫ H` there, the value
  have hQ := isEMM_horizonSpot (T := N) hna S₀ hp0 hp1 hq hqcrr
  have hQ' := (hQ.integrable_and_integral_gains (martingaleTransform_mem_tradedGains hpred hbdd))
  have hx : (Contract.pay T a).value (coinFlipMeasure q hq) (fun t _ ↦ discount ρ h t)
      (assets S₀ u d h) = x := by
    have := hQ.isProb
    rw [← integral_eq_of_replicates hQ.ac hQ'.1 hQ'.2 hrep, horizonMeasure,
      integral_map (measurable_flips N).aemeasurable Integrable.of_finite.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ (hflips ω).symm)
  exact hx ▸ hrep

end MathFin.Contracts.Binomial
