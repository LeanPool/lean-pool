/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.Value
public import LeanPool.MathFin.Risk.Credit.TrancheLoss

/-!
# A credit tranche leg, as a contract

The loss of the tranche `[a, d]` of a credit portfolio, as a fraction of its notional, is
`((L − a)⁺ − (L − d)⁺)/(d − a)` when the portfolio has lost the fraction `L`
(`tranchePayoff` in `Risk/Credit/TrancheLoss.lean`). Reading `L` as the single underlying `()` of
a scenario, that is a `Payoff`, and paying it at `T` is a `Contract`.

## Main definitions

* `trancheLossPayoff`: the tranche loss as a payoff on the portfolio loss observed at `T`.
* `trancheLeg`: the tranche loss paid at `T`.

## Main results

* `eval_trancheLossPayoff`: the payoff evaluates to `tranchePayoff a d` of the loss observed at `T`.
* `value_trancheLeg`: on a deterministic discount curve the leg is worth the discounted expected
  `tranchePayoff`.

## Scope

The portfolio loss fraction is the underlying `X () T`, a given process; its law (for instance the
large-pool limit of `Risk/Credit/TrancheLoss.lean`) is not part of these statements.

## References

* [A. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management*][McNeilFreyEmbrechts],
  §11
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 25

## Tags

credit tranche, CDO, attachment point, detachment point, tranche loss, payoff language,
MSC 91G40, JEL G13
-/

@[expose] public section

open scoped NNReal

namespace MathFin.Contracts

/-- **The tranche loss as a payoff**: with the portfolio loss fraction `L` observed at `T`,
`((L − a)⁺ − (L − d)⁺)/(d − a)`. -/
noncomputable def trancheLossPayoff (a d : ℝ) (T : ℝ≥0) : Payoff Unit :=
  .mul (.const (d - a)⁻¹)
    (.sub (.max (.sub (.obs () T) (.const a)) (.const 0))
      (.max (.sub (.obs () T) (.const d)) (.const 0)))

/-- **The tranche leg**: the tranche loss `trancheLossPayoff a d T`, paid at `T`. -/
noncomputable def trancheLeg (a d : ℝ) (T : ℝ≥0) : Contract Unit :=
  .pay T (trancheLossPayoff a d T)

/-- The tranche loss payoff evaluates to `tranchePayoff a d` of the loss observed at `T`. -/
theorem eval_trancheLossPayoff (a d : ℝ) (T : ℝ≥0) (s : Scenario Unit) :
    (trancheLossPayoff a d T).eval s = tranchePayoff a d (s () T) := by
  simp [trancheLossPayoff, Payoff.eval, tranchePayoff, posPart_def, div_eq_inv_mul]

/-- **A tranche leg is worth the discounted expected tranche loss.** On a deterministic discount
curve `D`, with the portfolio loss fraction as the underlying `X ()`, the leg `trancheLeg a d T`
is worth `D T · 𝔼_Q[tranchePayoff a d (X () T)]`. -/
theorem value_trancheLeg {Ω : Type*} [MeasurableSpace Ω] (Q : MeasureTheory.Measure Ω)
    (D : ℝ≥0 → ℝ) (X : Unit → ℝ≥0 → Ω → ℝ) (a d : ℝ) (T : ℝ≥0) :
    (trancheLeg a d T).value Q (fun t _ ↦ D t) X
      = D T * ∫ ω, tranchePayoff a d (X () T ω) ∂Q := by
  rw [trancheLeg, Contract.value_pay, ← MeasureTheory.integral_const_mul]
  congr 1
  funext ω
  exact congrArg _ (eval_trancheLossPayoff a d T _)

end MathFin.Contracts
