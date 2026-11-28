/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Binomial.Binomial
public import LeanPool.MathFin.Risk.ExpectedShortfall

/-!
# The risk of a contract position

A position in a contract `c`, bought at price `p`, loses `p − pathPV` along each outcome: the price
paid less the discounted payoff (`Contract.loss`). Its value-at-risk and expected shortfall are
those of `Risk/ValueAtRisk.lean`, taken under a law `P` of the outcomes. `P` is the
measure the risk is measured under, and need not be the pricing measure: the price `p` is an
input, typically a `Contract.value` under some `Q`.

* A book's expected shortfall is at most the sum of its contracts'
  (`expectedShortfall_loss_both_le`), which is the subadditivity of expected shortfall
  (`expectedShortfall_add_le`) read through `Contract.pathPV_both`. Value-at-risk has no such bound.
* A position whose payoff is never negative cannot lose more than its price
  (`valueAtRisk_loss_le_of_nonneg`), so a long call's value-at-risk is at most its premium
  (`valueAtRisk_loss_europeanCall_le`).
* In the binomial tree, a seller who receives a European contract's value and follows its hedge
  (`Binomial.pathPV_eq_value_add_gains`) carries zero value-at-risk and zero expected shortfall,
  under every law of the coin flips (`Binomial.valueAtRisk_hedged_eq_zero`).

## Main definitions

* `Contract.loss` — the loss of a position in a contract bought at a given price.

## Main results

* `expectedShortfall_loss_both_le`, `valueAtRisk_loss_le_of_nonneg`,
  `valueAtRisk_loss_europeanCall_le`, `Binomial.valueAtRisk_hedged_eq_zero`.

## Source

The layered separation of contract semantics from pricing semantics, and the
framing "the contract is not the model", are due to Paul Bilokon,
*The Contract Is Not the Model: Proof-Carrying Exotic Derivatives and the
Economics of Model Risk* (working paper, 9 August 2026; Mathematical
Finance, Imperial College London), with code at
<https://github.com/thalesians/lean_contracts> (Apache-2.0). That paper in
turn builds on the compositional contract-DSL of
Peyton Jones, Eber and Seward (2000) and the certified-contract work of Bahr,
Berthold and Elsman (2015) and Annenkov (2018).

No code is copied from `lean_contracts`; every definition and proof here is
written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
§6 for the full credit line.

## References

* [P. Artzner et al., *Coherent measures of risk*][ArtznerDelbaenEberHeath1999]
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [J. C. Cox, S. A. Ross and M. Rubinstein, *Option pricing: a simplified
  approach*][CoxRossRubinstein1979]
* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Section 2.2; Section 2.3
* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  Theorem 1.2.2

## Tags

value at risk, expected shortfall, subadditivity, position loss, hedged position,
risk of a derivative book, MSC 91G70, JEL G32
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace MathFin

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {α : ℝ}

namespace Contracts

variable {ι : Type*} {D : ℝ≥0 → ℝ} {X : ι → ℝ≥0 → Ω → ℝ}

/-- The **loss of a position** in the contract `c` bought at price `p`: along each outcome, the
price paid less the discounted payoff. -/
noncomputable def Contract.loss (p : ℝ) (D : ℝ≥0 → ℝ) (X : ι → ℝ≥0 → Ω → ℝ) (c : Contract ι) :
    Ω → ℝ :=
  fun ω ↦ p - c.pathPV D (scenarioAt X ω)

variable [IsProbabilityMeasure P]

/-- **A book's expected shortfall is at most the sum of its contracts'.** Holding `a` bought at
`p_a` and `b` bought at `p_b` loses what the two positions lose together (`Contract.pathPV_both`),
and expected shortfall is subadditive (`expectedShortfall_add_le`). -/
theorem expectedShortfall_loss_both_le (hα : α ∈ Ioo 0 1) {a b : Contract ι}
    (ha : Integrable (fun ω ↦ a.pathPV D (scenarioAt X ω)) P)
    (hb : Integrable (fun ω ↦ b.pathPV D (scenarioAt X ω)) P) (pa pb : ℝ) :
    expectedShortfall ((Contract.both a b).loss (pa + pb) D X) P α
      ≤ expectedShortfall (a.loss pa D X) P α + expectedShortfall (b.loss pb D X) P α := by
  have h : (Contract.both a b).loss (pa + pb) D X = fun ω ↦ a.loss pa D X ω + b.loss pb D X ω :=
    funext fun ω ↦ by simp only [Contract.loss, Contract.pathPV_both]; ring
  rw [h]
  exact expectedShortfall_add_le ((integrable_const pa).sub ha) ((integrable_const pb).sub hb) hα

/-- **A position that never pays a negative amount cannot lose more than its price.** If the
discounted payoff of `c` is nonnegative on every outcome, the value-at-risk of the position bought
at `p` is at most `p`. -/
theorem valueAtRisk_loss_le_of_nonneg (hα : α ∈ Ioo 0 1) {c : Contract ι}
    (hm : AEMeasurable (fun ω ↦ c.pathPV D (scenarioAt X ω)) P)
    (hc : ∀ ω, 0 ≤ c.pathPV D (scenarioAt X ω)) (p : ℝ) :
    valueAtRisk (c.loss p D X) P α ≤ p := by
  calc valueAtRisk (c.loss p D X) P α ≤ valueAtRisk (fun _ ↦ p) P α :=
        valueAtRisk_mono (aemeasurable_const.sub hm) aemeasurable_const
          (Filter.Eventually.of_forall fun ω ↦ sub_le_self p (hc ω)) hα
    _ = p := valueAtRisk_const p hα

/-- **A long call's value-at-risk is at most its premium**, for a nonnegative discount factor. -/
theorem valueAtRisk_loss_europeanCall_le (hα : α ∈ Ioo 0 1) {X : Unit → ℝ≥0 → Ω → ℝ} {K : ℝ}
    {T : ℝ≥0} (hD : 0 ≤ D T)
    (hm : AEMeasurable (fun ω ↦ (europeanCall K T).pathPV D (scenarioAt X ω)) P) (p : ℝ) :
    valueAtRisk ((europeanCall K T).loss p D X) P α ≤ p :=
  valueAtRisk_loss_le_of_nonneg hα hm (fun ω ↦ by
    simpa [europeanCall, europeanCallPayoff, Contract.pathPV, Contract.cashflows, Payoff.eval]
      using mul_nonneg hD (le_max_right _ _)) p

namespace Binomial

variable {u d ρ h : ℝ} {q : ℝ≥0} (hq : q ≤ 1)

/-- **A hedged seller carries no risk.** In the binomial tree under no-arbitrage, a seller of a
European contract who receives its value and follows the hedge of `pathPV_eq_value_add_gains`
loses `pathPV − (value + gains) = 0` on every path. So under every law `P` of the coin flips,
physical or not, the hedged position has zero value-at-risk and zero expected shortfall at every
level. -/
theorem valueAtRisk_hedged_eq_zero (hqcrr : crrUpProb u d ρ = q) (S₀ : ℝ) {T : ℝ≥0} {N : ℕ}
    (hTN : (T : ℝ) / h = N) (hna : BinomialNoArb u d ρ) (hS₀ : S₀ ≠ 0) {a : Payoff Unit}
    {g : ℝ → ℝ} (hg : ∀ s : Scenario Unit, a.eval s = g (s () T)) :
    ∃ H : ℕ → (ℕ → Bool) → ℝ, StronglyAdapted flipFiltration (fun n ↦ H (n + 1)) ∧
      ∀ (P : Measure (ℕ → Bool)) [IsProbabilityMeasure P], ∀ α ∈ Ioo (0 : ℝ) 1,
        let L := fun ω ↦ (Contract.pay T a).pathPV (discount ρ h) (scenarioAt (assets S₀ u d h) ω)
          - ((Contract.pay T a).value (coinFlipMeasure q hq) (fun t _ ↦ discount ρ h t)
              (assets S₀ u d h)
            + martingaleTransform H (discountedSpot S₀ u d ρ) N ω)
        valueAtRisk L P α = 0 ∧ expectedShortfall L P α = 0 := by
  obtain ⟨H, hH, hrep⟩ := pathPV_eq_value_add_gains hq hqcrr S₀ hTN hna hS₀ hg
  refine ⟨H, hH, fun P _ α hα ↦ ?_⟩
  have hL : (fun ω ↦ (Contract.pay T a).pathPV (discount ρ h) (scenarioAt (assets S₀ u d h) ω)
      - ((Contract.pay T a).value (coinFlipMeasure q hq) (fun t _ ↦ discount ρ h t)
          (assets S₀ u d h)
        + martingaleTransform H (discountedSpot S₀ u d ρ) N ω))
      = fun _ ↦ 0 := funext fun ω ↦ sub_eq_zero.2 (hrep ω)
  simp only [hL]
  exact ⟨valueAtRisk_const 0 hα, expectedShortfall_const 0 hα⟩

end Binomial

end Contracts

end MathFin
