/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Contracts.Core

/-!
# Schedules of payments, as contracts

A schedule of payments is a contract: `payFlows t a n` pays the payoff `a i` at `t i` for each
`i < n`, and along a scenario it is worth `∑ D(tᵢ) · aᵢ` (`pathPV_payFlows`); `fixedFlows t c n`
is the case of constant payoffs, `c i` at `t i`, worth `∑ D(tᵢ) cᵢ` (`pathPV_fixedFlows`). These
are the legs of bonds, annuities, swaps and credit default swaps. Nothing here assumes a model or
a pricing measure: the value of a schedule in every model is `value_fixedFlows_deterministic`
(`Pricing/Value.lean`), and the bonds and swaps of a deterministic curve are in
`Models/Rates/DeterministicCurve.lean`.

## Main definitions

* `payFlows` — a schedule of payments; `fixedFlows` — the schedule of fixed cash flows.

## Main results

* `pathPV_payFlows`, `pathPV_fixedFlows` — what a schedule pays along a scenario.

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

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 7

## Tags

schedule of payments, fixed cash flows, coupon, annuity, payoff language, MSC 91G30, JEL G12
-/

@[expose] public section

open scoped NNReal

namespace MathFin.Contracts

variable {ι : Type*}

/-- A **schedule of payments**: for each `i < n`, pay the payoff `a i` at time `t i`. -/
noncomputable def payFlows (t : ℕ → ℝ≥0) (a : ℕ → Payoff ι) : ℕ → Contract ι
  | 0 => .zero
  | n + 1 => .both (payFlows t a n) (.pay (t n) (a n))

/-- Along every scenario, a schedule of payments is worth `∑ D(tᵢ) · aᵢ`. -/
theorem pathPV_payFlows (D : ℝ≥0 → ℝ) (s : Scenario ι) (t : ℕ → ℝ≥0) (a : ℕ → Payoff ι)
    (n : ℕ) :
    (payFlows t a n).pathPV D s = ∑ i ∈ Finset.range n, D (t i) * (a i).eval s := by
  induction n with
  | zero => simp [payFlows, Contract.pathPV, Contract.cashflows]
  | succ n ih =>
    rw [payFlows, Contract.pathPV_both, ih, Finset.sum_range_succ]
    simp [Contract.pathPV, Contract.cashflows]

/-- A **schedule of fixed cash flows**: for each `i < n`, pay `c i` at time `t i`. -/
noncomputable def fixedFlows (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) : Contract ι :=
  payFlows t (fun i ↦ .const (c i)) n

/-- Along every scenario, a schedule of fixed cash flows is worth `∑ D(tᵢ) cᵢ`. -/
theorem pathPV_fixedFlows (D : ℝ≥0 → ℝ) (s : Scenario ι) (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) :
    (fixedFlows t c n : Contract ι).pathPV D s = ∑ i ∈ Finset.range n, D (t i) * c i := by
  simp [fixedFlows, pathPV_payFlows, Payoff.eval]

end MathFin.Contracts
