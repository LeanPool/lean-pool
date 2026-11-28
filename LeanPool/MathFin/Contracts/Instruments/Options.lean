/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Contracts.Core
public import LeanPool.MathFin.Contracts.Instruments.CallPayoff

/-!
# Options, as contracts

The instruments: the European call and put, the cash-or-nothing digital, the forward, the capped
call and the power call, each a `Contract Unit` written in the payoff language of
`Contracts/Core.lean`; the exchange option is a `Contract (Fin 2)` on two underlyings. Nothing here
assumes a model or a pricing measure. What is proved is what the instruments pay, along every
scenario. What follows for their values in every model, through the linearity of
`Contract.value`, is in `Pricing/Parity.lean`, and their prices in a particular model live in that
model's file (`Models/BlackScholes/BlackScholes.lean`).

The capped call is *defined* by composition, as a long call at `K₁` and a short call at `K₂`;
`cappedCall_payoff_eq` is what earns it the name: for `K₁ ≤ K₂` it pays
`min(max(S − K₁, 0), K₂ − K₁)` (`MathFin.cappedCall_eq_bull_spread`).

## Main definitions

* `europeanCallPayoff` — the call's payoff on its own.
* `europeanCall`, `europeanPut`, `digitalCall`, `forward` — the single-maturity instruments.
* `cappedCall` — a long `europeanCall K₁ T` combined with a short `europeanCall K₂ T`.
* `powerCall` — the call on `S_T ^ a`, the power being the payoff language's `rpow` node.
* `geomAsianCall` — the call on the geometric average of the underlying over `n` dates, from
  `Payoff.obsProd` and `rpow` at `1/n`.
* `chooser` — the chooser option as the static portfolio of a call and a put at the chooser date.
* `exchangeOption` — pays `max (S¹_T − S²_T) 0`.

## Main results

* `pathPV_europeanCall_eq_put_add_forward` — a call pays a put plus a forward on every path.
* `cappedCall_payoff_eq` — for `K₁ ≤ K₂`, `cappedCall K₁ K₂ T` pays the capped payoff.

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

Compositional contract construction — building an instrument from simpler ones
and pricing it by composition — is the core of Bilokon's DSL and of Peyton
Jones, Eber and Seward before him; what is added here is that the composition
is priced through the library's own closed forms rather than left as a
denotational identity.

No code is copied from `lean_contracts`; every definition and proof here is
written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
§6 for the full credit line.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 12.3

## Tags

European option, digital option, capped call, chooser option, power call, exchange option,
geometric Asian, MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The European call payoff `max (S_T - K) 0`, on its own so that every consumer builds against
the same term rather than re-spelling it. -/
noncomputable def europeanCallPayoff (K : ℝ) (T : ℝ≥0) : Payoff Unit :=
  .max (.sub (.obs () T) (.const K)) (.const 0)

/-- The reified European call: pays `max (S_T - K) 0` at maturity `T`. -/
noncomputable def europeanCall (K : ℝ) (T : ℝ≥0) : Contract Unit :=
  .pay T (europeanCallPayoff K T)

/-- The reified European put: pays `max (K - S_T) 0` at maturity `T`. -/
noncomputable def europeanPut (K : ℝ) (T : ℝ≥0) : Contract Unit :=
  .pay T (.max (.sub (.const K) (.obs () T)) (.const 0))

/-- The reified cash-or-nothing digital call: pays `1` at maturity `T` iff `S_T > K`. -/
noncomputable def digitalCall (K : ℝ) (T : ℝ≥0) : Contract Unit :=
  .pay T (.indicatorLt (.const K) (.obs () T))

/-- The reified power call: pays `max (S_T ^ a - K) 0` at maturity `T`, the power being the
payoff language's `rpow` node at the natural exponent `a`. -/
noncomputable def powerCall (a : ℕ) (K : ℝ) (T : ℝ≥0) : Contract Unit :=
  .pay T (.max (.sub (.rpow (.obs () T) a) (.const K)) (.const 0))

/-- The product of the observations of underlying `i` at the dates `ts`, built from `Payoff.mul`. -/
def Payoff.obsProd {ι : Type*} (i : ι) : List ℝ≥0 → Payoff ι
  | [] => .const 1
  | t :: ts => .mul (.obs i t) (obsProd i ts)

/-- Evaluating `Payoff.obsProd` is the product of the observed values. -/
theorem Payoff.eval_obsProd {ι : Type*} (s : Scenario ι) (i : ι) (ts : List ℝ≥0) :
    (Payoff.obsProd i ts).eval s = (ts.map (s i)).prod := by
  induction ts with
  | nil => simp [Payoff.obsProd, Payoff.eval]
  | cons t ts ih => simp [Payoff.obsProd, Payoff.eval, ih]

/-- The reified geometric-average Asian call over the `n` averaging dates `τ`: pays
`max ((∏ᵢ S_{τᵢ}) ^ (1/n) - K) 0` at maturity `T`, the geometric average being `Payoff.obsProd`
under the `rpow` node at the exponent `1/n`. -/
noncomputable def geomAsianCall (K : ℝ) (T : ℝ≥0) {n : ℕ} (τ : Fin n → ℝ≥0) : Contract Unit :=
  .pay T (.max (.sub (.rpow (.obsProd () (List.ofFn τ)) (n : ℝ≥0)⁻¹) (.const K)) (.const 0))

/-- The reified simple chooser option, by static replication. At the chooser date `t₁ ≤ T` the
holder takes the more valuable of the call and the put, `max (C_{t₁}, P_{t₁})`; put–call parity at
`t₁` (`MathFin.chooserPayoff_decompose_BS`) writes that as
`C_{t₁} + max (K e^{−r(T−t₁)} − S_{t₁}, 0)`. The first term is what a call struck at `K` maturing at
`T` is worth at `t₁`, the second pays at `t₁`, so the chooser is the call at `K, T` together with a
put maturing at `t₁` struck at `K e^{−r(T−t₁)}`. The payoff language has no node for the conditional
value at `t₁`, so this is the replicating portfolio, not the holder's choice written as a payoff;
the rate `r` enters only through the put's strike. -/
noncomputable def chooser (K r : ℝ) (T t₁ : ℝ≥0) : Contract Unit :=
  .both (europeanCall K T) (europeanPut (K * Real.exp (-(r * ((T : ℝ) - t₁)))) t₁)

/-- The reified exchange option (Margrabe) on two underlyings indexed by `Fin 2`: pays
`max (S¹_T - S²_T) 0` at maturity `T`. -/
noncomputable def exchangeOption (T : ℝ≥0) : Contract (Fin 2) :=
  .pay T (.max (.sub (.obs 0 T) (.obs 1 T)) (.const 0))

/-- The reified forward struck at `K`: pays `S_T − K` at maturity `T`. -/
noncomputable def forward (K : ℝ) (T : ℝ≥0) : Contract Unit :=
  .pay T (.sub (.obs () T) (.const K))

/-- A capped call struck at `K₁` and capped at `K₂`, built as a long call at `K₁` and a
short call at `K₂`. `cappedCall_payoff_eq` proves this composed object really does pay
`min (max (S - K₁) 0) (K₂ - K₁)`. -/
noncomputable def cappedCall (K₁ K₂ : ℝ) (T : ℝ≥0) : Contract Unit :=
  .both (europeanCall K₁ T) (.scale (-1) (europeanCall K₂ T))

/-- **The capped call really pays the capped payoff.** For `K₁ ≤ K₂`, `cappedCall K₁ K₂ T`,
the composed long-call/short-call contract, pays exactly `min(max(S − K₁, 0), K₂ − K₁)` along
any scenario — the identity `MathFin.cappedCall_eq_bull_spread` transported from a pointwise
real equation to the contract's own `pathPV`. This is what earns the definition its name. -/
theorem cappedCall_payoff_eq {K₁ K₂ : ℝ} (h : K₁ ≤ K₂) {T : ℝ≥0}
    (s : Scenario Unit) :
    (cappedCall K₁ K₂ T).pathPV (fun _ ↦ 1) s
      = min (max (s () T - K₁) 0) (K₂ - K₁) := by
  simp only [cappedCall, Contract.pathPV, Contract.cashflows, europeanCall, europeanCallPayoff,
    Payoff.eval, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, one_mul, add_zero]
  linarith [MathFin.cappedCall_eq_bull_spread (s () T) K₁ K₂ h]

/-- **A call is a put plus a forward, on every path.** Along any scenario and for any discount,
the call struck at `K` pays what the put struck at `K` and the forward struck at `K` pay together:
`max (S_T − K) 0 = max (K − S_T) 0 + (S_T − K)`. No model is involved. -/
theorem pathPV_europeanCall_eq_put_add_forward (D : ℝ≥0 → ℝ) (s : Scenario Unit) (K : ℝ)
    (T : ℝ≥0) :
    (europeanCall K T).pathPV D s
      = (Contract.both (europeanPut K T) (forward K T)).pathPV D s := by
  simp only [europeanCall, europeanCallPayoff, europeanPut, forward, Contract.pathPV,
    Contract.cashflows, Payoff.eval, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, add_zero, ← mul_add]
  have h := max_zero_sub_max_neg_zero_eq_self (s () T - K)
  rw [neg_sub] at h
  linear_combination D T * h

end MathFin.Contracts
