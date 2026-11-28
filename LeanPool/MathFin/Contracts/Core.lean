/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.Process.HittingTime

/-!
# A reified payoff language

`Payoff ι` and `Contract ι` represent *what an instrument pays*, independently of
any stochastic model. Market outcomes enter through `Scenario ι = ι → ℝ≥0 → ℝ`;
a stochastic model is a law on that type, and appears only from
`Pricing/Value.lean` onward.

Every other payoff in this library — `Models/BlackScholes/Call.lean`, `Digital.lean`,
`CappedCall.lean` — is written inline as a lambda inside the integral that prices
it, so the payoff and the model are the same syntactic object. This file
separates them, which is what lets `Models/BlackScholes/BlackScholes.lean` price a capped
call by *composing* two European call values rather than by evaluating a third
integral.

## Payments at a random date

`Contract.pay` fixes its date. `Contract.payAtHit i A amount` pays at the first time the observed
underlying `i` enters the set `A` (`Scenario.hitTime`, Mathlib's `hittingAfter` of the observed
path), which is how a payment at a default time is written: the underlying is the default
indicator `1{τ ≤ u}` and `A = [1, ∞)`. The model-free results below hold for every contract; the
integrability theorem of `Contracts/Adapted.lean` is for `Contract.FixedDated` ones, since a
hitting time of an arbitrary path is not measurable and an unbounded discount factor evaluated at
it need not be integrable.

## Deliberately absent

Branching contracts (`ifThen`), currency, and the lifecycle layer (outstanding
notional, termination, partial redemption). Each is additive and each waits for
the corpus entry that forces it; see
`docs/specs/2026-08-16-contracts-tower-design.md` §2.3.

## Main definitions

* `Scenario ι`: a market scenario `ι → ℝ≥0 → ℝ`, the realized value of each underlying at each
  time.
* `Payoff ι`: payoff formulas as data (constants, observations, `add`, `sub`, `mul`, `max`, `min`,
  `indicatorLt`, and `rpow` with an `ℝ≥0` exponent); `Payoff.eval` interprets one against a
  scenario.
* `Payoff.obsList`: the `(underlying, date)` observations a payoff reads, found syntactically.
* `Contract.obsList`: the observations a contract's payoffs read.
* `Scenario.hitTime`: the first time the observed underlying `i` lies in `A`, as Mathlib's
  `hittingAfter` of the observed path.
* `Contract ι`: contracts built from `zero`, `pay t amount`, `payAtHit i A amount`, `both` and
  `scale`.
* `Contract.cashflows`: the list of `(time, amount)` cashflows of a contract along a scenario.
* `Contract.FixedDated`: the contract contains no `payAtHit`.
* `Contract.dates`: the payment dates of a contract's `pay` nodes.
* `Contract.pathPV`: the present value of a contract along one scenario path, for a discount
  function `D : ℝ≥0 → ℝ`.

## Main results

* `Contract.pathPV_both`, `Contract.pathPV_scale` — `pathPV` is additive over
  `both` and homogeneous over `scale`. These are what `Pricing/Value.lean`
  integrates to get linearity of `value`.
* `Contract.pathPV_const` — a constant discount factor comes out of `pathPV`.
* `Payoff.eval_congr`, `Contract.cashflows_congr` — a payoff, and a fixed-dated contract's cash
  flows, are the same on two scenarios that agree at the observations they read
  (`Payoff.obsList`, `Contract.obsList`). `Pricing/Value.lean` lifts this to models that agree
  almost surely (`Contract.value_congr_ae`).
* `Contract.pathPV_congr` — a fixed-dated contract's present value depends on the scenario only
  at `c.obsList` and on the discount factor only at `c.dates`. `Pricing/Value.lean` lifts this to
  models whose observations have one law (`Contract.value_eq_of_map_observation_eq`).

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

This file takes his separation of the payoff object from the probability law.
The type design is ours: a typed underlying index rather than `String` keys, a
single inductive rather than a mutual `NumExpr` / `BoolExpr` pair, and `ℝ≥0` time
matching `Filtration ℝ≥0 mΩ`.

No code is copied from `lean_contracts`; every definition and proof here is
written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
§6 for the full credit line.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [S. Peyton Jones, J. M. Eber and J. Seward, *Composing contracts*][PeytonJonesEberSeward2000]

## Tags

contract language, reified payoff, contract DSL, Bilokon, Peyton Jones, payment at default time,
MSC 91G20, JEL G13
-/

@[expose] public section

open scoped NNReal

namespace MathFin.Contracts

variable {ι : Type*}

/-- A market scenario: for each underlying `i : ι` and time `t : ℝ≥0`, its
realized value. A stochastic model is a probability law on this type. -/
abbrev Scenario (ι : Type*) := ι → ℝ≥0 → ℝ

/-- A payoff formula, reified as data rather than written inline as a lambda.
Independent of any scenario until `Payoff.eval` interprets it against one. -/
inductive Payoff (ι : Type*) where
  | const (c : ℝ)
  | obs (i : ι) (t : ℝ≥0)
  | add (a b : Payoff ι)
  | sub (a b : Payoff ι)
  | mul (a b : Payoff ι)
  | max (a b : Payoff ι)
  | min (a b : Payoff ι)
  | indicatorLt (a b : Payoff ι)
  /-- A nonnegative real power. The exponent is an `ℝ≥0`, so `eval` stays continuous in the
  observations and bounded on bounded scenarios; there is no `exp` or `log` node, since `log` is
  unbounded near `0`. Meaningful on nonnegative observations: at a negative base `Real.rpow` is
  the junk value `|x|^p cos(pπ)`, which no model theorem here reaches (spots are positive). -/
  | rpow (a : Payoff ι) (p : ℝ≥0)

/-- Interpret a `Payoff` against a `Scenario`, producing its realized value. -/
noncomputable def Payoff.eval (s : Scenario ι) : Payoff ι → ℝ
  | .const c => c
  | .obs i t => s i t
  | .add a b => eval s a + eval s b
  | .sub a b => eval s a - eval s b
  | .mul a b => eval s a * eval s b
  | .max a b => Max.max (eval s a) (eval s b)
  | .min a b => Min.min (eval s a) (eval s b)
  | .indicatorLt a b => if eval s a < eval s b then 1 else 0
  | .rpow a p => eval s a ^ (p : ℝ)

/-- The `(underlying, date)` observations a `Payoff` reads, found syntactically. An
over-approximation: `Payoff.mul (.const 0) (.obs i t)` evaluates to `0` on every scenario, yet
lists `(i, t)`. -/
def Payoff.obsList : Payoff ι → List (ι × ℝ≥0)
  | .const _ => []
  | .obs i t => [(i, t)]
  | .add a b | .sub a b | .mul a b | .max a b | .min a b | .indicatorLt a b =>
      a.obsList ++ b.obsList
  | .rpow a _ => a.obsList

/-- The first time the observed underlying `i` of a scenario lies in `A`: Mathlib's
`hittingAfter` of the process `u ↦ s i u` at time `0`, which is `⊤` if it never does. It is the
infimum of the times at which the observation is in `A`, so it is attained when the path is right
continuous and `A` closed. -/
noncomputable def Scenario.hitTime (s : Scenario ι) (i : ι) (A : Set ℝ) : WithTop ℝ≥0 :=
  MeasureTheory.hittingAfter (fun u (s : Scenario ι) ↦ s i u) A 0 s

/-- A contract: what gets paid, when, built from `Payoff`s by combination. -/
inductive Contract (ι : Type*) where
  | zero
  | pay (t : ℝ≥0) (amount : Payoff ι)
  /-- A payment at a random date: `amount` is paid at the first time the observed underlying `i`
  lies in `A` (`Scenario.hitTime`), and nothing is paid if it never does. After the `when` of
  Peyton Jones, Eber and Seward (2000), with the event reduced to an observed underlying entering a
  set. `amount` is observed at its own fixed dates, as in `pay`. That the date is a stopping time
  of a model's filtration is not asserted here. -/
  | payAtHit (i : ι) (A : Set ℝ) (amount : Payoff ι)
  | both (a b : Contract ι)
  | scale (c : ℝ) (a : Contract ι)

/-- The list of `(time, amount)` cashflows a `Contract` generates along a
given `Scenario`. -/
noncomputable def Contract.cashflows (s : Scenario ι) :
    Contract ι → List (ℝ≥0 × ℝ)
  | .zero => []
  | .pay t a => [(t, a.eval s)]
  | .payAtHit i A a =>
      WithTop.recTopCoe (C := fun _ ↦ List (ℝ≥0 × ℝ)) [] (fun τ ↦ [(τ, a.eval s)])
        (s.hitTime i A)
  | .both a b => cashflows s a ++ cashflows s b
  | .scale c a => (cashflows s a).map fun p ↦ (p.1, c * p.2)

/-- A contract **pays at fixed dates** if it contains no `payAtHit`: the dates of its cashflows
are then the same in every scenario. -/
def Contract.FixedDated : Contract ι → Prop
  | .zero => True
  | .pay _ _ => True
  | .payAtHit _ _ _ => False
  | .both a b => a.FixedDated ∧ b.FixedDated
  | .scale _ a => a.FixedDated

/-- The present value of a `Contract` along one scenario path, given a
discount factor `D : ℝ≥0 → ℝ`. -/
noncomputable def Contract.pathPV (D : ℝ≥0 → ℝ) (s : Scenario ι)
    (c : Contract ι) : ℝ :=
  ((c.cashflows s).map fun p ↦ D p.1 * p.2).sum

/-- **A payment at the hitting time**, when the underlying does hit `A`, at the time `τ`: the
discounted amount at `τ`. -/
theorem Contract.pathPV_payAtHit_of_eq (D : ℝ≥0 → ℝ) (s : Scenario ι) {i : ι} {A : Set ℝ}
    {τ : ℝ≥0} (a : Payoff ι) (h : s.hitTime i A = τ) :
    (Contract.payAtHit i A a).pathPV D s = D τ * a.eval s := by
  simp only [pathPV, cashflows, h]
  change (([(τ, a.eval s)] : List (ℝ≥0 × ℝ)).map fun p ↦ D p.1 * p.2).sum = _
  simp

/-- **A payment at the hitting time is nothing** if the underlying never hits `A`. -/
theorem Contract.pathPV_payAtHit_of_eq_top (D : ℝ≥0 → ℝ) (s : Scenario ι) {i : ι} {A : Set ℝ}
    (a : Payoff ι) (h : s.hitTime i A = ⊤) : (Contract.payAtHit i A a).pathPV D s = 0 := by
  simp [pathPV, cashflows, h]

theorem Contract.pathPV_both (D : ℝ≥0 → ℝ) (s : Scenario ι)
    (a b : Contract ι) :
    (Contract.both a b).pathPV D s = a.pathPV D s + b.pathPV D s := by
  simp [pathPV, cashflows]

theorem Contract.pathPV_scale (D : ℝ≥0 → ℝ) (s : Scenario ι)
    (c : ℝ) (a : Contract ι) :
    (Contract.scale c a).pathPV D s = c * a.pathPV D s := by
  simp only [pathPV, cashflows, List.map_map]
  rw [← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun p _ ↦ by simp; ring)

/-- A constant discount factor comes out of `pathPV`: discounting every cashflow by `a` is
discounting the undiscounted present value by `a`. -/
theorem Contract.pathPV_const (a : ℝ) (s : Scenario ι) (c : Contract ι) :
    c.pathPV (fun _ ↦ a) s = a * c.pathPV (fun _ ↦ 1) s := by
  simp [pathPV, List.sum_map_mul_left]

/-! ### Two scenarios that agree where the contract looks -/

/-- A payoff evaluates the same on two scenarios that agree at the observations it reads. -/
theorem Payoff.eval_congr {s s' : Scenario ι} (a : Payoff ι)
    (h : ∀ p ∈ a.obsList, s p.1 p.2 = s' p.1 p.2) : a.eval s = a.eval s' := by
  induction a with
  | const _ => rfl
  | obs i t => exact h (i, t) (List.mem_singleton_self _)
  | add a b ha hb | sub a b ha hb | mul a b ha hb | max a b ha hb | min a b ha hb
  | indicatorLt a b ha hb =>
      obtain ⟨hl, hr⟩ := List.forall_mem_append.1 h
      simp only [Payoff.eval, ha hl, hb hr]
  | rpow a _ ha => simp only [Payoff.eval, ha h]

/-- The `(underlying, date)` observations a `Contract` reads (those of its payoffs; the dates of
a `payAtHit` are not listed, which is why the congruence below asks for `FixedDated`). -/
def Contract.obsList : Contract ι → List (ι × ℝ≥0)
  | .zero => []
  | .pay _ a => a.obsList
  | .payAtHit _ _ a => a.obsList
  | .both a b => a.obsList ++ b.obsList
  | .scale _ a => a.obsList

/-- A fixed-dated contract generates the same cash flows along two scenarios that agree at the
observations it reads. -/
theorem Contract.cashflows_congr {s s' : Scenario ι} (c : Contract ι) (hc : c.FixedDated)
    (h : ∀ p ∈ c.obsList, s p.1 p.2 = s' p.1 p.2) : c.cashflows s = c.cashflows s' := by
  induction c with
  | zero => rfl
  | pay t a => simp only [Contract.cashflows, Payoff.eval_congr a h]
  | payAtHit _ _ _ => exact hc.elim
  | both a b ha hb =>
      obtain ⟨hl, hr⟩ := List.forall_mem_append.1 h
      simp only [Contract.cashflows, ha hc.1 hl, hb hc.2 hr]
  | scale _ a ha => simp only [Contract.cashflows, ha hc h]

/-- The payment dates of a contract: the dates of its `pay` nodes. A `payAtHit` pays at a date the
scenario decides and lists none, which is why the congruence below asks for `FixedDated`. -/
def Contract.dates : Contract ι → List ℝ≥0
  | .zero => []
  | .pay t _ => [t]
  | .payAtHit _ _ _ => []
  | .both a b => a.dates ++ b.dates
  | .scale _ a => a.dates

/-- **A fixed-dated contract reads a scenario only at its observations and a discount factor only
at its payment dates**: two discount factors that agree on `c.dates`, along two scenarios that
agree on `c.obsList`, give the same present value. -/
theorem Contract.pathPV_congr {D D' : ℝ≥0 → ℝ} {s s' : Scenario ι} (c : Contract ι)
    (hc : c.FixedDated) (hD : ∀ t ∈ c.dates, D t = D' t)
    (hs : ∀ p ∈ c.obsList, s p.1 p.2 = s' p.1 p.2) : c.pathPV D s = c.pathPV D' s' := by
  induction c with
  | zero => rfl
  | pay t a =>
      simp only [pathPV, cashflows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        hD t (List.mem_singleton_self t), Payoff.eval_congr a hs]
  | payAtHit _ _ _ => exact hc.elim
  | both a b ha hb =>
      obtain ⟨hDa, hDb⟩ := List.forall_mem_append.1 hD
      obtain ⟨hsa, hsb⟩ := List.forall_mem_append.1 hs
      rw [pathPV_both, pathPV_both, ha hc.1 hDa hsa, hb hc.2 hDb hsb]
  | scale _ a ha => rw [pathPV_scale, pathPV_scale, ha hc hD hs]

end MathFin.Contracts
