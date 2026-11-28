/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.Parity
public import LeanPool.MathFin.Models.Binomial.PathMeasure
public import LeanPool.MathFin.Models.Binomial.MartingaleRepresentation

/-!
# The contracts priced in the binomial model

The second model for the instruments of `Contracts/Instruments/Options.lean`, after
`Models/BlackScholes/BlackScholes.lean`. The instruments are the same terms; only the model changes.

The binomial market with step length `h` is a model map on coin-flip paths `ω : ℕ → Bool`: at
time `t` the underlying is the spot after the `⌊t / h⌋` flips made by then,
`spotPath S₀ u d ⌊t / h⌋ ω`. Unlike `BlackScholes.assets` it is a genuine path, not a terminal
value read at every time, so a path-dependent instrument already has the model it needs. Cash
is discounted at `ρ` per step, and paths are drawn from `coinFlipMeasure q` with
`q = crrUpProb u d ρ`: i.i.d. flips, up with the risk-neutral probability. Everything about the
tree itself (the path measure, the spot's measurability and bound, the CRR sequence) lives in
`MathFin/Binomial/`; this file is only the translation of contracts into it.

A single cash flow paying `g` of the spot at a maturity `T` that falls on step `N` is worth the
backward-induction price `binomialPrice u d ρ g N S₀` (`value_pay_eq_binomialPrice`); this is
`binomialPrice_eq_integral_coinFlipMeasure`, which writes the tree price as an expectation over
paths. Every fixed-date contract is integrable here, because the spot after finitely many flips
is bounded
(`integrable_pathPV`), so a composed instrument is priced by composition with no integrability
side conditions to prove.

The value is also a price in the sense of replication. Under no-arbitrage, a European contract's
discounted payoff is, on every path, its value plus the gains of a predictable strategy in the
discounted spot (`pathPV_eq_value_add_gains`). The strategy comes from the tree
(`binomialPrice_replication`, `Models/Binomial/MartingaleRepresentation.lean`).

## Main definitions

* `Binomial.assets` — the binomial market with step `h` as a model map.
* `Binomial.discount` — discounting at `ρ` per step.

## Main results

* `Binomial.value_pay_eq_binomialPrice` — a European payoff is worth its tree price.
* `Binomial.integrable_pathPV` — every fixed-date contract's discounted payoff is integrable.
* `Binomial.value_europeanCall`, `value_europeanPut`, `value_digitalCall` — each is the tree
  price of its payoff.
* `Binomial.value_forward` — under no-arbitrage the forward is worth `S₀ − K e^{−ρN}`.
* `Binomial.value_cappedCall` — the capped call is worth the difference of two call values.
* `Binomial.pathPV_eq_value_add_gains` — a European contract's value is the cost of its hedge: on
  every path its discounted payoff is its value plus the gains of a predictable strategy in the
  discounted spot.

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
* [J. C. Cox, S. A. Ross and M. Rubinstein, *Option pricing: a simplified
  approach*][CoxRossRubinstein1979]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 12.3
* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  Theorem 1.2.2; ch. 1-2

## Tags

binomial tree, Cox–Ross–Rubinstein, replicating strategy, risk-neutral probability, coin-flip paths,
MSC 91G20, MSC 60G42, JEL G13
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts.Binomial

/-- The binomial market with step length `h` as a model map: at time `t` the underlying is the
spot after the `⌊t / h⌋` flips made by then. -/
noncomputable def assets (S₀ u d h : ℝ) : Unit → ℝ≥0 → (ℕ → Bool) → ℝ :=
  fun _ t ω ↦ spotPath S₀ u d ⌊(t : ℝ) / h⌋₊ ω

/-- Discounting at `ρ` per step of length `h`: a cash flow at time `t` is worth `e^{−ρ t / h}` of
one paid today. -/
noncomputable def discount (ρ h : ℝ) : ℝ≥0 → ℝ := fun t ↦ Real.exp (-(ρ * (t / h)))

variable {u d ρ h : ℝ} {q : ℝ≥0} (hq : q ≤ 1)

/-- **A European payoff is worth its tree price.** Under the law of i.i.d. flips that go up with
the risk-neutral probability `crrUpProb u d ρ`, if a cash flow at `T` pays `g` of the underlying
at `T`, whatever the scenario, and `T` falls on step `N`, its binomial value is the
backward-induction price `binomialPrice u d ρ g N S₀`. -/
theorem value_pay_eq_binomialPrice (hqcrr : crrUpProb u d ρ = q) (S₀ : ℝ) {T : ℝ≥0} {N : ℕ}
    (hTN : (T : ℝ) / h = N) {a : Payoff Unit} {g : ℝ → ℝ}
    (hg : ∀ s : Scenario Unit, a.eval s = g (s () T)) :
    (Contract.pay T a).value (coinFlipMeasure q hq) (fun t _ ↦ discount ρ h t) (assets S₀ u d h)
      = binomialPrice u d ρ g N S₀ := by
  rw [Contract.value_pay, binomialPrice_eq_integral_coinFlipMeasure u d ρ g hq hqcrr N S₀]
  simp only [hg, scenarioAt, assets, discount, hTN, Nat.floor_natCast]
  exact integral_const_mul _ _

/-- **Every fixed-date contract is integrable in the binomial model**, under any law of the flips:
the spot after finitely many flips is measurable and bounded (`measurable_spotPath`,
`abs_spotPath_le`), so `Contract.integrable_pathPV_of_bounded` applies. -/
theorem integrable_pathPV (S₀ u d h : ℝ) (D : ℝ≥0 → ℝ) {c : Contract Unit} (hc : c.FixedDated) :
    Integrable (fun ω ↦ c.pathPV D (scenarioAt (assets S₀ u d h) ω)) (coinFlipMeasure q hq) :=
  Contract.integrable_pathPV_of_bounded D (fun _ _ ↦ measurable_spotPath ..)
    (fun _ t ↦ ⟨_, abs_spotPath_le S₀ u d ⌊(t : ℝ) / h⌋₊⟩) hc

variable (hqcrr : crrUpProb u d ρ = q) (S₀ K : ℝ) {T : ℝ≥0} {N : ℕ} (hTN : (T : ℝ) / h = N)
include hqcrr hTN

/-- The European call's binomial value is the tree price of `max (S − K) 0`. -/
theorem value_europeanCall :
    (europeanCall K T).value (coinFlipMeasure q hq) (fun t _ ↦ discount ρ h t) (assets S₀ u d h)
      = binomialPrice u d ρ (fun S ↦ max (S - K) 0) N S₀ :=
  value_pay_eq_binomialPrice hq hqcrr S₀ hTN fun _ ↦ rfl

/-- The European put's binomial value is the tree price of `max (K − S) 0`. -/
theorem value_europeanPut :
    (europeanPut K T).value (coinFlipMeasure q hq) (fun t _ ↦ discount ρ h t) (assets S₀ u d h)
      = binomialPrice u d ρ (fun S ↦ max (K - S) 0) N S₀ :=
  value_pay_eq_binomialPrice hq hqcrr S₀ hTN fun _ ↦ rfl

/-- The cash-or-nothing digital call's binomial value is the tree price of `𝟙{S > K}`. -/
theorem value_digitalCall :
    (digitalCall K T).value (coinFlipMeasure q hq) (fun t _ ↦ discount ρ h t) (assets S₀ u d h)
      = binomialPrice u d ρ (fun S ↦ if K < S then 1 else 0) N S₀ :=
  value_pay_eq_binomialPrice hq hqcrr S₀ hTN fun _ ↦ rfl

/-- **The forward's binomial value** is `S₀ − K e^{−ρN}` under no-arbitrage: the discounted spot
is a martingale (`binomialPrice_id`) and cash is discounted at `ρ` per step
(`binomialPrice_const`). -/
theorem value_forward (hna : BinomialNoArb u d ρ) :
    (forward K T).value (coinFlipMeasure q hq) (fun t _ ↦ discount ρ h t) (assets S₀ u d h)
      = S₀ - K * Real.exp (-(ρ * N)) := by
  rw [forward, value_pay_eq_binomialPrice hq hqcrr S₀ hTN (g := fun S ↦ S + -K)
      fun _ ↦ sub_eq_add_neg _ _,
    binomialPrice_add u d ρ (fun S ↦ S) (fun _ ↦ -K), binomialPrice_id u d ρ hna,
    binomialPrice_const u d ρ _ hna, show -(N : ℝ) * ρ = -(ρ * N) by ring]
  ring

/-- **The capped call's binomial value, by composition**: the difference of two call values.
Unlike its Black–Scholes counterpart it needs no integrability argument, since every fixed-date
contract is integrable in this model (`integrable_pathPV`). -/
theorem value_cappedCall (K₂ : ℝ) :
    (cappedCall K K₂ T).value (coinFlipMeasure q hq) (fun t _ ↦ discount ρ h t) (assets S₀ u d h)
      = binomialPrice u d ρ (fun S ↦ max (S - K) 0) N S₀
        - binomialPrice u d ρ (fun S ↦ max (S - K₂) 0) N S₀ := by
  rw [cappedCall, Contract.value_both _ _ _ _ _
    (integrable_pathPV hq S₀ u d h _ (c := europeanCall K T) trivial)
    (integrable_pathPV hq S₀ u d h _ (c := .scale (-1) (europeanCall K₂ T)) trivial),
    Contract.value_scale,
    value_europeanCall hq hqcrr S₀ K hTN, value_europeanCall hq hqcrr S₀ K₂ hTN]
  ring

/-- **A European contract's binomial value is the cost of its hedge.** Under no-arbitrage, with
paths drawn under the risk-neutral up-probability and `S₀ ≠ 0`, there is a predictable strategy
`H` (`H_{k+1}` is `ℱₖ`-strongly measurable for `flipFiltration`: it depends only on the first `k`
flips) such that, on every path, the contract's
discounted payoff is its value plus the strategy's gains in the discounted spot
`S_tilde_k = e^{−ρk} S_k`, its `martingaleTransform`:

  `pathPV = value + ∑_{k<N} H_{k+1} (S_tilde_{k+1} − S_tilde_k)`.

So the value is not only an expectation: it is the initial capital that replicates the
contract. -/
theorem pathPV_eq_value_add_gains (hna : BinomialNoArb u d ρ) (hS₀ : S₀ ≠ 0) {a : Payoff Unit}
    {g : ℝ → ℝ} (hg : ∀ s : Scenario Unit, a.eval s = g (s () T)) :
    ∃ H : ℕ → (ℕ → Bool) → ℝ, StronglyAdapted flipFiltration (fun n ↦ H (n + 1)) ∧ ∀ ω,
      (Contract.pay T a).pathPV (discount ρ h) (scenarioAt (assets S₀ u d h) ω)
        = (Contract.pay T a).value (coinFlipMeasure q hq) (fun t _ ↦ discount ρ h t)
            (assets S₀ u d h)
          + martingaleTransform H (discountedSpot S₀ u d ρ) N ω := by
  obtain ⟨H, hH, hrep⟩ := binomialPrice_replication hna hS₀ g N
  refine ⟨H, hH, fun ω ↦ ?_⟩
  rw [value_pay_eq_binomialPrice hq hqcrr S₀ hTN hg, ← hrep ω]
  simp [Contract.pathPV, Contract.cashflows, hg, scenarioAt, assets, discount, hTN]

end MathFin.Contracts.Binomial

namespace MathFin

open Contracts

/-- **Put-call parity at the binomial level**: `call = put + (S − K·e^{−nr})`. The call is the
put plus the forward on every path (`value_europeanCall_eq_put_add_forward`), and in the tree the
forward is worth `S − K e^{−nr}` (`Binomial.value_forward`); the contracts' values are the tree
prices (`Binomial.value_europeanCall`, `Binomial.value_europeanPut`) for the step length `1`
and the risk-neutral up-probability. -/
lemma binomialPrice_callPut_parity {u d r K : ℝ} (h : BinomialNoArb u d r) (n : ℕ) (S : ℝ) :
    binomialPrice u d r (fun x ↦ max (x - K) 0) n S
      = binomialPrice u d r (fun x ↦ max (K - x) 0) n S
        + (S - K * Real.exp (-(n : ℝ) * r)) := by
  have hp := crrUpProb_mem_Ioo h
  have hq : (⟨crrUpProb u d r, hp.1.le⟩ : ℝ≥0) ≤ 1 := hp.2.le
  have hTN : (((n : ℝ≥0) : ℝ)) / 1 = n := by simp
  have := value_europeanCall_eq_put_add_forward (K := K) (T := (n : ℝ≥0))
    (coinFlipMeasure _ hq) (fun t _ ↦ Binomial.discount r 1 t) (Binomial.assets S u d 1)
    (Binomial.integrable_pathPV hq S u d 1 _ (c := europeanPut K n) trivial)
    (Binomial.integrable_pathPV hq S u d 1 _ (c := forward K n) trivial)
  rw [Binomial.value_europeanCall hq rfl S K hTN, Binomial.value_europeanPut hq rfl S K hTN,
    Binomial.value_forward hq rfl S K hTN h] at this
  rw [this, show -(n : ℝ) * r = -(r * n) by ring]

end MathFin
