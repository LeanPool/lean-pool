/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Contracts.Core

/-!
# A payoff is measurable, adapted to its observation times, and integrable in a bounded model

A `Payoff` is data, not yet a random variable: `Payoff.eval` only produces one
once it is applied to a `Scenario`. This file supplies the missing link —
substitute a genuinely stochastic model `X : ι → ℝ≥0 → Ω → ℝ` for the
`Scenario`, and `fun ω ↦ e.eval (fun i t ↦ X i t ω)` is measurable
(`Payoff.measurable_eval`), and moreover `𝓕 u`-measurable as soon as every
observation the payoff makes is dated no later than `u`
(`Payoff.measurable_eval_of_obsList_le`). That second fact is what will make a
`Payoff` a legitimate stochastic-integral integrand: it is the adaptedness
hypothesis a future integral rung against a filtered probability space will
need. **`measurable_eval_of_obsList_le` has no consumer yet** —
`Pricing/Value.lean` integrates only against a fixed measure `Q`, never
against a filtration, so it has no adaptedness hypothesis to discharge with
this file's results.

`Payoff.aemeasurable_eval` weakens `measurable_eval`'s hypothesis from
`Measurable` to `AEMeasurable` — the strength the tower's own pricing
hypotheses actually supply (`BSCallHyp`'s `Z_law : HasLaw Z (gaussianReal 0 1)
Q` gives only `AEMeasurable Z`, never `Measurable Z`). It has no consumer
now either: the integrability lemmas of `Models/BlackScholes/BlackScholes.lean` build each
reified payoff from integrable pieces (`Integrable.pos_part`, `.sub`,
`.const_mul`), which carry their own measurability.

`Contract.integrable_pathPV_of_bounded` is the consumer `measurable_eval` was waiting for: in a
model whose every coordinate is bounded, the discounted payoff of every contract that pays at fixed
dates (`Contract.FixedDated`) is integrable against any finite measure. Measurability comes from
`measurable_eval`, and the bound from `Payoff.exists_bound_eval`, a structural induction like the
others. A finite-state model such as
the binomial tree is bounded, so there `Contract.value_both` needs no per-instrument
integrability lemma (`Models/Binomial/Binomial.lean`).

## Main results

* `Payoff.measurable_eval` — evaluating a payoff against a jointly-measurable
  model is measurable, unconditionally.
* `Contract.measurable_pathPV` — a fixed-dated contract's present value under a measurable
  stochastic discount factor is measurable.
* `Payoff.measurable_eval_of_obsList_le` — if every date in `e.obsList` (the syntactic list of
  observations `Contracts/Core.lean` defines; an over-approximation, so the criterion is
  sufficient, not necessary: `Payoff.mul (.const 0) (.obs i t)` lists `t` though its value does
  not depend on it) is `≤ u` and each `X i t` is `𝓕 t`-measurable, then evaluating `e` against `X`
  is `𝓕 u`-measurable. The filtration's monotonicity (`𝓕.mono`) does the work
  in the `obs` leaf; the six binary constructors combine two adapted pieces
  into one by the corresponding `Measurable.add`/`.sub`/`.mul`/`.max`/`.min`
  lemma, or `Measurable.ite` composed with `measurableSet_lt` for
  `indicatorLt`; `rpow` keeps the adapted piece under `Measurable.pow_const`.
* `Payoff.aemeasurable_eval` — the same conclusion as `measurable_eval`, from
  the weaker hypothesis that each `X i t` is only `AEMeasurable`. Built from
  `measurable_eval` applied to measurable representatives `(hX i t).mk (X i
  t)`, transported across the a.e. equality `e.eval X =ᵐ[μ] e.eval X'` proved
  by a second structural induction (each `obs` leaf contributes
  `AEMeasurable.ae_eq_mk`; the six binary constructors combine two a.e. facts
  by `filter_upwards`, and `rpow` from the one) — not a direct induction into
  `AEMeasurable`, whose `indicatorLt` case would need a `NullMeasurableSet` this route avoids
  producing.
* `Payoff.exists_bound_eval` — against a model with bounded coordinates, a payoff is bounded
  (a nonnegative power by `Real.abs_rpow_le_abs_rpow`).
* `Contract.integrable_pathPV_of_bounded` — against a finite measure and a measurable, bounded
  model, the discounted payoff of every fixed-date contract is integrable.

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

Bilokon's `Contract.observationTimes` exists to feed a syntactic chronology
check discharged `by decide`; the same function here carries content, as the
hypothesis of an adaptedness theorem. The measurability and adaptedness
results have no counterpart in the source.

No code is copied from `lean_contracts`; every definition and proof here is
written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
§6 for the full credit line.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], ch. 3-4

## Tags

payoff measurability, adapted payoff, filtration, observation times, integrability, MSC 91G20,
MSC 60G07, JEL G13
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Evaluating a payoff against a jointly-measurable model is measurable. -/
theorem Payoff.measurable_eval (e : Payoff ι) (X : ι → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i t, Measurable (X i t)) :
    Measurable fun ω ↦ e.eval (fun i t ↦ X i t ω) := by
  induction e with
  | const c => exact measurable_const
  | obs i t => exact hX i t
  | add a b ha hb => exact ha.add hb
  | sub a b ha hb => exact ha.sub hb
  | mul a b ha hb => exact ha.mul hb
  | max a b ha hb => exact ha.max hb
  | min a b ha hb => exact ha.min hb
  | indicatorLt a b ha hb =>
      exact Measurable.ite (measurableSet_lt ha hb) measurable_const measurable_const
  | rpow a p ha => exact ha.pow_const _

/-- **A fixed-dated contract's deflated present value is measurable** for a measurable model and
a measurable stochastic discount factor `D : ℝ≥0 → Ω → ℝ`. -/
theorem Contract.measurable_pathPV {c : Contract ι} (hc : c.FixedDated) {D : ℝ≥0 → Ω → ℝ}
    (hD : ∀ t, Measurable (D t)) {X : ι → ℝ≥0 → Ω → ℝ} (hX : ∀ i t, Measurable (X i t)) :
    Measurable fun ω ↦ c.pathPV (fun t ↦ D t ω) (fun i t ↦ X i t ω) := by
  induction c with
  | zero =>
      simp only [Contract.pathPV, Contract.cashflows, List.map_nil, List.sum_nil]
      exact measurable_const
  | pay t a =>
      simp only [Contract.pathPV, Contract.cashflows, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      exact (hD t).mul (a.measurable_eval X hX)
  | payAtHit _ _ _ => exact hc.elim
  | both a b ha hb =>
      simp only [Contract.pathPV_both]
      exact (ha hc.1).add (hb hc.2)
  | scale r a ha =>
      simp only [Contract.pathPV_scale]
      exact (ha hc).const_mul r

/-- Evaluating a payoff against an a.e.-measurable model is a.e.-measurable: the strength a
consumer whose model only satisfies `AEMeasurable` (e.g. `HasLaw.aemeasurable`, never
`Measurable`) actually has. Built from `measurable_eval` on each model coordinate's measurable
representative `(hX i t).mk (X i t)`, transported across its a.e. equality with the original —
not a second induction into `AEMeasurable`, whose `indicatorLt` case wants a
`NullMeasurableSet` awkward to produce here. -/
theorem Payoff.aemeasurable_eval {μ : Measure Ω} (e : Payoff ι) (X : ι → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i t, AEMeasurable (X i t) μ) :
    AEMeasurable (fun ω ↦ e.eval (fun i t ↦ X i t ω)) μ := by
  let X' : ι → ℝ≥0 → Ω → ℝ := fun i t ↦ (hX i t).mk (X i t)
  have heq (e : Payoff ι) : (fun ω ↦ e.eval (fun i t ↦ X i t ω))
      =ᵐ[μ] fun ω ↦ e.eval (fun i t ↦ X' i t ω) := by
    induction e with
    | const c => exact .of_forall fun _ ↦ rfl
    | obs i t => exact (hX i t).ae_eq_mk
    | add a b ha hb => filter_upwards [ha, hb] with ω hae hbe; simp only [Payoff.eval, hae, hbe]
    | sub a b ha hb => filter_upwards [ha, hb] with ω hae hbe; simp only [Payoff.eval, hae, hbe]
    | mul a b ha hb => filter_upwards [ha, hb] with ω hae hbe; simp only [Payoff.eval, hae, hbe]
    | max a b ha hb => filter_upwards [ha, hb] with ω hae hbe; simp only [Payoff.eval, hae, hbe]
    | min a b ha hb => filter_upwards [ha, hb] with ω hae hbe; simp only [Payoff.eval, hae, hbe]
    | indicatorLt a b ha hb =>
        filter_upwards [ha, hb] with ω hae hbe; simp only [Payoff.eval, hae, hbe]
    | rpow a p ha => filter_upwards [ha] with ω hae; simp only [Payoff.eval, hae]
  have hX'meas : ∀ i t, Measurable (X' i t) := fun i t ↦ (hX i t).measurable_mk
  exact (Payoff.measurable_eval e X' hX'meas).aemeasurable.congr (heq e).symm

/-- Evaluating a payoff against a filtration-adapted model `X` is adapted to
`𝓕 u`, as soon as every time the payoff observes is dated no later than `u`.
This is the theorem that will make a `Payoff` a legitimate stochastic-integral
integrand — the adaptedness hypothesis a future integral rung will need.
Still has no consumer: `Pricing/Value.lean` integrates against a fixed
measure, not a filtration, and unlike `measurable_eval`'s a.e. counterpart
above, no `Payoff` in the tower yet needs an argument observed before a fixed
time rather than a fixed measure. -/
theorem Payoff.measurable_eval_of_obsList_le
    {𝓕 : Filtration ℝ≥0 mΩ} {u : ℝ≥0} (e : Payoff ι) (X : ι → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i t, Measurable[𝓕 t] (X i t))
    (hle : ∀ p ∈ e.obsList, p.2 ≤ u) :
    Measurable[𝓕 u] fun ω ↦ e.eval (fun i t ↦ X i t ω) := by
  induction e generalizing u with
  | const c => exact measurable_const
  | obs i t => exact (hX i t).mono (𝓕.mono (hle (i, t) (by simp [Payoff.obsList]))) le_rfl
  | add a b ha hb =>
      obtain ⟨hl, hr⟩ := List.forall_mem_append.1 hle; exact (ha hl).add (hb hr)
  | sub a b ha hb =>
      obtain ⟨hl, hr⟩ := List.forall_mem_append.1 hle; exact (ha hl).sub (hb hr)
  | mul a b ha hb =>
      obtain ⟨hl, hr⟩ := List.forall_mem_append.1 hle; exact (ha hl).mul (hb hr)
  | max a b ha hb =>
      obtain ⟨hl, hr⟩ := List.forall_mem_append.1 hle; exact (ha hl).max (hb hr)
  | min a b ha hb =>
      obtain ⟨hl, hr⟩ := List.forall_mem_append.1 hle; exact (ha hl).min (hb hr)
  | indicatorLt a b ha hb =>
      obtain ⟨hl, hr⟩ := List.forall_mem_append.1 hle
      exact Measurable.ite (measurableSet_lt (ha hl) (hb hr)) measurable_const measurable_const
  | rpow a p ha => exact (ha hle).pow_const _

/-- Evaluating a payoff against a model whose every coordinate is bounded is bounded: each
constructor combines its bounds into one, an indicator is bounded by `1`, and a nonnegative power
by the power of the bound (`Real.abs_rpow_le_abs_rpow`). -/
theorem Payoff.exists_bound_eval (e : Payoff ι) {X : ι → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i t, ∃ C, ∀ ω, |X i t ω| ≤ C) : ∃ C, ∀ ω, |e.eval (fun i t ↦ X i t ω)| ≤ C := by
  induction e with
  | const c => exact ⟨|c|, fun _ ↦ le_rfl⟩
  | obs i t => exact hX i t
  | add a b ha hb =>
      obtain ⟨⟨Ca, ha⟩, ⟨Cb, hb⟩⟩ := And.intro ha hb
      exact ⟨Ca + Cb, fun ω ↦ (abs_add_le _ _).trans (add_le_add (ha ω) (hb ω))⟩
  | sub a b ha hb =>
      obtain ⟨⟨Ca, ha⟩, ⟨Cb, hb⟩⟩ := And.intro ha hb
      exact ⟨Ca + Cb, fun ω ↦ (abs_sub _ _).trans (add_le_add (ha ω) (hb ω))⟩
  | mul a b ha hb =>
      obtain ⟨⟨Ca, ha⟩, ⟨Cb, hb⟩⟩ := And.intro ha hb
      exact ⟨Ca * Cb, fun ω ↦ (abs_mul _ _).trans_le
        (mul_le_mul (ha ω) (hb ω) (abs_nonneg _) ((abs_nonneg _).trans (ha ω)))⟩
  | max a b ha hb =>
      obtain ⟨⟨Ca, ha⟩, ⟨Cb, hb⟩⟩ := And.intro ha hb
      exact ⟨Max.max Ca Cb, fun ω ↦ abs_max_le_max_abs_abs.trans (max_le_max (ha ω) (hb ω))⟩
  | min a b ha hb =>
      obtain ⟨⟨Ca, ha⟩, ⟨Cb, hb⟩⟩ := And.intro ha hb
      exact ⟨Max.max Ca Cb, fun ω ↦ abs_min_le_max_abs_abs.trans (max_le_max (ha ω) (hb ω))⟩
  | indicatorLt a b _ _ => exact ⟨1, fun ω ↦ by simp only [Payoff.eval]; split_ifs <;> simp⟩
  | rpow a p ha =>
      obtain ⟨C, hC⟩ := ha
      exact ⟨C ^ (p : ℝ), fun ω ↦ (Real.abs_rpow_le_abs_rpow _ _).trans
        (Real.rpow_le_rpow (abs_nonneg _) (hC ω) p.2)⟩

/-- **A bounded model prices every fixed-date contract.** Against a finite measure and a measurable
model whose every coordinate is bounded, every contract that pays at fixed dates
(`Contract.FixedDated`) has an integrable discounted payoff, so `Contract.value_both` applies to
any two of them with no further hypothesis. A finite-state model such as the binomial tree is
bounded; a lognormal one is not, and there each instrument's integrability is proved on its own
(`Models/BlackScholes/BlackScholes.lean`). A `payAtHit` is excluded: the hitting time of a
measurable process need not be measurable, and an unbounded discount factor evaluated at a random
date need not be integrable. -/
theorem Contract.integrable_pathPV_of_bounded {Q : Measure Ω} [IsFiniteMeasure Q]
    (D : ℝ≥0 → ℝ) {X : ι → ℝ≥0 → Ω → ℝ} (hXm : ∀ i t, Measurable (X i t))
    (hXb : ∀ i t, ∃ C, ∀ ω, |X i t ω| ≤ C) {c : Contract ι} (hc : c.FixedDated) :
    Integrable (fun ω ↦ c.pathPV D (fun i t ↦ X i t ω)) Q := by
  induction c with
  | zero => simp [Contract.pathPV, Contract.cashflows]
  | pay t a =>
      obtain ⟨C, hC⟩ := a.exists_bound_eval hXb
      simp only [Contract.pathPV, Contract.cashflows, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      exact (Integrable.of_bound (a.measurable_eval X hXm).aestronglyMeasurable C
        (.of_forall hC)).const_mul _
  | payAtHit i A a => exact hc.elim
  | both a b ha hb =>
      simp only [Contract.pathPV_both]
      exact (ha hc.1).add (hb hc.2)
  | scale r a ha => simpa only [Contract.pathPV_scale] using (ha hc).const_mul r

end MathFin.Contracts
