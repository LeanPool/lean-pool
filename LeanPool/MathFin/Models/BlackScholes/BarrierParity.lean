/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.PDE
public import LeanPool.MathFin.Pricing.Value

/-!
# Knock-in / knock-out barrier parity (in–out parity)

A knock-**in** option pays the vanilla payoff `f` only if the underlying path
hits the barrier during the option's life; the matching knock-**out** pays `f`
only if it does *not*. The barrier-hit event `A` and its complement `Aᶜ`
partition every path, so the two discounted expected payoffs add back to the
vanilla price:

`V_in + V_out = V_vanilla`.

This needs **no** barrier density and no running-max law — it is a pure
linearity-of-expectation identity, in the register of
`Models/BlackScholes/ChooserComposition.lean`'s `chooser_integral_decomp`: a pathwise
payoff decomposition (`barrier_payoff_partition`) lifted through the integral.

We first name the present-value functional the library had only ever written
inline — `discountedValue D Q g = D · E_Q[g]` — so the barrier values are thin,
honest specialisations of it and the parity reads as an identity about *values*.

## Main definitions

* `discountedValue`: the discounted risk-neutral value `D · E_Q[g]` of a payoff `g` under the
  measure `Q` and discount factor `D`.
* `knockInValue`: the value of an option that pays `f` only on the barrier-hit event `A`.
* `knockOutValue`: the value of an option that pays `f` only off the barrier-hit event, that is on
  the complement `Aᶜ`.
* `vanillaValue`: the discounted expected payoff `f`, paid on every path.

## Main results

* `discountedValue_eq_contract_value`: `discountedValue` is `Contract.value` of the contract that
  pays the observed variable `g` at time `0`, so the barrier values are values in the contracts
  tower.
* `barrier_payoff_partition`: the pathwise split `𝟙_A·f + 𝟙_{Aᶜ}·f = f`.
* `knockIn_add_knockOut_eq_vanilla`: in–out parity `V_in + V_out = V_vanilla`.
* `knockIn_add_knockOut_eq_bsV`: for a call under the Black–Scholes lognormal hypothesis,
  the knock-in and knock-out values sum to the Black–Scholes price `bsV`, for any measurable
  barrier event. So a closed form for either leg gives the other as `bsV` minus it; no
  closed form for either leg is proved here.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull]
* [E. Reiner and M. Rubinstein, *Breaking down the barriers*][ReinerRubinstein1991]

## Tags

in–out parity, barrier option, knock-in, knock-out, vanilla decomposition, discounted value,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Discounted risk-neutral value** of a payoff `g` under pricing measure `Q`
and discount factor `D`: `D · E_Q[g]`. The present-value functional the pricing
files had been spelling out inline; named here so in–out parity is an identity
about values rather than raw integrals. -/
noncomputable def discountedValue (D : ℝ) (Q : Measure Ω) (g : Ω → ℝ) : ℝ :=
  D * ∫ ω, g ω ∂Q

/-- **`discountedValue` is `Contract.value`.** `D · E_Q[g]` is the value, under the pricing measure
`Q` and the constant discount factor `D`, of the contract that pays the observable `g` at time `0`
(`Contract.pay`, `Payoff.obs`), in the model whose single observable is `g`. The barrier values
below are this with `g` the knock-in, knock-out or vanilla payoff. -/
theorem discountedValue_eq_contract_value (D : ℝ) (Q : Measure Ω) (g : Ω → ℝ) :
    discountedValue D Q g
      = (Contracts.Contract.pay 0 (Contracts.Payoff.obs () 0)).value Q (fun _ _ ↦ D)
          (fun _ _ ↦ g) := by
  simp only [discountedValue, Contracts.Contract.value_pay, Contracts.Payoff.eval,
    Contracts.scenarioAt, integral_const_mul]

/-- **Knock-in value**: the option pays the payoff `f` only on the barrier-hit
event `A`, so its value is the discounted expectation of `𝟙_A · f`. -/
noncomputable def knockInValue (D : ℝ) (Q : Measure Ω) (A : Set Ω) (f : Ω → ℝ) : ℝ :=
  discountedValue D Q (A.indicator f)

/-- **Knock-out value**: the option pays `f` only off the barrier-hit event, i.e.
on the complement `Aᶜ`, so its value is the discounted expectation of
`𝟙_{Aᶜ} · f = (1 − 𝟙_A) · f`. -/
noncomputable def knockOutValue (D : ℝ) (Q : Measure Ω) (A : Set Ω) (f : Ω → ℝ) : ℝ :=
  discountedValue D Q (Aᶜ.indicator f)

/-- **Vanilla value**: the discounted expected payoff `f`, paid on every path. -/
noncomputable def vanillaValue (D : ℝ) (Q : Measure Ω) (f : Ω → ℝ) : ℝ :=
  discountedValue D Q f

/-- **Barrier payoff partition** (pathwise): the knock-in payoff `𝟙_A · f` and the
knock-out payoff `𝟙_{Aᶜ} · f` sum to the vanilla payoff `f` on every path — each
path either hits the barrier (`ω ∈ A`) or does not (`ω ∈ Aᶜ`), and contributes
`f ω` to exactly one leg. -/
theorem barrier_payoff_partition (A : Set Ω) (f : Ω → ℝ) :
    A.indicator f + Aᶜ.indicator f = f :=
  Set.indicator_self_add_compl A f

/-- **In–out barrier parity**: `V_in + V_out = V_vanilla`. The barrier-hit event
`A` and its complement partition the paths (`barrier_payoff_partition`), so the
discounted expected payoffs add to the vanilla price. Pure linearity of the
integral — no barrier density required. -/
theorem knockIn_add_knockOut_eq_vanilla
    (D : ℝ) (Q : Measure Ω) (A : Set Ω) (f : Ω → ℝ)
    (hA : MeasurableSet A) (hf : Integrable f Q) :
    knockInValue D Q A f + knockOutValue D Q A f = vanillaValue D Q f := by
  unfold knockInValue knockOutValue vanillaValue discountedValue
  rw [← mul_add, integral_indicator hA, integral_indicator hA.compl,
    integral_add_compl hA hf]

/-- **In–out parity for a Black–Scholes call.** Under `BSCallHyp`, for any measurable
barrier-hit event `A`, the knock-in and knock-out calls (payoff `max(S_T − K, 0)`, discount
`e^{−rT}`) sum to the Black–Scholes price: `V_in + V_out = bsV K r σ S₀ T`. This is
`knockIn_add_knockOut_eq_vanilla` with the vanilla leg priced by
`integral_bsCall_payoff_eq_bsV`. -/
theorem knockIn_add_knockOut_eq_bsV {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z) {A : Set Ω}
    (hA : MeasurableSet A) :
    knockInValue (Real.exp (-r * T)) Q A (fun ω ↦ max (bsTerminal S_0 r σ T (Z ω) - K) 0) +
        knockOutValue (Real.exp (-r * T)) Q A (fun ω ↦ max (bsTerminal S_0 r σ T (Z ω) - K) 0)
      = bsV K r σ S_0 T := by
  rw [knockIn_add_knockOut_eq_vanilla _ _ _ _ hA
      ((integrable_bsTerminal h.Z_law S_0 r σ T).sub' (integrable_const K)).pos_part,
    vanillaValue, discountedValue, ← integral_const_mul, integral_bsCall_payoff_eq_bsV h]

end MathFin
