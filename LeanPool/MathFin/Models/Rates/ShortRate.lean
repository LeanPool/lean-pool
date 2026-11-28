/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.Value
public import LeanPool.MathFin.Models.Rates.HullWhiteCalibration
public import LeanPool.MathFin.Models.Rates.GSRPiecewiseVol

/-!
# Stochastic discounting, and contracts in the Gaussian short-rate models

In a short-rate model the discount factor is a random variable at each time,
`D t = exp(−∫₀ᵗ r_s ds)` (`shortRateDiscount`), and `Contract.value Q D X c` values a contract
along each outcome by that outcome's discount path.

A schedule of fixed cash flows sees only the model's zero curve `P(0, t) = 𝔼_Q[D t]`
(`zeroCurve`, `Pricing/Value.lean`): its value under the stochastic discount factor is its value
on that curve (`value_fixedFlows_eq_zeroCurve`), given each `D tᵢ` integrable. The Gaussian
short-rate models give the curve in closed form, and the integrability comes with it, since a
function whose integral is nonzero is integrable (`value_fixedFlows_of_zeroCurve_eq`). So a
coupon bond is worth `∑ cᵢ P(0, tᵢ)` with

* Vasicek: `P(0, t) = A(t) e^{−B(t) r₀}` (`value_fixedFlows_vasicek`, from
  `vasicekBondPrice_affine`);
* Hull–White with continuous forcing `θ`: the same `B`, and `A` carrying `θ`
  (`value_fixedFlows_hullWhite`, from `HullWhite.bondPrice_affine`);
* two-piece GSR, for payment dates after the volatility switch `T*`:
  `P(0, t) = exp(−M(t) + V(t)/2)` with the GSR variance (`value_fixedFlows_gsr`, from
  `gsrBondPrice_eq`).

In each, the measure is read as the pricing measure: no change of measure is built, as in the
bond-price theorems the instances consume. Contracts whose cash flows depend on the rate, such as
a floating leg paying the rate it observes, are not covered by these closed forms: valuing one
needs the bond prices `P(t, T)` at `t > 0`, the conditional expectation `bondPrice`
(`Models/Rates/Caplet.lean`). For the Vasicek, Hull–White and two-piece GSR models they are in
closed form (`bondPrice_vasicek`, `bondPrice_hullWhite`, `bondPrice_gsr`,
`Models/Rates/VasicekBond.lean`, `Models/Rates/HullWhiteBond.lean`,
`Models/Rates/GSRBond.lean`), and the bond put and caplet follow
(`Models/Rates/Jamshidian.lean`).

## Main definitions

* `shortRateDiscount` — `D t = exp(−R t)` from an integrated short rate `R`.

## Main results

* `value_fixedFlows_vasicek`, `value_fixedFlows_hullWhite`, `value_fixedFlows_gsr`.

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

* [Andersen and Piterbarg, *Interest Rate Modeling*][AndersenPiterbarg2010], ch. 10
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  sec. 1.2; sec. 3.2.1; sec. 3.3
* [J. Hull and A. White, *Pricing interest-rate-derivative securities*][HullWhite1990]
* [O. Vasicek, *An equilibrium characterization of the term structure*][Vasicek1977]

## Tags

stochastic discount factor, zero curve, coupon bond pricing, Vasicek model, Hull–White model,
Gaussian short rate, contract valuation, MSC 91G30, MSC 91G20, JEL E43
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Short-rate discounting -/

/-- The discount factor of a short-rate model, `D t = exp(−R t)`, from its integrated short rate
`R t = ∫₀ᵗ r_s ds`. -/
noncomputable def shortRateDiscount (R : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ Real.exp (-R t ω)

/-! ### The Gaussian short-rate models -/

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- **A coupon bond in the Vasicek model**: discounted by `exp(−∫₀ᵗ r)` along the Vasicek short
rate from `r₀`, the schedule paying `cᵢ` at `tᵢ` is worth `∑ A(tᵢ) e^{−B(tᵢ) r₀} cᵢ`, the
affine bond prices of `vasicekBondPrice_affine`, with `μ` read as the pricing measure. -/
theorem value_fixedFlows_vasicek (hB : IsPreBrownianReal B μ) (r₀ θ σ : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (X : ι → ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) :
    (fixedFlows t c n : Contract ι).value μ
        (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) X
      = ∑ i ∈ Finset.range n,
          vasicekBondA θ σ κ (t i) * Real.exp (-(vasicekBondB κ (t i) * r₀)) * c i :=
  value_fixedFlows_of_zeroCurve_eq (P := fun s ↦
      vasicekBondA θ σ κ s * Real.exp (-(vasicekBondB κ s * r₀))) X t c n
    (fun i _ ↦ vasicekBondPrice_affine hB r₀ θ σ hκ (t i))
    fun _ _ ↦ (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne'

/-- **A coupon bond in the Hull–White model**: for continuous forcing `θ`, the schedule paying
`cᵢ` at `tᵢ` is worth `∑ A(tᵢ) e^{−B(tᵢ) r₀} cᵢ`, with Vasicek's `B` and `A = HullWhite.bondA`
carrying `θ` (`HullWhite.bondPrice_affine`), with `μ` read as the pricing measure. -/
theorem value_fixedFlows_hullWhite (hB : IsPreBrownianReal B μ) {θ : ℝ → ℝ}
    (hθ : Continuous θ) (κ σ r₀ : ℝ) (hκ : 0 < κ) (X : ι → ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0)
    (c : ℕ → ℝ) (n : ℕ) :
    (fixedFlows t c n : Contract ι).value μ
        (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) X
      = ∑ i ∈ Finset.range n,
          HullWhite.bondA θ σ κ (t i) * Real.exp (-(vasicekBondB κ (t i) * r₀)) * c i :=
  value_fixedFlows_of_zeroCurve_eq (P := fun s ↦
      HullWhite.bondA θ σ κ s * Real.exp (-(vasicekBondB κ s * r₀))) X t c n
    (fun i _ ↦ HullWhite.bondPrice_affine hB θ κ σ r₀ hθ hκ (t i))
    fun _ _ ↦ (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne'

/-- **A coupon bond in the two-piece GSR model**: with volatility `σ₁` before `T*` and `σ₂`
after, the schedule paying `cᵢ` at dates `tᵢ ≥ T*` is worth `∑ exp(−M(tᵢ) + V(tᵢ)/2) cᵢ`, with
`M` the Vasicek integrated mean and `V = gsrBondV` (`gsrBondPrice_eq`), with `μ` read as the
pricing measure. -/
theorem value_fixedFlows_gsr (hB : IsPreBrownianReal B μ) (r₀ θ σ1 σ2 : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (Tstar : ℝ≥0) (X : ι → ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ)
    (ht : ∀ i < n, Tstar ≤ t i) :
    (fixedFlows t c n : Contract ι).value μ
        (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) X
      = ∑ i ∈ Finset.range n, Real.exp (-(vasicekIntegratedMean r₀ θ κ (t i))
          + gsrBondV κ σ1 σ2 (Tstar : ℝ) (t i) / 2) * c i :=
  value_fixedFlows_of_zeroCurve_eq (P := fun s ↦ Real.exp (-(vasicekIntegratedMean r₀ θ κ s)
      + gsrBondV κ σ1 σ2 (Tstar : ℝ) s / 2)) X t c n
    (fun i hi ↦ gsrBondPrice_eq hB r₀ θ σ1 σ2 hκ Tstar (t i) (ht i hi))
    fun _ _ ↦ (Real.exp_pos _).ne'

end MathFin.Contracts
