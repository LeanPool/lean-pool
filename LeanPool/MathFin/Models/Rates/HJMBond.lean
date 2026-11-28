/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.ShortRate
public import LeanPool.MathFin.Models.Rates.HJM

/-!
# Fixed cash flows in the Heath–Jarrow–Morton model

An `HJM.HJMModel` has a short rate `r(t) = f(t,t)` and so a stochastic discount factor
`D t = exp(-∫₀ᵗ r)`, the inverse of its bank account. `HJMModel.discount` is that factor as
`shortRateDiscount` of the integrated short rate, the object the contracts layer already prices
with (`Contract.value`), and `HJMModel.discount_eq_inv_bankAccount` identifies it with
`(bankAccount)⁻¹`.

A schedule of fixed cash flows sees the model only through the zero curve `𝔼[D tᵢ]`
(`value_fixedFlows_of_zeroCurve_eq`). Two results:

* `value_fixedFlows_hjm`: **conditional on the pricing hypothesis** `𝔼[D tᵢ] = P(0, tᵢ)`,
  where `P(0,·)` is the initial bond curve, assumed deterministic (`hdet`), the schedule is worth
  `∑ P(0, tᵢ) cᵢ`. That hypothesis is what the HJM drift condition delivers (the discounted bonds
  are martingales); it is *not* proved here and is an explicit hypothesis of the statement.
* `value_fixedFlows_hjm_flat`: unconditionally, for a deterministic flat forward curve
  `f(s,u) = r` (`s ≤ u`), the schedule is worth `∑ zcb r 0 tᵢ · cᵢ`.

## Main definitions

* `HJMModel.discount`: the stochastic discount factor `exp(-∫₀ᵗ f(s,s) ds)` of an HJM model.

## Main results

* `HJMModel.discount_eq_inv_bankAccount`: `discount t ω = (bankAccount t ω)⁻¹`.
* `value_fixedFlows_hjm`: fixed flows are worth `∑ P(0,tᵢ) cᵢ` given `𝔼[D tᵢ] = P(0,tᵢ)`.
* `value_fixedFlows_hjm_flat`: on a flat deterministic curve, they are worth `∑ zcb r 0 tᵢ cᵢ`.

## References

* [Heath–Jarrow–Morton, *Bond pricing and the term structure*][HeathJarrowMorton1992], §2
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  sec. 5.1
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]

## Tags

Heath–Jarrow–Morton, stochastic discount factor, zero curve, coupon bond pricing,
contract valuation, MSC 91G30, JEL E43
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathFin.Contracts

open ItoIntegralL2 ItoIntegralCLM HJM

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {hB : IsPreBrownianReal B μ} {hBmeas : ∀ t, Measurable (B t)} {H : ℝ≥0}

/-- **The stochastic discount factor of an HJM model**: `D t = exp(-∫₀ᵗ f(s,s) ds)`, the
`shortRateDiscount` of the integrated short rate. -/
noncomputable def _root_.MathFin.HJM.HJMModel.discount (M : HJMModel μ hB hBmeas H) : ℝ≥0 → Ω → ℝ :=
  shortRateDiscount M.integratedRate

/-- The HJM discount factor is the inverse of the bank account. -/
theorem _root_.MathFin.HJM.HJMModel.discount_eq_inv_bankAccount (M : HJMModel μ hB hBmeas H)
    (t : ℝ≥0) (ω : Ω) :
    M.discount t ω = (M.bankAccount t ω)⁻¹ := by
  rw [HJMModel.discount, shortRateDiscount, HJMModel.bankAccount, Real.exp_neg]

/-- **Fixed cash flows in the HJM model, given the pricing hypothesis.** Let `P` be the initial
bond curve: `P(0, tᵢ) = bond 0 tᵢ` for every outcome (the time-`0` curve is deterministic). If the
discount factor prices each bond at its curve value, `𝔼[D tᵢ] = P(0, tᵢ)` (`hprice`: the
discounted-bond martingale property that the HJM drift condition delivers, which is **not**
proved here), then a schedule paying `cᵢ` at `tᵢ` is worth `∑ P(0, tᵢ) cᵢ`. -/
theorem value_fixedFlows_hjm (M : HJMModel μ hB hBmeas H) (X : ι → ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) {P : ℝ≥0 → ℝ}
    (hdet : ∀ i < n, ∀ ω, M.bond 0 (t i) ω = P (t i))
    (hprice : ∀ i < n, ∫ ω, M.discount (t i) ω ∂μ = P (t i)) :
    (fixedFlows t c n : Contract ι).value μ M.discount X
      = ∑ i ∈ Finset.range n, P (t i) * c i := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  refine value_fixedFlows_of_zeroCurve_eq X t c n hprice fun i hi ↦ ?_
  have h := M.bond_pos 0 (t i) ω₀
  rw [hdet i hi ω₀] at h
  exact h.ne'

/-- **Fixed cash flows on a flat deterministic HJM curve.** If `f(s,u) = r` for all `s ≤ u` and
outcomes, the discount factor is the deterministic `zcb r 0 t = exp(-r t)` and a schedule paying
`cᵢ` at `tᵢ` is worth `∑ zcb r 0 tᵢ · cᵢ`. Unconditional. -/
theorem value_fixedFlows_hjm_flat (M : HJMModel μ hB hBmeas H) {r : ℝ}
    (hflat : ∀ s u ω, s ≤ u → M.fwd s u ω = r) (X : ι → ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0)
    (c : ℕ → ℝ) (n : ℕ) :
    (fixedFlows t c n : Contract ι).value μ M.discount X
      = ∑ i ∈ Finset.range n, zcb r 0 (t i) * c i := by
  have hD (s : ℝ≥0) (ω : Ω) : M.discount s ω = zcb r 0 s := by
    have hint : M.integratedRate s ω = r * (s : ℝ) := by
      rw [HJMModel.integratedRate,
        setIntegral_congr_fun measurableSet_Ioc (f := fun u ↦ M.shortRate u ω) (g := fun _ ↦ r)
          (fun u _ ↦ hflat u u ω le_rfl), setIntegral_const, Measure.real_def, timeMeasure_Ioc,
        ENNReal.toReal_ofReal (by simp), smul_eq_mul, mul_comm]; simp
    rw [HJM.HJMModel.discount, shortRateDiscount, hint, zcb]
    simp
  exact value_fixedFlows_of_zeroCurve_eq (P := fun s ↦ zcb r 0 s) X t c n
    (fun i _ ↦ by simp [zeroCurve, hD]) fun i _ ↦ (zcb_pos r 0 (t i)).ne'

end MathFin.Contracts
