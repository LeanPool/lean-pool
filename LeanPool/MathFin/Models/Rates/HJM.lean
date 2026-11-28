/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.ZCB
public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralProcessGeneral

/-!
# The Heath–Jarrow–Morton model bundle

The HJM model describes the whole forward-rate curve `f(t,T)`, `t ≤ T`, as a family of Itô
processes in `t`, one for each fixed maturity `T`:
`f(t,T) = f(0,T) + ∫₀ᵗ α(s,T) ds + ∫₀ᵗ σ(s,T) dB_s`, driven by the Brownian motion `B` on
`[0,H]`. `HJMModel` is that data. The stochastic integral is the library's `itoProcessCLM` of the
`L²(trim_H)` realization `volLp T` of the volatility `σ(·,T)`, so the dynamics hold as an identity
of `L²(μ)` classes at each `t ≤ min T H`, and the drift is the pathwise `timeMeasure` integral
(as `driftPath`).

The objects every later node of the HJM program consumes are defined from the bundle: the bond
`P(t,T) = exp(-∫_t^T f(t,u) du)`, the short rate `r(t) = f(t,t)`, the bank account
`B(t) = exp(∫₀ᵗ r)`, the discounted bond `P/B`, and the integrated coefficients
`α*(t,T) = ∫_t^T α(t,u) du`, `σ*(t,T) = ∫_t^T σ(t,u) du`. Only well-definedness is proved here
(`P(T,T) = 1`, positivity of `P` and `B`), and the seam into the library's constant-rate bond:
on a flat curve `f(t,·) ≡ r` the HJM bond is `zcb r t T`.

No dynamics of `P`, no drift condition and no stochastic Fubini interchange is proved in this file.

## Main definitions

* `HJMModel`: the bundle (forward curve, drift, volatility, the `L²` realization of the volatility,
  the Itô dynamics in `t` for each maturity, adaptedness, measurability, integrability of the
  curve and of the short rate).
* `HJMModel.bond`, `HJMModel.shortRate`, `HJMModel.integratedRate`,
  `HJMModel.bankAccount`, `HJMModel.discountedBond`,
  `HJMModel.starDrift`, `HJMModel.starVol`: the derived objects.

## Main results

* `HJMModel.bond_self`: `P(T,T) = 1`.
* `HJMModel.bond_pos`, `HJMModel.bankAccount_pos`, `HJMModel.discountedBond_pos`: positivity.
* `HJMModel.bond_of_flat`: on a flat forward curve `f(t,·) ≡ r` the bond is `zcb r t T`.

## References

* [Heath–Jarrow–Morton, *Bond pricing and the term structure*][HeathJarrowMorton1992], §2
* [D. Brigo, F. Mercurio, *Interest Rate Models*][BrigoMercurio2006], §5.1

## Tags

Heath–Jarrow–Morton, forward rate curve, term structure, zero-coupon bond, short rate,
bank account, JEL E43, MSC 91G30
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathFin
namespace HJM

open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral

/-- **The HJM model bundle** on the horizon `[0,H]` over a Brownian motion `B`.
`fwd t T ω = f(t,T)(ω)`, `drift s T = α(s,T)`, `vol s T = σ(s,T)`; `volLp T` is the `L²(trim_H)`
class of `σ(·,T)` (the Itô-integrable realization), and `fwd_ito` is the dynamics
`f(t,T) = f(0,T) + ∫₀ᵗ α(s,T) ds + ∫₀ᵗ σ(s,T) dB_s` a.s., for `t ≤ T` and `t ≤ H`. -/
structure HJMModel {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0) where
  /-- The forward-rate curve `f(t,T)`. -/
  fwd : ℝ≥0 → ℝ≥0 → Ω → ℝ
  /-- The forward-rate drift `α(s,T)`. -/
  drift : ℝ≥0 → ℝ≥0 → Ω → ℝ
  /-- The forward-rate volatility `σ(s,T)`. -/
  vol : ℝ≥0 → ℝ≥0 → Ω → ℝ
  /-- The `L²(trim_H)` realization of the volatility `σ(·,T)` of maturity `T`. -/
  volLp : ℝ≥0 → Lp ℝ 2 (trimMeasure (μ := μ) H hBmeas)
  volLp_ae : ∀ T, ⇑(volLp T) =ᵐ[trimMeasure (μ := μ) H hBmeas] fun z ↦ vol z.1 T z.2
  /-- `f(·,T)` is an Itô process: initial value, drift integral and Itô integral. -/
  fwd_ito : ∀ T t, t ≤ T → t ≤ H → fwd t T =ᵐ[μ] fun ω ↦
    fwd 0 T ω + ∫ s in Set.Ioc 0 t, drift s T ω ∂timeMeasure +
      itoProcessCLM hB H t hBmeas (volLp T) ω
  fwd_adapted : ∀ t T,
    StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (fwd t T)
  drift_meas : ∀ ω, Measurable fun p : ℝ≥0 × ℝ≥0 ↦ drift p.1 p.2 ω
  vol_meas : ∀ ω, Measurable fun p : ℝ≥0 × ℝ≥0 ↦ vol p.1 p.2 ω
  drift_integrable : ∀ T ω, IntegrableOn (fun s ↦ drift s T ω) (Set.Ioc 0 H) timeMeasure
  fwd_integrable : ∀ t ω, IntegrableOn (fun u ↦ fwd t u ω) (Set.Ioc t H) timeMeasure
  /-- The short rate `f(s,s)` is integrable on the horizon, so the bank account is not a junk
  `exp 0`. -/
  shortRate_integrable : ∀ ω, IntegrableOn (fun s ↦ fwd s s ω) (Set.Ioc 0 H) timeMeasure

namespace HJMModel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {hB : IsPreBrownianReal B μ} {hBmeas : ∀ t, Measurable (B t)} {H : ℝ≥0}
  (M : HJMModel μ hB hBmeas H)

/-- **The bond price** `P(t,T) = exp(-∫_t^T f(t,u) du)`. -/
noncomputable def bond (t T : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-∫ u in Set.Ioc t T, M.fwd t u ω ∂timeMeasure)

/-- **The short rate** `r(t) = f(t,t)`. -/
def shortRate (t : ℝ≥0) (ω : Ω) : ℝ := M.fwd t t ω

/-- **The integrated short rate** `∫₀ᵗ r(s) ds`. -/
noncomputable def integratedRate (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Set.Ioc 0 t, M.shortRate s ω ∂timeMeasure

/-- **The bank account** `B(t) = exp(∫₀ᵗ r(s) ds)`. -/
noncomputable def bankAccount (t : ℝ≥0) (ω : Ω) : ℝ := Real.exp (M.integratedRate t ω)

/-- **The discounted bond** `Z(t,T) = P(t,T) / B(t)`. -/
noncomputable def discountedBond (t T : ℝ≥0) (ω : Ω) : ℝ := M.bond t T ω / M.bankAccount t ω

/-- **The integrated drift** `α*(t,T) = ∫_t^T α(t,u) du`. -/
noncomputable def starDrift (t T : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ u in Set.Ioc t T, M.drift t u ω ∂timeMeasure

/-- **The integrated volatility** `σ*(t,T) = ∫_t^T σ(t,u) du`. -/
noncomputable def starVol (t T : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ u in Set.Ioc t T, M.vol t u ω ∂timeMeasure

/-- A bond is worth one at its own maturity: `P(T,T) = 1`. -/
@[simp] lemma bond_self (T : ℝ≥0) (ω : Ω) : M.bond T T ω = 1 := by
  simp [bond]

lemma bond_pos (t T : ℝ≥0) (ω : Ω) : 0 < M.bond t T ω := Real.exp_pos _

lemma bankAccount_pos (t : ℝ≥0) (ω : Ω) : 0 < M.bankAccount t ω := Real.exp_pos _

/-- The bank account starts at one. -/
@[simp] lemma bankAccount_zero (ω : Ω) : M.bankAccount 0 ω = 1 := by
  simp [bankAccount, integratedRate]

lemma discountedBond_pos (t T : ℝ≥0) (ω : Ω) : 0 < M.discountedBond t T ω :=
  div_pos (M.bond_pos t T ω) (M.bankAccount_pos t ω)

/-- **On a flat forward curve the HJM bond is the constant-rate bond.** If `f(t,u) = r` for
`u ∈ (t,T]`, then `P(t,T) = zcb r t T = exp(-r (T - t))`. -/
theorem bond_of_flat {r : ℝ} {t T : ℝ≥0} (ht : t ≤ T) {ω : Ω}
    (h : ∀ u ∈ Set.Ioc t T, M.fwd t u ω = r) : M.bond t T ω = zcb r t T := by
  have hint : ∫ u in Set.Ioc t T, M.fwd t u ω ∂timeMeasure = r * ((T : ℝ) - t) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ ↦ r) h, setIntegral_const,
      Measure.real_def, timeMeasure_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.2 (NNReal.coe_le_coe.2 ht)), smul_eq_mul, mul_comm]
  rw [bond, hint, zcb]

end HJMModel

end HJM
end MathFin
