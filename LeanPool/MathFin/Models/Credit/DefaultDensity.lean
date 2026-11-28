/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Credit.HazardCurve
public import LeanPool.MathFin.Models.Credit.Cox

/-!
# The default-time density of a deterministic hazard curve

Bagaria ch. 16, Calculation 16.2 (eq. 16.2): the protection leg is
`(1 − R) ∫₀ᵀ P(0,t) λ_t Q(t) dt`, with the remark "`−dQ/dt = λ_t Q(t)`, so this is
the loss integrated against the density of the default time". Survival is (16.1),
`Q(t) = P(τ > t) = exp(−∫₀ᵗ λ_s ds)`, taken with `λ` deterministic as in §16.1.

Here `Q = hazardSurvival h` (`Models/Credit/HazardCurve.lean`) and the density is
`defaultDensity h t = h t · hazardSurvival h t`.

## Calculus layer (no probability)

* `hasDerivAt_hazardSurvival` — `Q' = −λ·Q` at `t`, for `h` locally integrable and
  continuous at `t`.
* `defaultDensity_nonneg` — `λ ≥ 0 ⇒ f ≥ 0`.
* `integral_defaultDensity` — `∫ₐᵇ f = Q(a) − Q(b)` for continuous `h`;
  `integral_defaultDensity_zero` — `∫₀ᵀ f = 1 − Q(T)`.

## Measure-theoretic layer (a true Lebesgue density of `τ`'s law)

For a random time `τ` (a.e.-measurable, finite measure space) whose CDF on `[0, ∞)` is
`P(τ ≤ a) = 1 − Q(a)` — **hypothesized**, the shape of
`MathFin.Cox.cox_cdf_timeVarying` — with `h` continuous and `≥ 0`:

* `map_eq_withDensity` — `Law(τ) = Leb.withDensity (1_{[0,∞)}·f)` (`lawDensity`).
* `integral_comp_eq` — `E[g(τ)] = ∫_{[0,∞)} f·g` for measurable `g`.
* `integral_indicator_Iic_eq` — `E[D(τ)·1{τ ≤ T}] = ∫₀ᵀ D·f`: the (16.2) protection-leg
  kernel as an expectation, for any measurable discount curve `D`.
* `expMeasure_eq_withDensity` — constant-`λ` cross-check: `lawDensity` of the flat curve
  is Mathlib's `expMeasure λ`.

Scope: deterministic, *continuous* hazard (the bootstrapped piecewise-constant curve of
§16.4 is not covered); `τ` is not constructed here, and the stochastic-intensity (Cox
mixing) density is not treated.

## Main definitions

* `defaultDensity`: the default-time density `f(t) = λ(t)·Q(t) = λ(t)·exp(−∫₀ᵗ λ)` of a
  deterministic hazard curve `h`.
* `lawDensity`: the density of the law of `τ` as an `ℝ≥0∞`-valued function, `f` on `[0, ∞)` and
  zero on `(−∞, 0)`.

## Main results

* `hasDerivAt_hazardSurvival`: `−dQ/dt = λ·Q`, for a locally integrable hazard `h` continuous at
  `t`.
* `integral_defaultDensity`, `integral_defaultDensity_zero`: `∫ₐᵇ f = Q(a) − Q(b)` and
  `∫₀ᵀ f = 1 − Q(T)` for a continuous hazard.
* `map_eq_withDensity`: for a continuous nonnegative hazard `h` and an a.e.-measurable `τ` with CDF
  `P(τ ≤ a) = 1 − Q(a)` on `[0, ∞)`, the law of `τ` is `volume.withDensity (lawDensity h)`.
* `integral_comp_eq`: under the same hypotheses, `E[g(τ)] = ∫_{[0,∞)} f(s)·g(s) ds` for
  measurable `g`.
* `integral_indicator_Iic_eq`: under the same hypotheses, `E[D(τ)·1{τ ≤ T}] = ∫₀ᵀ D(s)·λ(s)·Q(s) ds`
  for measurable `D` and `T ≥ 0`.
* `expMeasure_eq_withDensity`: for constant hazard `λ > 0`, `lawDensity` reproduces Mathlib's
  exponential law.

## References

* [S. Bagaria, *Notes on Fixed Income Derivative Pricing*][BagariaFIDP], ch. 16.

## Tags

default density, hazard rate, survival function, protection leg, default time law, CDS pricing,
MSC 91G40, MSC 60E05, JEL G12
-/

@[expose] public section

namespace MathFin.DefaultDensity

open MeasureTheory Real

/-- The **default-time density** `f(t) = λ(t)·Q(t) = λ(t)·exp(−∫₀ᵗ λ)` of a deterministic
hazard curve `h` (Bagaria ch. 16, Calculation 16.2). As a function on all of `ℝ`; the law
of `τ` uses its restriction to `[0, ∞)` (see `map_eq_withDensity`). -/
noncomputable def defaultDensity (h : ℝ → ℝ) (t : ℝ) : ℝ := h t * hazardSurvival h t

/-- **`−dQ/dt = λ·Q`** (Bagaria ch. 16, Calc. 16.2): for a locally integrable hazard `h`
continuous at `t`, the survival curve has derivative `−f(t)` at `t`. FTC for
`∫₀ᵗ h` composed with `exp`. -/
theorem hasDerivAt_hazardSurvival {h : ℝ → ℝ} (hloc : LocallyIntegrable h) {t : ℝ}
    (ht : ContinuousAt h t) :
    HasDerivAt (hazardSurvival h) (-defaultDensity h t) t := by
  have hH : HasDerivAt (cumHazard h) (h t) t :=
    intervalIntegral.integral_hasDerivAt_right
      ((hloc.integrableOn_isCompact isCompact_uIcc).intervalIntegrable)
      (hloc.aestronglyMeasurable.stronglyMeasurableAtFilter) ht
  have h2 : HasDerivAt (fun s ↦ rexp (-cumHazard h s)) (rexp (-cumHazard h t) * -h t) t :=
    hH.neg.exp
  convert h2 using 1
  · rfl
  · simp only [defaultDensity, hazardSurvival, survivalFromIntensity, cumHazard]
    ring

/-- The density is nonnegative under a nonnegative hazard (`Q > 0` always). -/
theorem defaultDensity_nonneg {h : ℝ → ℝ} (hnn : ∀ s, 0 ≤ h s) (t : ℝ) :
    0 ≤ defaultDensity h t :=
  mul_nonneg (hnn t) (hazardSurvival_pos h t).le

/-- The density is continuous for a continuous hazard. -/
theorem continuous_defaultDensity {h : ℝ → ℝ} (hh : Continuous h) :
    Continuous (defaultDensity h) :=
  hh.mul (continuous_iff_continuousAt.2 fun _ ↦
    (hasDerivAt_hazardSurvival hh.locallyIntegrable hh.continuousAt).continuousAt)

/-- **Interval default probability**: `∫ₐᵇ f = Q(a) − Q(b)` for a continuous hazard. -/
theorem integral_defaultDensity {h : ℝ → ℝ} (hh : Continuous h) (a b : ℝ) :
    ∫ s in a..b, defaultDensity h s = hazardSurvival h a - hazardSurvival h b := by
  have hd : ∀ s, HasDerivAt (fun u ↦ -hazardSurvival h u) (defaultDensity h s) s := fun s ↦ by
    have := (hasDerivAt_hazardSurvival hh.locallyIntegrable hh.continuousAt (t := s)).neg
    rw [neg_neg] at this
    exact this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s)
    ((continuous_defaultDensity hh).intervalIntegrable a b)]
  ring

/-- **Default probability by `T`**: `∫₀ᵀ f = 1 − Q(T)` (calculus identity; no `τ`). This is
`MathFin.Cox.defaultDensity_antideriv`, restated through `defaultDensity` and
`hazardSurvival`. -/
theorem integral_defaultDensity_zero {h : ℝ → ℝ} (hh : Continuous h) (T : ℝ) :
    ∫ s in (0:ℝ)..T, defaultDensity h s = 1 - hazardSurvival h T :=
  MathFin.Cox.defaultDensity_antideriv hh T

/-! ### Measure-theoretic layer: `f` is the Lebesgue density of the law of `τ` -/

section Law

open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The density of `τ`'s law as an `ℝ≥0∞`-valued function: `f` on `[0, ∞)`, zero on
`(−∞, 0)`. -/
noncomputable def lawDensity (h : ℝ → ℝ) : ℝ → ℝ≥0∞ :=
  (Set.Ici 0).indicator fun s ↦ ENNReal.ofReal (defaultDensity h s)

/-- `lawDensity h` is measurable for a continuous hazard. -/
theorem measurable_lawDensity {h : ℝ → ℝ} (hh : Continuous h) : Measurable (lawDensity h) :=
  ((continuous_defaultDensity hh).measurable.ennreal_ofReal).indicator measurableSet_Ici

/-- Mass of `(−∞, a]` under `Leb.withDensity (lawDensity h)`, for `a ≥ 0`: `1 − Q(a)`. -/
theorem withDensity_Iic {h : ℝ → ℝ} (hh : Continuous h) (hnn : ∀ s, 0 ≤ h s) {a : ℝ}
    (ha : 0 ≤ a) :
    volume.withDensity (lawDensity h) (Set.Iic a) = ENNReal.ofReal (1 - hazardSurvival h a) := by
  rw [withDensity_apply _ measurableSet_Iic, lawDensity,
    lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    Set.Ici_inter_Iic, ← integral_defaultDensity_zero hh a, intervalIntegral.integral_of_le ha,
    ← integral_Icc_eq_integral_Ioc, ofReal_integral_eq_lintegral_ofReal]
  · exact (continuous_defaultDensity hh).continuousOn.integrableOn_Icc
  · exact Filter.Eventually.of_forall fun s ↦ defaultDensity_nonneg hnn s

/-- `Leb.withDensity (lawDensity h)` puts no mass on `(−∞, a]` for `a < 0`. -/
theorem withDensity_Iic_neg (h : ℝ → ℝ) {a : ℝ} (ha : a < 0) :
    volume.withDensity (lawDensity h) (Set.Iic a) = 0 := by
  rw [withDensity_apply _ measurableSet_Iic, lawDensity,
    lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    Set.Ici_inter_Iic, Set.Icc_eq_empty (by linarith), Measure.restrict_empty,
    lintegral_zero_measure]

/-- **The default-time density, measure-theoretically.** Let `h` be a continuous,
nonnegative hazard curve and `τ` an a.e.-measurable random time on a finite measure space
whose CDF on `[0, ∞)` is `P(τ ≤ a) = 1 − Q(a)` (`Q = hazardSurvival h`). Then the law of
`τ` is absolutely continuous with Lebesgue density `f = λ·Q` on `[0, ∞)` (zero on
`(−∞, 0)`):

  `Law(τ) = Leb.withDensity (1_{[0,∞)} · ofReal (λ·Q))`.

The CDF hypothesis has exactly the shape of the Cox-construction CDF identity
`MathFin.Cox.cox_cdf_timeVarying` (`Models/Credit/Cox.lean`); `τ` is hypothesized,
not constructed, here. -/
theorem map_eq_withDensity [IsFiniteMeasure μ] {h : ℝ → ℝ} (hh : Continuous h)
    (hnn : ∀ s, 0 ≤ h s) {τ : Ω → ℝ} (hτ : AEMeasurable τ μ)
    (hcdf : ∀ a, 0 ≤ a → μ {ω | τ ω ≤ a} = 1 - ENNReal.ofReal (hazardSurvival h a)) :
    μ.map τ = volume.withDensity (lawDensity h) := by
  refine Measure.ext_of_Iic _ _ fun a ↦ ?_
  rw [Measure.map_apply_of_aemeasurable hτ measurableSet_Iic]
  rcases lt_or_ge a 0 with ha | ha
  · rw [withDensity_Iic_neg h ha]
    refine nonpos_iff_eq_zero.mp ?_
    calc μ (τ ⁻¹' Set.Iic a) ≤ μ {ω | τ ω ≤ 0} :=
          measure_mono fun ω (hω : τ ω ≤ a) ↦ show τ ω ≤ 0 by linarith
      _ = 0 := by rw [hcdf 0 le_rfl, hazardSurvival_at_zero, ENNReal.ofReal_one, tsub_self]
  · rw [withDensity_Iic hh hnn ha, show τ ⁻¹' Set.Iic a = {ω | τ ω ≤ a} from rfl, hcdf a ha,
      ENNReal.ofReal_sub _ (hazardSurvival_pos h a).le, ENNReal.ofReal_one]

/-- **Expectations against the default time** (change of variables through the law):
for measurable `g`, `E[g(τ)] = ∫_{[0,∞)} f(s)·g(s) ds` — no integrability needed (both
sides are Bochner integrals, `0` together when non-integrable). -/
theorem integral_comp_eq [IsFiniteMeasure μ] {h : ℝ → ℝ} (hh : Continuous h)
    (hnn : ∀ s, 0 ≤ h s) {τ : Ω → ℝ} (hτ : AEMeasurable τ μ)
    (hcdf : ∀ a, 0 ≤ a → μ {ω | τ ω ≤ a} = 1 - ENNReal.ofReal (hazardSurvival h a))
    {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ ω, g (τ ω) ∂μ = ∫ s in Set.Ici 0, defaultDensity h s * g s := by
  rw [← integral_map hτ hg.aestronglyMeasurable, map_eq_withDensity hh hnn hτ hcdf,
    integral_withDensity_eq_integral_toReal_smul (measurable_lawDensity hh)
      (Filter.Eventually.of_forall fun s ↦ by
        unfold lawDensity; by_cases hs : s ∈ Set.Ici (0:ℝ) <;> simp [hs]),
    ← integral_indicator measurableSet_Ici]
  congr 1
  funext s
  by_cases hs : s ∈ Set.Ici (0:ℝ)
  · simp [lawDensity, hs, ENNReal.toReal_ofReal (defaultDensity_nonneg hnn s)]
  · simp [lawDensity, hs]

/-- **The protection-leg kernel as an expectation** (Bagaria ch. 16, Calc. 16.2 / eq. 16.2,
undiscounted loss `1 − R` factored out): for any measurable discount curve `D` (e.g.
`D t = P(0,t)`) and `T ≥ 0`,

  `E[D(τ)·1{τ ≤ T}] = ∫₀ᵀ D(s)·λ(s)·Q(s) ds`. -/
theorem integral_indicator_Iic_eq [IsFiniteMeasure μ] {h : ℝ → ℝ} (hh : Continuous h)
    (hnn : ∀ s, 0 ≤ h s) {τ : Ω → ℝ} (hτ : AEMeasurable τ μ)
    (hcdf : ∀ a, 0 ≤ a → μ {ω | τ ω ≤ a} = 1 - ENNReal.ofReal (hazardSurvival h a))
    {D : ℝ → ℝ} (hD : Measurable D) {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω, (Set.Iic T).indicator D (τ ω) ∂μ = ∫ s in (0:ℝ)..T, D s * defaultDensity h s := by
  rw [integral_comp_eq hh hnn hτ hcdf (hD.indicator measurableSet_Iic),
    intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc, ← Set.Ici_inter_Iic,
    Set.inter_comm, ← Measure.restrict_restrict measurableSet_Iic,
    ← integral_indicator measurableSet_Iic]
  congr 1
  funext s
  by_cases hs : s ∈ Set.Iic T
  · simp [hs, mul_comm]
  · simp [hs]

/-- **Cross-check against Mathlib's exponential law** (constant hazard `λ > 0`): the
`lawDensity` of the flat curve reproduces `expMeasure λ`, the law that
`MathFin.PoissonInterarrival.map_firstArrival_eq_expMeasure`
(`Probability/Jumps/PoissonInterarrival.lean`) assigns to the first arrival of a rate-`λ` Poisson
process. Obtained from `map_eq_withDensity` with `τ = id`. -/
theorem expMeasure_eq_withDensity {r : ℝ} (hr : 0 < r) :
    ProbabilityTheory.expMeasure r = volume.withDensity (lawDensity fun _ ↦ r) := by
  have := ProbabilityTheory.isProbabilityMeasure_expMeasure hr
  have hS : ∀ a, hazardSurvival (fun _ ↦ r) a = rexp (-(r * a)) := fun a ↦ by
    unfold hazardSurvival survivalFromIntensity
    rw [show cumulativeIntensity (fun _ ↦ r) a = r * a from cumHazard_const r a]
  have := map_eq_withDensity (μ := ProbabilityTheory.expMeasure r) (τ := id) continuous_const
    (fun _ ↦ hr.le) aemeasurable_id fun a ha ↦ by
      rw [show {ω : ℝ | id ω ≤ a} = Set.Iic a from rfl, ← ProbabilityTheory.ofReal_cdf,
        ProbabilityTheory.cdf_expMeasure_eq hr, ite_eq_left ha, hS,
        ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
  rwa [Measure.map_id] at this

end Law

end MathFin.DefaultDensity
