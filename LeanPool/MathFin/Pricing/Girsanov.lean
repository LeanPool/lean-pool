/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.ContinuousMarket
public import LeanPool.MathFin.Probability.Brownian.Girsanov.GirsanovConstantTheta

/-!
# Continuous-time Girsanov for Black–Scholes — the EMM as an explicit change of measure

The equivalent martingale measure of the Black–Scholes model, **constructed** as a
Girsanov density change of the physical measure — not recognised after the fact. Under
the physical measure `P` the stock has drift `μ`,
`S_t = S_0 · exp((μ − σ²/2)t + σ X_t)`, so the discounted price is
`D_t = e^{−rt} S_t = S_0 · exp((μ − r − σ²/2)t + σ X_t)`, a `P`-submartingale (drift
`μ − r ≠ 0`). Tilting by the **Girsanov density** with constant market price of risk
`θ = (μ − r)/σ`,

  `Z_t = exp(−θ X_t − ½θ² t)`   (the Wald exponential at `α = −θ`),
  `Q = P.withDensity Z_T`,

turns the discounted price into a `Q`-**martingale** on `[0, T]`: `Q` is the EMM.

The proof is one line of algebra on top of the constant-θ Girsanov theorem. Since
`μ − r = σθ`, the discounted price is `S_0` times the exponential `Q`-martingale of the
drift-corrected process `B^θ_t = X_t + θt` at `a = σ`:

  `(μ − r − σ²/2)t + σX_t = σ(X_t + θt) − ½σ²t`,

and `expBtheta_isQMartingale` (`GirsanovConstantTheta`) is that exponential's martingale
property under the same `Q`. The constant `S_0` comes out of both integrals.

This wires the **I ↔ II seam** (pricing ↔ Itô/Brownian tower) on the martingale side:
the risk-neutral measure is an explicit density change of the physical one, retiring the
Wald shortcut of `discountedGBM_isMartingale` (which took `Q = P` from the start). The
*distributional* Girsanov (the drift-corrected `B^θ_t = B_t + ∫₀ᵗ θ_s ds` is a `Q`-Brownian
motion, `gir-thm-9.1.8`) is strictly stronger: `GirsanovConstantTheta` for constant `θ`,
`GirsanovAdaptedTheta` for bounded continuous adapted `θ`, and `GirsanovPredictableTheta`
for bounded predictable `θ`.

That is the martingale property as a set-integral identity. `bs_discounted_isEMM` packages it as an
equivalent martingale measure of the model-agnostic frame `IsEMM`, at the horizon
`T` of the density: `Q ≈ P` (the density `exp(−θ X_T − ½θ² T)` is positive and integrates to `1`)
and the discounted price stopped at `T` is a `Q`-martingale. The horizon is part of the statement,
not an artefact: past `T` the discounted price is not a `Q`-martingale, and the frame's forward FTAP
(`ContinuousMarket.isEMM_noArbitrageSimple`) is then about strategies trading up to `T`.

## Main results

* `MathFin.bs_discounted_isQMartingale`
* `MathFin.bs_discounted_isEMM`

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Ch 9
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], Ch 5.2

## Tags

Girsanov theorem, risk-neutral measure, market price of risk, Black–Scholes,
equivalent martingale measure, Doléans exponential, JEL G13, MSC 91G20, MSC 60G44
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- **Black–Scholes EMM via Girsanov.** With physical drift `μ`, rate `r`, volatility
`σ ≠ 0`, and market price of risk `θ = (μ − r)/σ`, the discounted stock price
`D_t = S_0 · exp((μ − r − σ²/2)t + σ X_t)` is a martingale on `[0, T]` under the tilted
measure `Q = P.withDensity (exp(−θ X_T − ½θ² T))`: for `s ≤ t ≤ T` and `A ∈ 𝓕_s`, the
`Q`-integrals of `D_t` and `D_s` over `A` agree. `Q` is the equivalent martingale measure,
exhibited as an explicit Girsanov change of measure. It is `S_0` times
`expBtheta_isQMartingale` at `a = σ`. -/
theorem bs_discounted_isQMartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [IsFilteredPreBrownian X 𝓕 P]
    (S_0 r μ σ : ℝ) (hσ : σ ≠ 0) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, (S_0 * Real.exp ((μ - r - σ ^ 2 / 2) * (t : ℝ) + σ * X t ω))
        ∂(P.withDensity fun ω ↦ ENNReal.ofReal
          (Real.exp (-((μ - r) / σ) * X T ω - ((μ - r) / σ) ^ 2 * (T : ℝ) / 2)))
      = ∫ ω in A, (S_0 * Real.exp ((μ - r - σ ^ 2 / 2) * (s : ℝ) + σ * X s ω))
        ∂(P.withDensity fun ω ↦ ENNReal.ofReal
          (Real.exp (-((μ - r) / σ) * X T ω - ((μ - r) / σ) ^ 2 * (T : ℝ) / 2))) := by
  have hD (u : ℝ≥0) (ω : Ω) : (μ - r - σ ^ 2 / 2) * (u : ℝ) + σ * X u ω
      = σ * (X u ω + (μ - r) / σ * (u : ℝ)) - σ ^ 2 * (u : ℝ) / 2 := by
    field_simp
    ring
  simp only [hD, integral_const_mul]
  rw [expBtheta_isQMartingale ((μ - r) / σ) σ T hst htT hA]

/-- **The Black–Scholes Girsanov measure is an equivalent martingale measure up to `T`.** With
physical drift `μ`, rate `r`, volatility `σ ≠ 0` and market price of risk `θ = (μ − r)/σ`, the
measure `Q = P.withDensity (exp(−θ X_T − ½θ² T))` is equivalent to `P` and makes the discounted
price `D_t = S_0 · exp((μ − r − σ²/2)t + σ X_t)` a `Q`-martingale on `[0, T]`: an `IsEMM` of the
continuous-market frame at the horizon `T`.

The set-integral identity is `bs_discounted_isQMartingale`; what the frame adds is adaptedness,
`Q`-integrability (under `Q` the drift-corrected `X_t + θ t` is `N(0, t)`, so `D_t` is `S_0` times a
Gaussian exponential), and equivalence (`girsanovMeasure_isProbabilityMeasure`, a positive density
of unit mean). -/
theorem bs_discounted_isEMM
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (S_0 r μ σ : ℝ) (hσ : σ ≠ 0) (T : ℝ≥0) :
    IsEMM 𝓕 P
      (fun (t : ℝ≥0) ω ↦ S_0 * Real.exp ((μ - r - σ ^ 2 / 2) * (t : ℝ) + σ * X t ω)) T
      (P.withDensity fun ω ↦ ENNReal.ofReal
        (Real.exp (-((μ - r) / σ) * X T ω - ((μ - r) / σ) ^ 2 * (T : ℝ) / 2))) := by
  set θ : ℝ := (μ - r) / σ with hθ
  have : IsProbabilityMeasure (P.withDensity fun ω ↦ ENNReal.ofReal
      (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))) :=
    girsanovMeasure_isProbabilityMeasure (X := X) (𝓕 := 𝓕) θ T
  have hmeasX (u : ℝ≥0) : Measurable (X u) := ((hX.stronglyAdapted u).mono (𝓕.le u)).measurable
  have hcont (t : ℝ≥0) : Continuous fun x : ℝ ↦ S_0 * Real.exp
      ((μ - r - σ ^ 2 / 2) * (t : ℝ) + σ * x) := by
    fun_prop
  refine ⟨isEquivProbMeasure_withDensity_of_isProbabilityMeasure P
      (Real.measurable_exp.comp (((hmeasX T).const_mul (-θ)).sub_const _)).aemeasurable
      (ae_of_all _ fun _ ↦ Real.exp_pos _) inferInstance,
    ContinuousMarket.martingale_stopped_of_setIntegral_eq
      (fun t _ ↦ (hcont t).comp_stronglyMeasurable (hX.stronglyAdapted t)) (fun t htT ↦ ?_)
      (fun s t hst htT A hA ↦ ?_)⟩
  · -- `D_t = S_0 · exp(σ B^θ_t − ½σ² t)` with `B^θ_t ~ N(0, t)` under `Q`
    have hσθ : σ * θ = μ - r := by rw [hθ]; field_simp
    have hlaw := Btheta_map_eq_gaussianReal (P := P) (X := X) (𝓕 := 𝓕) θ T htT
    have hexp : Integrable (fun x : ℝ ↦ Real.exp (σ * x)) (gaussianReal 0 t) :=
      integrable_exp_mul_gaussianReal σ
    have hg : Integrable (fun x : ℝ ↦ S_0 * Real.exp (σ * x - σ ^ 2 * (t : ℝ) / 2))
        (gaussianReal 0 t) := by
      refine (hexp.const_mul (S_0 * Real.exp (-(σ ^ 2 * (t : ℝ) / 2)))).congr
          (ae_of_all _ fun x ↦ ?_)
      beta_reduce
      rw [show σ * x - σ ^ 2 * (t : ℝ) / 2 = -(σ ^ 2 * (t : ℝ) / 2) + σ * x by ring, Real.exp_add]
      ring
    rw [← hlaw] at hg
    refine ((integrable_map_measure hg.aestronglyMeasurable
      ((hmeasX t).add_const _ |>.aemeasurable)).mp hg).congr (ae_of_all _ fun ω ↦ ?_)
    change S_0 * Real.exp (σ * (X t ω + θ * (t : ℝ)) - σ ^ 2 * (t : ℝ) / 2) = _
    rw [show σ * (X t ω + θ * (t : ℝ)) - σ ^ 2 * (t : ℝ) / 2
      = (μ - r - σ ^ 2 / 2) * (t : ℝ) + σ * X t ω by linear_combination (t : ℝ) * hσθ]
  · exact bs_discounted_isQMartingale S_0 r μ σ hσ T hst htT hA

end MathFin
