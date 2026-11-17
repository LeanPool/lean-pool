/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.Process.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Energy.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Cumulant.Envelope

/-!
# The cutoff-weighted energy claim
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
/--
The cutoff-weighted energy integral `∫₀ᵀ E[γ(p_s)² E_{d+1}(p_s)(u)] ds` (BKL (95)–(97) along the
cutoff process). -/
def weightedEnergyIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : Param n → ℝ)
    (p : ℝ → Ω → Param n) (d : ℕ) (u : EuclideanSpace ℝ (Fin n)) (T : ℝ) : ℝ :=
  ∫ ω,
    ∫ s in Set.Ioc (0 : ℝ) T,
      γ (p s ω) ^ 2 *
        cumulantEnergy
          (compactPosterior μ hc (p s ω).1 (p s ω).2 : Measure (EuclideanSpace ℝ (Fin n))) d
          u ∂volume ∂P

/--
**BKL (95) in cutoff form** at order `m = d + 1 ≥ 2` with envelope `b_m = envelope K m`: for every
compactly
supported isotropic log-concave prior, unit vector `u`, tolerance `ε > 0` and horizon `T`, for every
large enough cutoff
radius `R` and every ball-cutoff Eldan process on any Brownian setup,
`E_m(0) + ½ ∫₀ᵀ E[γ_R² E_{m+1}(p_s)] ds ≤ b_m + ε`. -/
def CutoffEnergyClaim (K : ℝ) (d : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support),
    KLS.Isotropic μ → KLS.LogConcave μ → ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 →
    ∀ ε : ℝ, 0 < ε → ∀ T : ℝ, 0 ≤ T → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (W : MultidimBrownianMotion P n) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
        (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ),
        (∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t) →
        (∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) →
        ∀ {p : ℝ → Ω → Param n}, IsEldanCutoff μ hc W ℱ hW (ballCutoff R) p →
          cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) d u +
              (1 / 2 : ℝ) * weightedEnergyIntegral μ hc P (ballCutoff R) p (d + 1) u T ≤
            envelope K (d + 1) + ε


end FunctionalInequalities.KLS.BKL.Localization
