/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardGlobal
public import LeanPool.KLS.LevyStochCalc.Ito.VectorItoVersionLimit
public import LeanPool.KLS.LevyStochCalc.Ito.ItoFormulaUnbounded
public import LeanPool.KLS.LevyStochCalc.Brownian.AugmentedFiltration
public import LeanPool.KLS.LevyStochCalc.Brownian.MultidimFiltered
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoL2CompletionMaster
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoFinsetSum
public import LeanPool.KLS.LevyStochCalc.Probability.DoobContinuous
public import LeanPool.KLS.LevyStochCalc.Poisson.Filtered

/-!
# Brownian setup and diffusions with Itô representation

The usual augmentation of the right-continuous natural filtration of a multidimensional Brownian
motion
(vendored LevyStochCalc API) and `IsDiffusion`: an everywhere continuous adapted version `Y` of
`x₀ + ∫₀ᵗ b(Y_s) ds + Σ_k ∫₀ᵗ σ_k(Y_s) dW^k_s` with coefficients evaluated along `Y`. This is the
first
project module importing the vendored stochastic calculus (formalization/vendor/README.md); only
vendored
declarations with standard logical axioms are used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace FunctionalInequalities.Probability.Diffusion

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
  LevyStochCalc.Brownian.Ito

section Usual

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The augmented right-continuous natural filtration of the multidimensional Brownian motion. -/
noncomputable def usualFiltration (W : MultidimBrownianMotion P d) :
    Filtration ℝ ‹MeasurableSpace Ω› :=
  augFiltration W.naturalFiltration.rightCont P

theorem usualFiltration_brownian (W : MultidimBrownianMotion P d) (k : Fin d) :
    IsBrownianFiltration (W.W k) (usualFiltration W) :=
  isBrownianFiltration_augFiltration (W.isBrownianFiltration_natural k).rightCont

instance (W : MultidimBrownianMotion P d) : (usualFiltration W).IsRightContinuous :=
  isRightContinuous_augFiltration W.naturalFiltration P

theorem usualFiltration_le_of_nonpos (W : MultidimBrownianMotion P d) (t : ℝ) (ht : t ≤ 0) :
    usualFiltration W 0 ≤ usualFiltration W t :=
  le_of_eq (augFiltration_of_nonpos W.naturalFiltration.rightCont P ht).symm

theorem usualFiltration_null (W : MultidimBrownianMotion P d) (s : Set Ω)
    (hs : MeasurableSet s) (h0 : P s = 0) : MeasurableSet[usualFiltration W 0] s :=
  measurableSet_augFiltration_of_null W.naturalFiltration.rightCont P hs h0

end Usual

section Diffusion

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {N d : ℕ}

/-- `Y` is an everywhere-continuous adapted version of
`x₀ + ∫₀ᵗ b(Y_s) ds + Σ_k ∫₀ᵗ σ_k(Y_s) dW^k_s`, coefficients evaluated along `Y` itself. -/
def IsDiffusion (W : MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ)
    (b : (Fin N → ℝ) → Fin N → ℝ) (σ : (Fin N → ℝ) → Fin d → Fin N → ℝ) (x₀ : Fin N → ℝ)
    (Y : ℝ → Ω → Fin N → ℝ) : Prop :=
  ∃ (hm : ∀ i k, Measurable (Function.uncurry fun ω s => σ (Y s ω) k i))
    (hp : ∀ i k, Probability.ProgressivelyMeasurable ℱ fun ω s => σ (Y s ω) k i)
    (hq : ∀ i k (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖σ (Y s ω) k i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
    IsVectorItoVersion W ℱ hW (fun i k ω s => σ (Y s ω) k i) hm hp hq
      (fun _ => x₀) (fun i ω s => b (Y s ω) i) Y

end Diffusion

end FunctionalInequalities.Probability.Diffusion
