/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Poincaré constants: source formula and local test domain

Source: [Definition 2.1 of the historical manuscript](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/01-definitions.tex#L17-L25)
uses `Var_P(f) ≤ C_P E_P ‖∇f‖²` for smooth real-valued `f ∈ L²(P)`. Its
[preceding context](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/01-definitions.tex#L6-L15)
is a Euclidean probability density proportional to `exp (-U)` and its Langevin generator.

This module preserves the numerical normalization while explicitly choosing globally `C∞`,
L² tests with integrable squared canonical Hilbert gradient. This finite-energy Hilbert reading
and the `ENNReal` infimum are local encodings, not a verbatim copy of the source assumptions.
Fixed constants and energies are real-valued; `⊤` means no finite valid constant exists.
The source's identification with the reciprocal spectral gap, and a closed Sobolev-domain
identification, are not established here.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace FunctionalInequalities.Poincare.SmoothTest

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [MeasurableSpace E]


/-- Source: local test-domain encoding of Definition 2.1, linked above.
Global `ContDiff ℝ ∞` and finite canonical-gradient energy are explicit local choices;
the energy field prevents a nonintegrable real integral from being assigned zero. -/
structure Admissible (μ : Measure E) (f : E → ℝ) : Prop where
  smooth' : ContDiff ℝ ∞ f
  memLp_two : MemLp f 2 μ
  energy_integrable : Integrable (fun x ↦ ‖gradient f x‖ ^ 2) μ

/-- Source: the energy formula in Definition 2.1, realized as a real Bochner integral.
There is no factor `1/2`. Its finite-energy use is controlled by
`Admissible.energy_integrable`, since a nonintegrable real Bochner integral is totalized to zero. -/
def energy (μ : Measure E) (f : E → ℝ) : ℝ :=
  ∫ x, ‖gradient f x‖ ^ 2 ∂μ

/-- Source: local consequence of Mathlib's `integral_nonneg` and `sq_nonneg`. -/
theorem energy_nonneg (μ : Measure E) (f : E → ℝ) :
    0 ≤ energy μ f := by
  exact integral_nonneg fun _ ↦ sq_nonneg _

omit [MeasurableSpace E] in
/-- Source: local Hilbert-geometry helper using Mathlib's `toDual_gradient` and the
norm-preserving Riesz map `InnerProductSpace.toDual`. -/
theorem norm_fderiv_eq_norm_gradient (f : E → ℝ) (x : E) :
    ‖fderiv ℝ f x‖ = ‖gradient f x‖ := by
  rw [← toDual_gradient]
  exact (InnerProductSpace.toDual ℝ E).norm_map _

/-- Source: local consequence of `norm_fderiv_eq_norm_gradient` and `integral_congr_ae`.
The energy also equals the integral of the squared Fréchet-derivative operator norm. -/
theorem energy_eq_fderiv (μ : Measure E) (f : E → ℝ) :
    energy μ f = ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    change ‖gradient f x‖ ^ 2 = ‖fderiv ℝ f x‖ ^ 2
    rw [norm_fderiv_eq_norm_gradient]

/--
Source: the inequality in [Definition 2.1](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/01-definitions.tex#L17-L25),
with the local Hilbert test domain `Admissible`. Probability and finite-constant
nonnegativity are explicit; no source-domain or spectral-gap equivalence is asserted. -/
structure Holds (μ : Measure E) (C : ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  constant_nonneg : 0 ≤ C
  /-- Apply the variance bound to a globally smooth L² test with integrable squared
    gradient. The energy is `∫ ‖gradient f‖²`, with no factor `1/2`. -/
  variance_le : ∀ ⦃f : E → ℝ⦄, Admissible μ f → variance f μ ≤ C * energy μ f

namespace Holds

/-- Increasing a valid constant preserves the inequality, since `energy_nonneg` makes
multiplication by the energy monotone. The probability and nonnegativity fields are preserved. -/
theorem mono {μ : Measure E} {C C' : ℝ} (h : Holds μ C) (hCC' : C ≤ C') :
    Holds μ C' := by
  refine ⟨h.probability, h.constant_nonneg.trans hCC', ?_⟩
  intro f hf
  exact (h.variance_le hf).trans
    (mul_le_mul_of_nonneg_right hCC' (Poincare.SmoothTest.energy_nonneg μ f))

end Holds

/-- Source: local extended-infimum encoding of the optimal constant in Definition 2.1.
The infimum ranges over finite `NNReal` constants satisfying the local `Holds`; an empty
set of valid constants gives `⊤`. This definition does not identify a spectral gap. -/
def optimalConstant (μ : Measure E) : ENNReal :=
  ⨅ C : {C : NNReal // Holds μ (C : ℝ)}, (C.1 : ENNReal)

/-- Source: local order consequence of `optimalConstant` and Mathlib's `iInf_le_of_le`.
Every finite valid constant bounds the optimal constant from above. -/
theorem constant_le {μ : Measure E} {C : NNReal}
    (hC : Holds μ (C : ℝ)) :
    optimalConstant μ ≤ (C : ENNReal) := by
  exact iInf_le_of_le ⟨C, hC⟩ le_rfl

/-- Source: local order consequence of `optimalConstant` and Mathlib's `le_iInf`.
A lower bound for every finite valid constant bounds the optimal constant from below. -/
theorem le_constant {μ : Measure E} {L : ENNReal}
    (hL : ∀ C : NNReal, Holds μ (C : ℝ) → L ≤ (C : ENNReal)) :
    L ≤ optimalConstant μ := by
  refine le_iInf fun C ↦ ?_
  exact hL C.1 C.2

/-- Source: local empty-infimum consequence of the definition `optimalConstant`. -/
theorem constant_eq_top_of_no_finite {μ : Measure E}
    (h : ∀ C : NNReal, ¬ Holds μ (C : ℝ)) :
    optimalConstant μ = ⊤ := by
  apply top_unique
  refine le_iInf fun C ↦ ?_
  exact (h C.1 C.2).elim

/-- Source: local consequence of `constant_le` and Mathlib's `ENNReal.coe_ne_top`. -/
theorem constant_ne_top_of_holds {μ : Measure E} {C : NNReal}
    (hC : Holds μ (C : ℝ)) :
    optimalConstant μ ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (constant_le hC)

/-- Source: local combination of `constant_ne_top_of_holds` and
`constant_eq_top_of_no_finite`; infinity means no finite valid `Holds` constant exists. -/
theorem constant_eq_top_iff {μ : Measure E} :
    optimalConstant μ = ⊤ ↔
      ∀ C : NNReal, ¬ Holds μ (C : ℝ) := by
  constructor
  · intro htop C hC
    exact (constant_ne_top_of_holds hC htop).elim
  · exact constant_eq_top_of_no_finite

end FunctionalInequalities.Poincare.SmoothTest
