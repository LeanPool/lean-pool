/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Smooth-gradient pre-energy on a finite-dimensional real Hilbert space

This module realizes globally `C∞`, square-integrable real functions as elements of
`L²(μ)` and equips them with the finite energy

`    ∫ x, ‖gradient f x‖² ∂μ.`

The measurable structure is required to be Borel and second countable. Its sequential `L²`
relaxation is the intended ambient-Euclidean candidate for the standard canonical energy `2 Ch`.
This definition-only module does not assert density, closedness, or identification with Cheeger
energy; the first two are proved in companion modules. For singular measures, agreement of the
relaxation with every raw ambient-gradient test remains a separate fiber-consistency or core
question, even though the relaxed functional itself is closed quadratic.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace FunctionalInequalities.Energy.SmoothGradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]

/-- A globally `C∞` real `L²(μ)` test with finite canonical gradient energy. -/
structure Test (μ : ProbabilityMeasure E) where
  /-- The real-valued test function. -/
  toFun : E → ℝ
  /-- The test is globally `C∞`.

  In Mathlib's differentiability index, `∞` denotes ordinary infinite differentiability;
  `⊤` is the stronger analytic regularity and is not required here.
  -/
  contDiff : ContDiff ℝ ∞ toFun
  /-- The test defines an element of real `L²(μ)`. -/
  memLp_two : MemLp toFun 2 (μ : Measure E)
  /-- The squared norm of the canonical Hilbert gradient is integrable. -/
  gradient_sq_integrable :
    Integrable (fun x ↦ ‖gradient toFun x‖ ^ 2) (μ : Measure E)

namespace Test

variable {μ : ProbabilityMeasure E}

instance : CoeFun (Test μ) (fun _ ↦ E → ℝ) :=
  ⟨toFun⟩

/-- The squared gradient norm is pointwise nonnegative. -/
theorem gradientSq_nonneg (f : Test μ) (x : E) :
    0 ≤ ‖gradient f.toFun x‖ ^ 2 :=
  sq_nonneg _

/-- The finite real integral underlying the smooth-gradient energy is nonnegative. -/
theorem gradientIntegral_nonneg (f : Test μ) :
    0 ≤ ∫ x, ‖gradient f.toFun x‖ ^ 2 ∂(μ : Measure E) :=
  integral_nonneg f.gradientSq_nonneg

/-- The finite canonical gradient integral, valued in `NNReal`. -/
def energy (f : Test μ) : NNReal :=
  ⟨∫ x, ‖gradient f.toFun x‖ ^ 2 ∂(μ : Measure E), f.gradientIntegral_nonneg⟩

/-- Coercing the finite energy to `ℝ` recovers its defining integral. -/
@[simp, norm_cast]
theorem coe_energy (f : Test μ) :
    (f.energy : ℝ) = ∫ x, ‖gradient f.toFun x‖ ^ 2 ∂(μ : Measure E) :=
  rfl

/-- The `L²(μ)` element represented by a smooth-gradient test. -/
def toL2 (f : Test μ) : Lp ℝ 2 (μ : Measure E) :=
  f.memLp_two.toLp f.toFun

/-- The `L²` realization agrees almost everywhere with the original test function. -/
theorem toL2_coeFn (f : Test μ) :
    f.toL2 =ᵐ[(μ : Measure E)] f.toFun :=
  f.memLp_two.coeFn_toLp

end Test

/-- The finite smooth-gradient pre-energy, realized in real `L²(μ)`. -/
def preEnergy (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E] :
    PreEnergy (Lp ℝ 2 (μ : Measure E)) where
  Test := Test μ
  toAmbient := Test.toL2
  energy := Test.energy

/-- The ambient realization of the smooth-gradient pre-energy is the test's `L²` class. -/
@[simp]
theorem preEnergy_toAmbient (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E]
    (f : Test μ) :
    (preEnergy μ).toAmbient f = f.toL2 :=
  rfl

/-- The smooth-gradient pre-energy is exactly the finite squared-gradient integral. -/
@[simp]
theorem preEnergy_energy (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E]
    (f : Test μ) :
    (preEnergy μ).energy f = f.energy :=
  rfl

/-- The sequential `L²` relaxation of the smooth-gradient pre-energy.

This is the intended candidate for the standard canonical energy `2 Ch`. The equality with
`2 Ch`, and the required smooth-core density statement, are deliberately left as later
theorems rather than built into this name. -/
def relaxation (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E] :
    Functional (Lp ℝ 2 (μ : Measure E)) :=
  (preEnergy μ).sequentialRelaxation

/-- Unfolding the smooth-gradient relaxation exposes the generic sequential relaxation. -/
theorem relaxation_apply (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E]
    (f : Lp ℝ 2 (μ : Measure E)) :
    relaxation μ f =
      (preEnergy μ).sequentialRelaxation f :=
  rfl

end FunctionalInequalities.Energy.SmoothGradient
