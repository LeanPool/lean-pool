/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Poincare.SmoothTest.Basic
public import LeanPool.KLS.FunctionalInequalities.Poincare.SmoothGradient.Comparison
public import LeanPool.KLS.FunctionalInequalities.Poincare.Relaxation

/-!
# Connecting smooth tests to the selected relaxed constant

These five proved comparisons belong to `lem:legacy-relaxed-poincare-comparison`.
Read them in order: identify the raw test family, compare finite constants with ambient
relaxation, compare extended optima, then use the ambient/intrinsic-affine bridge.

The normalization is always variance at most `C` times the integral of the squared gradient;
there is no factor of two. `SmoothTest.Holds` takes a real constant, so its argument is explicitly
`(C : ℝ)` for `C : NNReal`. Optimal constants stay in `ENNReal`, including infinity.

Source: Blueprint `thm:legacy-relaxed-holds-equivalence` and
`thm:legacy-canonical-constant-comparison`. The historical manuscript's Definition 2.1 supplies
the variance/gradient normalization, as documented in `Poincare.SmoothTest.Basic`; the exact test
domain,
relaxation and coordinate comparisons are local specifications. They apply to every Borel
probability in finite dimension, without second moments, density, log-concavity, or a positive
dimension assumption. They do not identify the locally Lipschitz literature constant.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare.SmoothTest

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : ProbabilityMeasure E)

/-- The concrete smooth-gradient family has exactly the smooth-test fixed-constant inequality.
Source: identical smooth finite-energy tests and `L2.variance_toLp`; no closure theorem is used. -/
theorem holds_iff_preEnergy (C : NNReal) :
    Holds (μ : Measure E) (C : ℝ) ↔
      (TestFamily.ofPreEnergy μ (Energy.SmoothGradient.preEnergy μ)).Holds C := by
  have hvariance (f : Energy.SmoothGradient.Test μ) :
      (L2.variance μ f.toL2 : ℝ) = ProbabilityTheory.variance f.toFun (μ : Measure E) :=
    (L2.coe_variance_eq_pointwise μ f.toL2).trans
      (ProbabilityTheory.variance_congr f.toL2_coeFn)
  constructor
  · intro h
    change ∀ f : Energy.SmoothGradient.Test μ,
      L2.variance μ f.toL2 ≤ C * f.energy
    intro f
    apply NNReal.coe_le_coe.mp
    rw [hvariance, NNReal.coe_mul]
    exact h.variance_le ⟨f.contDiff, f.memLp_two, f.gradient_sq_integrable⟩
  · intro h
    refine ⟨inferInstance, C.2, ?_⟩
    intro f hf
    let t : Energy.SmoothGradient.Test μ :=
      ⟨f, hf.smooth', hf.memLp_two, hf.energy_integrable⟩
    have ht := NNReal.coe_le_coe.mpr (h t)
    change (L2.variance μ t.toL2 : ℝ) ≤ (C * t.energy : NNReal) at ht
    rw [hvariance, NNReal.coe_mul] at ht
    exact ht

/-- Smooth-test and ambient relaxed inequalities have the same valid finite constants.
Source: Blueprint `thm:legacy-relaxed-holds-equivalence` and the abstract pre-energy bridge. -/
theorem holds_iff_ambient (C : NNReal) :
    Holds (μ : Measure E) (C : ℝ) ↔ Poincare.SmoothGradient.Ambient.Holds μ C := by
  exact (holds_iff_preEnergy μ C).trans
    (TestFamily.holds_ofPreEnergy_iff μ (Energy.SmoothGradient.preEnergy μ) C)

/-- The smooth-test infimum equals the ambient relaxed Rayleigh supremum, also at infinity.
Source: equality of the sets of valid finite constants; no attainment assumption is needed. -/
theorem constant_eq_ambient :
    optimalConstant (μ : Measure E) = Poincare.SmoothGradient.Ambient.optimalConstant μ := by
  apply le_antisymm
  · by_cases h : Poincare.SmoothGradient.Ambient.optimalConstant μ = ⊤
    · simp [h]
    · have hcoe := ENNReal.coe_toNNReal h
      have hbound := (Poincare.SmoothGradient.Ambient.holds_iff_constant_le μ _).mpr hcoe.ge
      exact (constant_le ((holds_iff_ambient μ _).mpr hbound)).trans hcoe.le
  · apply le_constant
    intro C hC
    exact (Poincare.SmoothGradient.Ambient.holds_iff_constant_le μ C).mp
      ((holds_iff_ambient μ C).mp hC)

/-- A finite smooth-test bound gives exactly the selected intrinsic-affine inequality.
Source: the preceding fixed-constant equivalence and the ambient/intrinsic-affine comparison. -/
theorem holds_iff_intrinsic (C : NNReal) :
    Holds (μ : Measure E) (C : ℝ) ↔ Poincare.SmoothGradient.Intrinsic.Holds μ C := by
  exact (holds_iff_ambient μ C).trans
    (Poincare.SmoothGradient.Ambient.holds_iff_intrinsic μ C)

/--
The smooth-test and intrinsic smooth-gradient extended optima agree for every finite-dimensional
law.
Source: Blueprint `thm:legacy-canonical-constant-comparison`; literature equivalence is separate. -/
theorem constant_eq_intrinsic :
    optimalConstant (μ : Measure E) = Poincare.SmoothGradient.Intrinsic.optimalConstant μ := by
  exact (constant_eq_ambient μ).trans (Poincare.SmoothGradient.Ambient.constant_eq_intrinsic μ)

end FunctionalInequalities.Poincare.SmoothTest
