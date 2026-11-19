/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.SmoothGradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.Support.Affine
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Smooth-gradient relaxation in intrinsic affine coordinates

The affine-support construction expresses a finite-dimensional probability law on the direction
vector space of the affine span of its support. This module evaluates the smooth-gradient
relaxation in that intrinsic Hilbert space and pulls the result back to the original `L²` space.

This removes energy in directions normal to the affine support.
`Energy.SmoothGradient.Intrinsic.energy`
names this selected construction; identification with the metric-measure energy `2 Ch`
remains a separate theorem, especially for singular laws inside their affine support.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Energy.Euclidean

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

/-- Pull an ambient `L²(μ)` function back along reconstruction from intrinsic affine coordinates.

Because reconstruction preserves the probability law, this is a real linear isometry.
-/
def toIntrinsicL2 (μ : ProbabilityMeasure E) :
    Lp ℝ 2 (μ : Measure E) →ₗᵢ[ℝ]
      Lp ℝ 2 (Probability.intrinsicMeasure μ).toMeasure :=
  Lp.compMeasurePreservingₗᵢ ℝ (Probability.reconstruct μ)
    (Probability.measurePreserving_reconstruct μ)

/-- Pull an intrinsic-coordinate `L²` function back to the original ambient probability space. -/
def toAmbientL2 (μ : ProbabilityMeasure E) :
    Lp ℝ 2 (Probability.intrinsicMeasure μ).toMeasure →ₗᵢ[ℝ]
      Lp ℝ 2 (μ : Measure E) :=
  Lp.compMeasurePreservingₗᵢ ℝ (Probability.intrinsicMap μ)
    (Probability.measurePreserving_intrinsicMap μ)

omit [CompleteSpace E] in
/-- Returning to ambient coordinates after passing to intrinsic coordinates is the identity. -/
@[simp]
theorem toAmbientL2_toIntrinsicL2 (μ : ProbabilityMeasure E)
    (f : Lp ℝ 2 (μ : Measure E)) :
    toAmbientL2 μ (toIntrinsicL2 μ f) = f := by
  change
    Lp.compMeasurePreserving (Probability.intrinsicMap μ)
        (Probability.measurePreserving_intrinsicMap μ)
        (Lp.compMeasurePreserving (Probability.reconstruct μ)
          (Probability.measurePreserving_reconstruct μ) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f
    (Probability.measurePreserving_reconstruct μ)
    (Probability.measurePreserving_intrinsicMap μ)]
  apply Subtype.ext
  change
    f.1.compMeasurePreserving
        (Probability.reconstruct μ ∘ Probability.intrinsicMap μ)
        ((Probability.measurePreserving_reconstruct μ).comp
          (Probability.measurePreserving_intrinsicMap μ)) = f.1
  have hae :
      Probability.reconstruct μ ∘ Probability.intrinsicMap μ =ᵐ[(μ : Measure E)] id := by
    filter_upwards [Probability.reconstruct_intrinsicMap_ae μ] with x hx
    exact hx
  rw [AEEqFun.compMeasurePreserving_congr f.1
    ((Probability.measurePreserving_reconstruct μ).comp
      (Probability.measurePreserving_intrinsicMap μ))
    measurable_id hae]
  · exact AEEqFun.compMeasurePreserving_id f.1

omit [CompleteSpace E] in
/-- Passing back to intrinsic coordinates after ambient reconstruction is the identity. -/
@[simp]
theorem toIntrinsicL2_toAmbientL2 (μ : ProbabilityMeasure E)
    (f : Lp ℝ 2 (Probability.intrinsicMeasure μ).toMeasure) :
    toIntrinsicL2 μ (toAmbientL2 μ f) = f := by
  change
    Lp.compMeasurePreserving (Probability.reconstruct μ)
        (Probability.measurePreserving_reconstruct μ)
        (Lp.compMeasurePreserving (Probability.intrinsicMap μ)
          (Probability.measurePreserving_intrinsicMap μ) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f
    (Probability.measurePreserving_intrinsicMap μ)
    (Probability.measurePreserving_reconstruct μ)]
  apply Subtype.ext
  change
    f.1.compMeasurePreserving
        (Probability.intrinsicMap μ ∘ Probability.reconstruct μ)
        ((Probability.measurePreserving_intrinsicMap μ).comp
          (Probability.measurePreserving_reconstruct μ)) = f.1
  have hae :
      Probability.intrinsicMap μ ∘ Probability.reconstruct μ =ᵐ[
        (Probability.intrinsicMeasure μ : Measure _)] id :=
    Filter.Eventually.of_forall fun v ↦ Probability.intrinsicMap_reconstruct μ v
  rw [AEEqFun.compMeasurePreserving_congr f.1
    ((Probability.measurePreserving_intrinsicMap μ).comp
      (Probability.measurePreserving_reconstruct μ))
    measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1

/-- The original and intrinsic-coordinate real `L²` spaces are linearly isometrically
equivalent. -/
def intrinsicL2Equiv (μ : ProbabilityMeasure E) :
    Lp ℝ 2 (μ : Measure E) ≃ₗᵢ[ℝ]
      Lp ℝ 2 (Probability.intrinsicMeasure μ).toMeasure where
  toFun := toIntrinsicL2 μ
  invFun := toAmbientL2 μ
  left_inv := toAmbientL2_toIntrinsicL2 μ
  right_inv := toIntrinsicL2_toAmbientL2 μ
  map_add' := map_add (toIntrinsicL2 μ)
  map_smul' := map_smul (toIntrinsicL2 μ)
  norm_map' := norm_map (toIntrinsicL2 μ)

omit [CompleteSpace E] in
/-- The forward map of the intrinsic `L²` equivalence is coordinate pullback. -/
@[simp]
theorem intrinsicL2Equiv_apply (μ : ProbabilityMeasure E)
    (f : Lp ℝ 2 (μ : Measure E)) :
    intrinsicL2Equiv μ f = toIntrinsicL2 μ f :=
  rfl

omit [CompleteSpace E] in
/-- The inverse map of the intrinsic `L²` equivalence is ambient pullback. -/
@[simp]
theorem intrinsicL2Equiv_symm_apply (μ : ProbabilityMeasure E)
    (f : Lp ℝ 2 (Probability.intrinsicMeasure μ).toMeasure) :
    (intrinsicL2Equiv μ).symm f = toAmbientL2 μ f :=
  rfl

end FunctionalInequalities.Energy.Euclidean

namespace FunctionalInequalities.Energy.SmoothGradient.Intrinsic

open Euclidean

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

/-- The intrinsic-affine smooth-gradient relaxation, represented on the original `L²(μ)` space.

The functional first moves an `L²(μ)` class isometrically to the direction space of the affine
support, then evaluates the smooth-gradient relaxation of the intrinsic probability law.
-/
def energy (μ : ProbabilityMeasure E) :
    Functional (Lp ℝ 2 (μ : Measure E)) :=
  (Energy.SmoothGradient.relaxation (Probability.intrinsicMeasure μ)).comap (toIntrinsicL2 μ)

omit [CompleteSpace E] in
/-- Unfolding the intrinsic-affine relaxation exposes the isometric pullback. -/
@[simp]
theorem energy_apply (μ : ProbabilityMeasure E)
    (f : Lp ℝ 2 (μ : Measure E)) :
    energy μ f =
      Energy.SmoothGradient.relaxation (Probability.intrinsicMeasure μ) (toIntrinsicL2 μ f) :=
  rfl

end FunctionalInequalities.Energy.SmoothGradient.Intrinsic
