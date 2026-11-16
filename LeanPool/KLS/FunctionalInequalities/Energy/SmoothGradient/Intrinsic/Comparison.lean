/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Basic
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Comparing ambient and intrinsic smooth-gradient relaxations

These three proved comparisons belong to `lem:ambient-intrinsic-poincare-comparison`.
They implement the proof route of Blueprint `thm:ambient-intrinsic-relaxation-equality`:
restrict a smooth test to the affine support, extend an intrinsic test with no normal variation,
and apply both operations to approximating sequences.

All probabilities on finite-dimensional real Borel Hilbert spaces are allowed, including
singular laws and a zero-dimensional affine support. No second moment or density is required.
Restriction can decrease raw energy; extension can preserve it. Equality is asserted only for
the relaxed functionals on the common ambient `L²` carrier.

The extension uses orthogonal projection onto the affine support. The existing
`Probability.intrinsicMap` uses an arbitrary measurable branch off that support and cannot be
used as a globally smooth extension map.

Source: local coordinate-comparison argument in Blueprint chapter 30, with the existing
`Probability.reconstruct` and `Energy.Euclidean.intrinsicL2Equiv` as its checked geometric inputs.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff

namespace FunctionalInequalities.Energy.SmoothGradient

open Euclidean

universe u

private theorem norm_gradient_comp_le
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    {f : Y → ℝ} {φ : X → Y} (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ)
    (hlip : LipschitzWith 1 φ) (x : X) :
    ‖gradient (f ∘ φ) x‖ ≤ ‖gradient f (φ x)‖ := by
  have hnorm : ‖fderiv ℝ φ x‖ ≤ 1 := norm_fderiv_le_of_lipschitz ℝ hlip
  calc
    ‖gradient (f ∘ φ) x‖ = ‖fderiv ℝ (f ∘ φ) x‖ := by
      rw [← toDual_gradient]
      exact ((toDual ℝ X).norm_map _).symm
    _ ≤ ‖fderiv ℝ f (φ x)‖ := by
      rw [fderiv_comp x (hf.differentiable (by simp) _) (hφ.differentiable (by simp) _)]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by simpa using mul_le_mul_of_nonneg_left hnorm (norm_nonneg (fderiv ℝ f (φ x))))
    _ = ‖gradient f (φ x)‖ := by
      rw [← toDual_gradient]
      exact (toDual ℝ Y).norm_map _

private def pullbackTest
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] [MeasurableSpace Y]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} (f : Test ν)
    (φ : X → Y) (hφ : ContDiff ℝ ∞ φ) (hlip : LipschitzWith 1 φ)
    (hmp : MeasurePreserving φ (μ : Measure X) (ν : Measure Y)) : Test μ where
  toFun := f ∘ φ
  contDiff := f.contDiff.comp hφ
  memLp_two := f.memLp_two.comp_measurePreserving hmp
  gradient_sq_integrable := by
    apply (hmp.integrable_comp_of_integrable f.gradient_sq_integrable).mono'
    · have hc : Continuous (gradient (f ∘ φ)) :=
        (toDual ℝ X).symm.continuous.comp
          ((f.contDiff.comp hφ).continuous_fderiv (by simp))
      exact (hc.norm.pow 2).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_comp_le f.contDiff hφ hlip x) 2

private theorem pullbackTest_energy_le
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] [MeasurableSpace Y]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} (f : Test ν)
    (φ : X → Y) (hφ : ContDiff ℝ ∞ φ) (hlip : LipschitzWith 1 φ)
    (hmp : MeasurePreserving φ (μ : Measure X) (ν : Measure Y)) :
    (pullbackTest f φ hφ hlip hmp).energy ≤ f.energy := by
  apply NNReal.coe_le_coe.mp
  calc
    _ ≤ ∫ x, ‖gradient f (φ x)‖ ^ 2 ∂(μ : Measure X) := by
      apply integral_mono (pullbackTest f φ hφ hlip hmp).gradient_sq_integrable
        (hmp.integrable_comp_of_integrable f.gradient_sq_integrable)
      intro x
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_comp_le f.contDiff hφ hlip x) 2
    _ = _ := by
      have h := integral_map hmp.measurable.aemeasurable
        (hmp.map_eq.symm ▸ f.gradient_sq_integrable.aestronglyMeasurable)
      simpa only [hmp.map_eq, Test.coe_energy] using h.symm

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : ProbabilityMeasure E)

namespace Test

/-- Restriction has the expected `L²` realization and does not increase raw energy.
Source: the tangential-gradient projection argument in the local Blueprint comparison. -/
theorem exists_intrinsic_restriction (f : Energy.SmoothGradient.Test μ) :
    ∃ g : Energy.SmoothGradient.Test (Probability.intrinsicMeasure μ),
      (∀ v, g v = f (Probability.reconstruct μ v)) ∧
      g.toL2 = toIntrinsicL2 μ f.toL2 ∧ g.energy ≤ f.energy := by
  let φ := Probability.reconstruct μ
  have hφ : ContDiff ℝ ∞ φ := φ.toContinuousAffineMap.contDiff
  let g := pullbackTest f φ hφ φ.isometry.lipschitzWith
    (Probability.measurePreserving_reconstruct μ)
  exact ⟨g, fun _ ↦ rfl, rfl,
    pullbackTest_energy_le f φ hφ φ.isometry.lipschitzWith
      (Probability.measurePreserving_reconstruct μ)⟩

end Test

private def projectionCoordinates (x : E) : (Probability.affineSupport μ).direction :=
  (Probability.affineSupport μ).direction.orthogonalProjectionOnto
    (x - Probability.supportPoint μ)

section ProjectionCoordinates

omit [CompleteSpace E] [BorelSpace E]
private theorem projectionCoordinates_reconstruct (v : (Probability.affineSupport μ).direction) :
    projectionCoordinates μ (Probability.reconstruct μ v) = v := by
  change (Probability.affineSupport μ).direction.orthogonalProjectionOnto
    ((v : E) + Probability.supportPoint μ - Probability.supportPoint μ) = v
  simp

private theorem contDiff_projectionCoordinates : ContDiff ℝ ∞ (projectionCoordinates μ) :=
  (Probability.affineSupport μ).direction.orthogonalProjectionOnto.contDiff.comp
    (contDiff_id.sub contDiff_const)

private theorem lipschitz_projectionCoordinates : LipschitzWith 1 (projectionCoordinates μ) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa only [projectionCoordinates, dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right,
    NNReal.coe_one, one_mul] using
    (Probability.affineSupport μ).direction.norm_orthogonalProjectionOnto_apply_le (x - y)

end ProjectionCoordinates

omit [CompleteSpace E] in
private theorem measurePreserving_projectionCoordinates :
    MeasurePreserving (projectionCoordinates μ) (μ : Measure E)
      (Probability.intrinsicMeasure μ : Measure _) := by
  have hae : projectionCoordinates μ =ᵐ[(μ : Measure E)] Probability.intrinsicMap μ := by
    filter_upwards [Probability.reconstruct_intrinsicMap_ae μ] with x hx
    rw [← hx, projectionCoordinates_reconstruct, Probability.intrinsicMap_reconstruct]
  exact ⟨(contDiff_projectionCoordinates μ).continuous.measurable,
    (Measure.map_congr hae).trans (Probability.measurePreserving_intrinsicMap μ).map_eq⟩

namespace Test

/-- An intrinsic test has a smooth ambient extension with exactly the same raw energy.
Source: extension through orthogonal projection in the local Blueprint comparison. -/
theorem exists_ambient_extension
    (g : Energy.SmoothGradient.Test (Probability.intrinsicMeasure μ)) :
    ∃ f : Energy.SmoothGradient.Test μ,
      (∀ v, f (Probability.reconstruct μ v) = g v) ∧
      toIntrinsicL2 μ f.toL2 = g.toL2 ∧ f.energy = g.energy := by
  let f := pullbackTest g (projectionCoordinates μ) (contDiff_projectionCoordinates μ)
    (lipschitz_projectionCoordinates μ) (measurePreserving_projectionCoordinates μ)
  have hpoint : ∀ v, f (Probability.reconstruct μ v) = g v := by
    intro v
    change g (projectionCoordinates μ (Probability.reconstruct μ v)) = g v
    rw [projectionCoordinates_reconstruct]
  obtain ⟨r, hr, hL2, henergy⟩ := f.exists_intrinsic_restriction μ
  have hrg : r = g := by
    have hfun : r.toFun = g.toFun := funext fun v ↦ (hr v).trans (hpoint v)
    cases r
    cases g
    cases hfun
    rfl
  subst r
  exact ⟨f, hpoint, hL2.symm, le_antisymm
    (pullbackTest_energy_le g (projectionCoordinates μ) (contDiff_projectionCoordinates μ)
      (lipschitz_projectionCoordinates μ) (measurePreserving_projectionCoordinates μ)) henergy⟩

end Test

/-- The two extended energies agree on the original `L²(μ)` space, including at infinity.
Source: Blueprint `thm:ambient-intrinsic-relaxation-equality`, using the preceding test maps. -/
theorem relaxation_eq_intrinsic_energy :
    relaxation μ = Intrinsic.energy μ := by
  apply Functional.ext
  intro f
  change (preEnergy μ).sequentialRelaxation f =
    (preEnergy (Probability.intrinsicMeasure μ)).sequentialRelaxation
      (toIntrinsicL2 μ f)
  apply le_antisymm
  · have h := (preEnergy (Probability.intrinsicMeasure μ)).sequentialRelaxation_comp_le
      (preEnergy μ) (toAmbientL2 μ) (toAmbientL2 μ).continuous
      (fun g ↦ by
        obtain ⟨t, _, ht, he⟩ := g.exists_ambient_extension μ
        refine ⟨t, ?_, he.le⟩
        change t.toL2 = toAmbientL2 μ g.toL2
        rw [← ht, toAmbientL2_toIntrinsicL2]) (toIntrinsicL2 μ f)
    simpa only [toAmbientL2_toIntrinsicL2] using h
  · exact (preEnergy μ).sequentialRelaxation_comp_le
      (preEnergy (Probability.intrinsicMeasure μ))
      (toIntrinsicL2 μ) (toIntrinsicL2 μ).continuous
      (fun t ↦ by
        obtain ⟨g, _, hg, he⟩ := t.exists_intrinsic_restriction μ
        exact ⟨g, hg, he⟩) f

end FunctionalInequalities.Energy.SmoothGradient
