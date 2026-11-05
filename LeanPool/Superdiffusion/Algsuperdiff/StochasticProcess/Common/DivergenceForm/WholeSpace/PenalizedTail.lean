/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.Tail
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PenalizedMinimal
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.PointwiseDecay

/-!
# PenalizedTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Tail preparation for the exterior-penalized exhaustion

The chosen zero-trace Sobolev representative of a local penalized resolvent
is connected here to the scalar equation consumed by the normalized Agmon
tail estimate.  The data are allowed to vanish off the penalized cube; no
claim is made for general far-field data.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open MarkovProcess.Semigroup
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- A fixed `H¹₀` representative of a local exterior-penalized
resolvent. -/
def penalizedCubeResolventH10 {V : Set (Vec d)} (hV : IsOpen V)
    (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    H10Function (wholeSpaceCube d m) :=
  Classical.choose (ZeroTraceSobolev.exists_h10Function
    (isOpenBoundedConvexDomain_wholeSpaceCube d m)
    (potentialSolution A.a mu.property A.hnu (A.cubeEllipticity m)
      (wholeSpacePenalizationPotential V n)
      (wholeSpacePenalizationPotential_isBounded hV n m)
      (boundedMeasurableToScalarL2
        (isOpenBoundedConvexDomain_wholeSpaceCube d m)
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y))))

/-- The chosen representative has the local potential-resolvent value
class. -/
theorem penalizedCubeResolventH10_value {V : Set (Vec d)} (hV : IsOpen V)
    (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    (A.penalizedCubeResolventH10 hV n mu hf hfD m).toH1Function.toScalarL2 =
      potentialResolvent A.a mu.property A.hnu (A.cubeEllipticity m)
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m)
        (boundedMeasurableToScalarL2
          (isOpenBoundedConvexDomain_wholeSpaceCube d m)
          (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)) := by
  simpa only [potentialResolvent_apply] using!
    (Classical.choose_spec (ZeroTraceSobolev.exists_h10Function
      (isOpenBoundedConvexDomain_wholeSpaceCube d m)
      (potentialSolution A.a mu.property A.hnu (A.cubeEllipticity m)
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m)
        (boundedMeasurableToScalarL2
          (isOpenBoundedConvexDomain_wholeSpaceCube d m)
          (hf.comp measurable_subtype_coe) (fun y ↦ hfD y))))).1

/-- The chosen representative solves the scalar equation with the potential
term moved to the forcing side. -/
theorem penalizedCubeResolventH10_isScalarForcedWeakSolution
    {V : Set (Vec d)} (hV : IsOpen V) (n : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
    let F := boundedMeasurableToScalarL2 hU
      (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)
    IsScalarForcedWeakSolution A.a (wholeSpaceCube d m)
      (fun y ↦ F y - ((mu : ℝ) + wholeSpacePenalizationPotential V n y) *
        (A.penalizedCubeResolventH10 hV n mu hf hfD m).toH1Function.toFun y)
      (A.penalizedCubeResolventH10 hV n mu hf hfD m).toH1Function := by
  dsimp only
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let F : ScalarL2 (wholeSpaceCube d m) :=
    boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
      (fun y ↦ hfD y)
  let z := A.penalizedCubeResolventH10 hV n mu hf hfD m
  have hzclass : ZeroTraceSobolev.ofH10Function z =
      potentialSolution A.a mu.property A.hnu (A.cubeEllipticity m)
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m) F := by
    apply ZeroTraceSobolev.ext
    · simpa only [ZeroTraceSobolev.toL2_ofH10Function, z, F, hU] using!
        A.penalizedCubeResolventH10_value hV n mu hf hfD m
    · exact (Classical.choose_spec (ZeroTraceSobolev.exists_h10Function hU
        (potentialSolution A.a mu.property A.hnu (A.cubeEllipticity m)
          (wholeSpacePenalizationPotential V n)
          (wholeSpacePenalizationPotential_isBounded hV n m) F))).2
  apply isScalarForcedWeakSolution_of_isPotentialWeakSolution z
    (wholeSpacePenalizationPotential_isBounded hV n m)
  rw [hzclass]
  exact potentialSolution_isPotentialWeakSolution A.a mu.property A.hnu
    (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
    (wholeSpacePenalizationPotential_isBounded hV n m) F

/-- The chosen representative inherits the potential maximum-principle
bound. -/
theorem penalizedCubeResolventH10_abs_le {V : Set (Vec d)} (hV : IsOpen V)
    (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
    {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d m),
      |(A.penalizedCubeResolventH10 hV n mu hf hfD m).toH1Function.toFun y| ≤
        D / (mu : ℝ) := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let F : ScalarL2 (wholeSpaceCube d m) :=
    boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
      (fun y ↦ hfD y)
  let z := A.penalizedCubeResolventH10 hV n mu hf hfD m
  have hFbound : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d m), |F y| ≤ D := by
    simpa only [F, abs_of_nonneg hD] using
      (abs_boundedMeasurableToScalarL2_le hU
        (hf.comp measurable_subtype_coe) (fun y ↦ hfD y))
  have hbound := abs_alpha_mul_potentialResolvent_le_ae A.a hU mu.property
    A.hnu (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
    (wholeSpacePenalizationPotential_isBounded hV n m) F D hD hFbound
  filter_upwards [hbound, z.toH1Function.coeFn_toScalarL2] with y hy hz
  have hvalue : z.toH1Function.toScalarL2 y =
      (potentialResolvent A.a mu.property A.hnu (A.cubeEllipticity m)
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m) F) y := by
    simpa only [z, F, hU] using congrArg
      (fun w : ScalarL2 (wholeSpaceCube d m) ↦ w y)
      (A.penalizedCubeResolventH10_value hV n mu hf hfD m)
  have hscaled : |(mu : ℝ) * z.toH1Function.toFun y| ≤ D := by
    rw [← hz, hvalue]
    exact hy
  rw [abs_mul, abs_of_pos mu.property] at hscaled
  exact (le_div_iff₀ mu.property).2 (by simpa only [mul_comm] using hscaled)

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
