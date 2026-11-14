/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PenalizationEverywhere
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ShiftedResolventRegularity
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PenalizedBoundaryComparison
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PenalizedInterchangeGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Vanishing

/-!
# CruxGeneralDomainTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Agmon tail comparison for a killed set inside an exhaustion cube

The exterior-penalization interchange compares the whole-space penalized
resolvents of a killed set `V` with the penalized resolvents of the next
exhaustion cube.  The error is the scale-free Agmon tail at mass `mu + n`, and
the only geometric input is that the data vanish off `V` and that `V` lies
inside a fixed exhaustion cube: a point beyond the collar of that cube has a
unit Euclidean ball disjoint from `V`, which is what the tail theorem reads.

The killed set is an arbitrary open subset of the cube.  No interchange
statement is asserted for data which remain nonzero outside the killed set.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open MarkovProcess.Semigroup
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- A point beyond the collar of an exhaustion cube has a unit Euclidean ball
disjoint from every subset of that cube. -/
theorem disjoint_unitBall_of_subset_wholeSpaceCube {V : Set (Vec d)} {v : ℕ}
    (hVcube : V ⊆ wholeSpaceCube d v) {x : Vec d}
    (hx : x ∉ interchangeCollar d v) :
    Disjoint (euclideanBall x 1) V :=
  Set.disjoint_of_subset_right hVcube
    (disjoint_unitBall_wholeSpaceCube_of_notMem_interchangeCollar v hx)

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- The zero-trace penalized cube solution and its analytic representative
agree almost everywhere on the cube. -/
theorem penalizedCubeResolventH10_ae_eq
    {V : Set (Vec d)} (hV : IsOpen V) (n : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    (A.penalizedCubeResolventH10 hV n mu hf hfD m).toH1Function.toFun =ᵐ[
        volumeMeasureOn (wholeSpaceCube d m)]
      A.analyticPenalizedCubeResolvent hV n mu f hf hfD m := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let F : ScalarL2 (wholeSpaceCube d m) :=
    boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
      (fun y ↦ hfD y)
  let z := A.penalizedCubeResolventH10 hV n mu hf hfD m
  have hvalue : z.toH1Function.toScalarL2 =
      potentialResolvent A.a mu.property A.hnu (A.cubeEllipticity m)
        (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m) F := by
    simpa only [z, F, hU] using
      A.penalizedCubeResolventH10_value hV n mu hf hfD m
  filter_upwards [z.toH1Function.coeFn_toScalarL2,
    A.analyticPenalizedCubeResolvent_ae hV n mu hf hfD m]
      with y hz hrep
  rw [← hz, hvalue, ← hrep]

end WholeSpaceAnalyticData

omit [NeZero d] in
/-- The `L²` class of a globally defined bounded measurable observable on an
exhaustion cube is that observable almost everywhere there. -/
theorem boundedMeasurableToScalarL2_wholeSpaceCube_ae_eq
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    (boundedMeasurableToScalarL2
      (isOpenBoundedConvexDomain_wholeSpaceCube d m)
      (hf.comp measurable_subtype_coe) (fun y ↦ hfD y) : Vec d → ℝ) =ᵐ[
        volumeMeasureOn (wholeSpaceCube d m)] f := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  filter_upwards [boundedMeasurableToScalarL2_coeFn hU
      (hf.comp measurable_subtype_coe) (fun y ↦ hfD y),
    ae_restrict_mem hU.isOpen.measurableSet] with y hy hyU
  rw [hy, domainExtension_of_mem hyU]
  rfl

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

omit [NeZero d] in
/-- On a measurable set the whole-space exterior penalization potential of a
killed set agrees almost everywhere with the local penalization potential. -/
theorem wholeSpacePenalizationPotential_ae_eq_penalizationPotential
    {V U : Set (Vec d)} (hU : MeasurableSet U) (n : ℕ) :
    wholeSpacePenalizationPotential V n =ᵐ[volumeMeasureOn U]
      penalizationPotential U V n := by
  filter_upwards [ae_restrict_mem hU] with y hyU
  classical
  by_cases hyV : y ∈ V
  · rw [wholeSpacePenalizationPotential_eq_zero n hyV, penalizationPotential,
      Set.indicator_of_notMem (fun hy ↦ hy.2 hyV)]
  · have hyc : y ∈ Vᶜ := hyV
    rw [wholeSpacePenalizationPotential, Set.indicator_of_mem hyc,
      penalizationPotential,
      Set.indicator_of_mem (show y ∈ U \ V from ⟨hyU, hyV⟩)]

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
