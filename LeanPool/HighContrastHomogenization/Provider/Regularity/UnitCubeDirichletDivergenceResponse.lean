/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Deterministic.HomogenizationBlackBoxes.DualityPositiveBridge
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.UnitCubeEuclideanL2

/-!
# High-contrast homogenization: Provider.Regularity.UnitCubeDirichletDivergenceResponse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# A selected identity Dirichlet response on the unit cube

Every proof-carrying Euclidean `L²` vector field on the centered unit cube
defines an admissible datum for the identity Dirichlet divergence problem.
This module selects one weak zero-trace response and records its defining weak
equation.  No pointwise uniqueness of `H10Function` representatives is
asserted.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A proof-carrying unit-cube Euclidean `L²` field is an ambient vector
`L²` datum for the normalized cube measure. -/
theorem unitCubeEuclideanL2Field_memLp_normalizedCubeMeasure
    (F : UnitCubeEuclideanL2Field d) :
    MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0)) := by
  rw [← cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  change MemLp F (2 : ℝ≥0∞) (unitCenteredCubeDomain d).normalizedVolume
  apply MemLp.of_eval
  intro i
  have hF := F.euclideanMemL2
  rw [memLp_piLp_iff] at hF
  simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hF i

/-- Every proof-carrying Euclidean `L²` datum on the centered unit cube has
an identity-coefficient zero-trace weak response. -/
theorem exists_unitCubeDirichletDivergenceResponse [NeZero d]
    (F : UnitCubeEuclideanL2Field d) :
    ∃ w : H10Function (openCubeSet (originCube d 0)),
      CubeDirichletDivergenceProblem (originCube d 0) w F :=
  exists_cubeDirichletDivergenceProblem_of_memLp_normalizedCubeMeasure
    (unitCubeEuclideanL2Field_memLp_normalizedCubeMeasure F)

/-- A selected identity-coefficient zero-trace weak response to a unit-cube
Euclidean `L²` datum.  The selection is characterized below only by the weak
equation, which is the representative-invariant property used downstream. -/
@[expose]
noncomputable def unitCubeDirichletDivergenceResponse [NeZero d]
    (F : UnitCubeEuclideanL2Field d) :
    H10Function (openCubeSet (originCube d 0)) :=
  Classical.choose (exists_unitCubeDirichletDivergenceResponse F)

/-- The selected response satisfies the identity Dirichlet divergence
problem with exactly the supplied datum. -/
theorem unitCubeDirichletDivergenceResponse_problem [NeZero d]
    (F : UnitCubeEuclideanL2Field d) :
    CubeDirichletDivergenceProblem (originCube d 0)
      (unitCubeDirichletDivergenceResponse F) F :=
  Classical.choose_spec (exists_unitCubeDirichletDivergenceResponse F)

end

end HighContrast
end HCPolySupport
