/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CenteredCubeDirichletNormalizedEuclideanL2Residual
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.ContinuousKRegularity

/-!
# High-contrast homogenization: Provider.Regularity.UnitCubeDirichletContinuousKCompetitor

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Unit-cube continuous K-functional competitor bounds

The exact normalized Euclidean `L²` residual contraction is combined with
the identity-Dirichlet `H²` lift.  For every genuine continuous `H¹`
competitor of the datum, this produces a genuine continuous `H¹` competitor
of the solution gradient.  The lower endpoint retains constant one; only the
upper endpoint carries a dimension-dependent constant.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

private noncomputable def unitCubeEuclideanL2FieldToCenteredCubeZero
    {d : ℕ} (F : UnitCubeEuclideanL2Field d) :
    CenteredCubeEuclideanL2Field d 0 where
  toField := F
  euclideanMemL2 := by
    simpa only [centeredCubeDomain, unitCenteredCubeDomain] using F.euclideanMemL2

@[simp] private theorem unitCubeEuclideanL2FieldToCenteredCubeZero_apply
    {d : ℕ} (F : UnitCubeEuclideanL2Field d) (x : Vec d) :
    unitCubeEuclideanL2FieldToCenteredCubeZero F x = F x :=
  rfl

/-- The unit-cube Euclidean `L²` field underlying a continuous `K`-functional competitor. -/
@[expose]
public noncomputable def continuousKCompetitorToUnitCubeEuclideanL2Field
    {d : ℕ} (G : ContinuousKCompetitor d) : UnitCubeEuclideanL2Field d where
  toField := G.toField
  euclideanMemL2 := G.euclideanMemL2

@[simp] private theorem continuousKCompetitorToUnitCubeEuclideanL2Field_apply
    {d : ℕ} (G : ContinuousKCompetitor d) (x : Vec d) :
    continuousKCompetitorToUnitCubeEuclideanL2Field G x = G.toField x :=
  rfl

/-- Every continuous `H¹` competitor for the datum lifts to a continuous
`H¹` competitor for the unit-cube Dirichlet solution gradient.  The residual
bound is nonexpansive in the exact normalized Euclidean `L²` norm; the upper
endpoint constant is fixed before the datum, solution, and competitor. -/
theorem exists_unitCubeDirichletContinuousKCompetitorBounds
    (d : ℕ) [NeZero d] :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (h : UnitCubeEuclideanL2Field d)
        (w : H10Function (openCubeSet (originCube d 0)))
        (G : ContinuousKCompetitor d),
        CubeDirichletDivergenceProblem (originCube d 0) w h →
          ∃ V : ContinuousKCompetitor d,
            continuousKResidualNorm (unitCubeGradientEuclideanL2Field w) V ≤
                continuousKResidualNorm h G ∧
              continuousKGradientNorm V ≤ B * continuousKGradientNorm G := by
  rcases cubeDirichletH1CompetitorLiftRegularity d with ⟨C₁, hC₁, hlift⟩
  let D : ℝ := (d + 1 : ℝ) ^ 2
  refine ⟨C₁ * D, mul_nonneg hC₁ (sq_nonneg _), ?_⟩
  intro h w G hw
  rcases hlift (originCube d 0) G.toCubeVectorH1Function with
    ⟨v, V, hv, hVfield, hVgradient⟩
  refine ⟨V.toContinuousKCompetitor, ?_, ?_⟩
  · have hresidualENorm :=
      centeredCubeDirichletDivergence_normalizedEuclideanLpENorm_grad_sub_le
        (unitCubeEuclideanL2FieldToCenteredCubeZero h)
        (unitCubeEuclideanL2FieldToCenteredCubeZero
          (continuousKCompetitorToUnitCubeEuclideanL2Field G)) w v
        (by simpa only [unitCubeEuclideanL2FieldToCenteredCubeZero_apply] using! hw)
        (by
          simpa only [continuousKCompetitorToUnitCubeEuclideanL2Field_apply,
            unitCubeEuclideanL2FieldToCenteredCubeZero_apply,
            ContinuousKCompetitor.toCubeVectorH1Function_toField] using! hv)
    have hresidualENorm' :
        (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
            (fun x ↦ unitCubeGradientEuclideanL2Field w x -
              V.toContinuousKCompetitor.toField x) ≤
          (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
            (fun x ↦ h x - G.toField x) := by
      simpa only [centeredCubeDomain, unitCenteredCubeDomain,
        unitCubeEuclideanL2FieldToCenteredCubeZero_apply,
        continuousKCompetitorToUnitCubeEuclideanL2Field_apply,
        unitCubeGradientEuclideanL2Field_apply,
        CubeVectorH1Function.toContinuousKCompetitor_toField, hVfield] using
          hresidualENorm
    have hinputMem : MemLp (fun x ↦ euclideanNorm (h x - G.toField x))
        (2 : ℝ≥0∞) (unitCenteredCubeDomain d).normalizedVolume := by
      have hsub := h.euclideanMemL2.sub G.euclideanMemL2
      simpa only [euclideanNorm_eq_norm_ofVec, HilbertVec.ofVec,
        PiLp.toLp_apply, Pi.sub_apply] using! hsub.norm
    unfold continuousKResidualNorm
    change
      ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
        (fun x ↦ unitCubeGradientEuclideanL2Field w x -
          V.toContinuousKCompetitor.toField x)).toReal ≤
        ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
          (fun x ↦ h x - G.toField x)).toReal
    exact ENNReal.toReal_mono hinputMem.eLpNorm_ne_top hresidualENorm'
  · calc
      continuousKGradientNorm V.toContinuousKCompetitor ≤
          V.toContinuousKCompetitor.toCubeVectorH1Function.relativeGradientCoordL2NormSum :=
        continuousKGradientNorm_le_cubeRelativeGradientCoordL2NormSum
          V.toContinuousKCompetitor
      _ = V.gradientCoordL2NormSum := by simp
      _ ≤ C₁ * G.toCubeVectorH1Function.gradientCoordL2NormSum := hVgradient
      _ = C₁ * G.toCubeVectorH1Function.relativeGradientCoordL2NormSum := by simp
      _ ≤ C₁ * ((d + 1 : ℝ) ^ 2 * continuousKGradientNorm G) :=
        mul_le_mul_of_nonneg_left
          (cubeRelativeGradientCoordL2NormSum_le_dimPlusOne_sq_mul_continuousKGradientNorm G)
          hC₁
      _ = (C₁ * D) * continuousKGradientNorm G := by
        dsimp [D]
        ring

end

end HighContrast
end HCPolySupport
