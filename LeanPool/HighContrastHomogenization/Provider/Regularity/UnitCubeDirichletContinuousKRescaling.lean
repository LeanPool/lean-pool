/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.UnitCubeDirichletContinuousKCompetitor

/-!
# High-contrast homogenization: Provider.Regularity.UnitCubeDirichletContinuousKRescaling

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Rescaled continuous K-functional bound for the unit-cube Dirichlet map

The exact lower endpoint and the finite upper endpoint are combined without
collapsing their constants.  Enlarging the interpolation scale by one fixed
factor absorbs the upper bound while the normalized Euclidean `L²` residual
retains constant one.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

private theorem continuousKFunctionalCompetitorValue_le_rescaled
    {d : ℕ} {A : ℝ} (hA : 0 ≤ A) {t u : ContinuousKScale}
    (htu : u.1 = A * t.1) (F H : UnitCubeEuclideanL2Field d)
    (V G : ContinuousKCompetitor d)
    (hresidual : continuousKResidualNorm F V ≤ continuousKResidualNorm H G)
    (hgradient : continuousKGradientNorm V ≤ A * continuousKGradientNorm G) :
    continuousKFunctionalCompetitorValue t F V ≤
      continuousKFunctionalCompetitorValue u H G := by
  have hresidualSq : continuousKResidualNorm F V ^ 2 ≤
      continuousKResidualNorm H G ^ 2 :=
    (sq_le_sq₀ (continuousKResidualNorm_nonneg F V)
      (continuousKResidualNorm_nonneg H G)).mpr hresidual
  have hscaledGradientNonneg : 0 ≤ A * continuousKGradientNorm G :=
    mul_nonneg hA (continuousKGradientNorm_nonneg G)
  have hgradientSq : continuousKGradientNorm V ^ 2 ≤
      (A * continuousKGradientNorm G) ^ 2 :=
    (sq_le_sq₀ (continuousKGradientNorm_nonneg V) hscaledGradientNonneg).mpr hgradient
  unfold continuousKFunctionalCompetitorValue
  apply Real.sqrt_le_sqrt
  calc
    continuousKResidualNorm F V ^ 2 + t.1 ^ 2 * continuousKGradientNorm V ^ 2 ≤
        continuousKResidualNorm H G ^ 2 +
          t.1 ^ 2 * (A * continuousKGradientNorm G) ^ 2 :=
      add_le_add hresidualSq
        (mul_le_mul_of_nonneg_left hgradientSq (sq_nonneg t.1))
    _ = continuousKResidualNorm H G ^ 2 +
        u.1 ^ 2 * continuousKGradientNorm G ^ 2 := by
      rw [htu]
      ring

/-- There is a dimension-dependent expansion factor `A ≥ 1` such that the
unit-cube identity Dirichlet solution map satisfies `K(t, ∇w) ≤ K(A t, h)`
whenever both displayed parameters belong to the source scale carrier.  The
factor is fixed before both scales, the datum, and the weak solution. -/
theorem exists_unitCubeDirichletContinuousKFunctional_rescaled
    (d : ℕ) [NeZero d] :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (h : UnitCubeEuclideanL2Field d)
        (w : H10Function (openCubeSet (originCube d 0)))
        (t u : ContinuousKScale),
        CubeDirichletDivergenceProblem (originCube d 0) w h →
          u.1 = A * t.1 →
            continuousKFunctional t (unitCubeGradientEuclideanL2Field w) ≤
              continuousKFunctional u h := by
  rcases exists_unitCubeDirichletContinuousKCompetitorBounds d with
    ⟨B, hBnonneg, hcompetitor⟩
  let A : ℝ := max 1 B
  have honeA : 1 ≤ A := by
    dsimp [A]
    exact le_max_left 1 B
  have hBA : B ≤ A := by
    dsimp [A]
    exact le_max_right 1 B
  have hAnonneg : 0 ≤ A := hBnonneg.trans hBA
  refine ⟨A, honeA, ?_⟩
  intro h w t u hw htu
  unfold continuousKFunctional
  refine le_csInf (continuousKFunctional_range_nonempty u h) ?_
  rintro y ⟨G, rfl⟩
  rcases hcompetitor h w G hw with ⟨V, hresidual, hgradient⟩
  have hgradient' : continuousKGradientNorm V ≤
      A * continuousKGradientNorm G :=
    hgradient.trans (mul_le_mul_of_nonneg_right hBA
      (continuousKGradientNorm_nonneg G))
  calc
    sInf (Set.range fun W : ContinuousKCompetitor d ↦
        continuousKFunctionalCompetitorValue t
          (unitCubeGradientEuclideanL2Field w) W) ≤
        continuousKFunctionalCompetitorValue t
          (unitCubeGradientEuclideanL2Field w) V :=
      csInf_le
        (continuousKFunctional_range_bddBelow t
          (unitCubeGradientEuclideanL2Field w)) ⟨V, rfl⟩
    _ ≤ continuousKFunctionalCompetitorValue u h G :=
      continuousKFunctionalCompetitorValue_le_rescaled
        hAnonneg htu
        (unitCubeGradientEuclideanL2Field w) h V G hresidual hgradient'

end

end HighContrast
end HCPolySupport
