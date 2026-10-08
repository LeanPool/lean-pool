/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.ProjectiveStep
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# High-contrast homogenization: Entry.ProjectiveStep

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The projective step

This proves the exact type of `HCPoly/Entry/Statements/ProjectiveStep.lean` (near
`l.projective.step`).
The source-scale premise is retained; its standing sentence is
near `e.source.lower.scale`. The explicit positive
source family is chosen before the geometric constant, and the geometric
constant before `γ`, `K`, the grid scale, the matrices and the step size.
The geometric proof does not use the source-scale premise. Choosing the
source family to be one makes no claim about the separate source estimate.
-/

open HCPolySupport.HighContrast (gridRatio)
namespace HCPolySupport.HighContrast.Entry

open scoped Matrix.Norms.L2Operator

/-- The three printed projective-step conclusions, with the constant
and premise order and arbitrary positive target matrix. -/
theorem projective_step
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ Csrc : ℝ → ℝ, (∀ γ : ℝ, γ ∈ Set.Ico (0 : ℝ) 1 → 0 < Csrc γ) ∧
    ∃ C : ℝ, 0 < C ∧
      ∀ γ : ℝ, γ ∈ Set.Ico (0 : ℝ) 1 →
      ∀ K : ℝ, 1 < K →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ⌈Csrc γ * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
        ∀ (m mStar : Mat d), m.PosDef → mStar.PosDef →
          ∀ ε : ℝ, 0 < ε →
            projectiveDistance m (geometryUpdate ε m mStar) ≤ ε ∧
              1 / 2 *
                    Real.log (‖geometryUpdate ε m mStar‖ * ‖(geometryUpdate ε m mStar)⁻¹‖) ≤
                  1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) + ε ∧
                (ε ≤ 1 →
                  gridRatio (Geometry.explicitRoundedGrid jStar m)
                      (Geometry.explicitRoundedGrid jStar (geometryUpdate ε m mStar)) ≤ C) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hgrid⟩ := Geometry.gridRatio_roundedGrid_le_of_projectiveDistance_le d hd
  refine ⟨fun _ => 1, fun _ _ => zero_lt_one, C, hC, ?_⟩
  intro γ _hγ K _hK jStar hj _hsrc m mStar hm hStar ε hε
  have hstep := Geometry.projectiveDistance_geometryUpdate_le hm hStar hε
  refine ⟨hstep, Geometry.log_eccentricity_geometryUpdate_le hm hStar hε, ?_⟩
  intro hεone
  exact hgrid jStar hj m (geometryUpdate ε m mStar) hm
    (Geometry.geometryUpdate_posDef hm hStar ε) (hstep.trans hεone)

end HCPolySupport.HighContrast.Entry
