/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.ConvexInteractionCurvature
public import LeanPool.CutoffRigidity.GibbsSelfAdjointEigenfunctions

/-!
# An actual operator eigenvalue supplied by the interaction symmetry

The coordinate-sum argument of Section 3.5 now supplies a nonzero vector in
the actual self-adjoint Gibbs form operator eigenspace. Its optimal-gap
identification additionally requires the curvature spectral lower bound.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ} {ρ : ℝ} {W : EuclideanSpace ℝ (Fin d) → ℝ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "V" => (fun x : E => ρ / 2 * ‖x‖ ^ 2 + W x)

/-- Translation invariance exhibits a nonzero eigenclass of the genuine
self-adjoint form operator, with actual L²-domain membership proved. -/
theorem diagonal_interaction_has_operator_eigenvector (hd : 0 < d)
    (hW : ContDiff ℝ 2 W) (hρ : 0 < ρ)
    (hinv : ∀ x : E, ∀ t : ℝ, W (x + t • diagonalDirection d) = W x)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hV : ContDiff ℝ 2 V) :
    ∃ u : gibbsOperatorEigenspace hV hprob ρ, u ≠ 0 := by
  obtain ⟨u, hu⟩ := exists_nonzero_classical_eigenvector_of_diagonal_invariance hd hW hρ hinv hprob
  have hm : (u : E →₂[gibbsMeasure volume V] ℝ) ∈ gibbsOperatorEigenspace hV hprob ρ :=
    classicalL2Eigenspace_le_gibbsOperatorEigenspace hV hprob ρ hρ.le u.property
  refine ⟨⟨u, hm⟩, ?_⟩
  intro hzero
  have hv : (u : E →₂[gibbsMeasure volume V] ℝ) = 0 :=
    congrArg (fun v : gibbsOperatorEigenspace hV hprob ρ =>
      (v : E →₂[gibbsMeasure volume V] ℝ)) hzero
  exact hu (Subtype.ext hv)

/-- The actual coordinate-sum operator eigenvalue is present after the
paper's explicit normalization, without a probability-measure hypothesis. -/
theorem normalized_convexInteraction_has_operator_eigenvector (hd : 0 < d)
    (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ Set.univ W) (hρ : 0 < ρ)
    (hinv : ∀ x : E, ∀ t : ℝ, W (x + t • diagonalDirection d) = W x) :
    let Z := ∫ x : E, Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + W x))
    let Vn := fun x : E => ρ / 2 * ‖x‖ ^ 2 + (W x + Real.log Z)
    ∃ (hVn : ContDiff ℝ 2 Vn)
      (hp : IsProbabilityMeasure (gibbsMeasure volume Vn)),
      ∃ u : gibbsOperatorEigenspace hVn hp ρ, u ≠ 0 := by
  intro Z Vn
  have hVn : ContDiff ℝ 2 Vn :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).add (hW.add contDiff_const)
  have hp : IsProbabilityMeasure (gibbsMeasure volume Vn) := by
    simpa only [Vn, add_assoc] using
      (convexInteraction_normalized_probability_memLp_two hW hconv ρ hρ).1
  refine ⟨hVn, hp, ?_⟩
  have hWn : ContDiff ℝ 2 (fun x : E => W x + Real.log Z) := hW.add contDiff_const
  have hi : ∀ x : E, ∀ t : ℝ,
      W (x + t • diagonalDirection d) + Real.log Z = W x + Real.log Z := by
    intro x t
    rw [hinv]
  exact diagonal_interaction_has_operator_eigenvector hd hWn hρ hi hp hVn

end CutoffRigidity
