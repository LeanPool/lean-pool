/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac002.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac001
public import LeanPool.LatticeDiracDerivation.PreparedBackground

/-!
DIRAC-002: reduced positive two-field action and prepared geometry.

This gate depends explicitly on DIRAC-001 and makes no Dirac claim yet.
-/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section

theorem dirac002_positive_two_field_action
    [Fintype Site] [Fintype Edge]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (bond : Edge → Bond Site) (hchi : 0 < chi0) (hB : 0 ≤ B)
    (hweight : ∀ edge, 0 ≤ (bond edge).weight) :
    0 ≤ hamiltonian chi0 B state velocity bond ∧
      state = ⟨state.psi, state.chi⟩ := by
  exact ⟨hamiltonian_nonnegative chi0 B state velocity bond
    hchi hB hweight, state_has_exactly_two_field_families state⟩

theorem dirac002_positive_c19_two_field_action
    [Fintype Site]
    (chi0 B : ℝ) (state : State Site) (velocity : Velocity Site)
    (geometry : C19Lattice Site) (hchi : 0 < chi0) (hB : 0 ≤ B) :
    0 ≤ c19Hamiltonian chi0 B state velocity geometry ∧
      state = ⟨state.psi, state.chi⟩ := by
  exact ⟨c19_hamiltonian_nonnegative chi0 B state velocity geometry hchi hB,
    state_has_exactly_two_field_families state⟩

theorem dirac002_positive_periodic_c19_two_field_action
    (L : ℕ) [NeZero L]
    (chi0 B : ℝ) (state : State (PeriodicCubicSite L))
    (velocity : Velocity (PeriodicCubicSite L))
    (hchi : 0 < chi0) (hB : 0 ≤ B) :
    0 ≤ c19Hamiltonian chi0 B state velocity (periodicC19Geometry L) ∧
      state = ⟨state.psi, state.chi⟩ :=
  dirac002_positive_c19_two_field_action
    chi0 B state velocity (periodicC19Geometry L) hchi hB

def PreparedCubeGeometry : Prop :=
    (∀ corner : CubeCorner,
      wedge (tetraCorner corner) (companion corner) = unitArea) ∧
    faceProduct 0 2 3 1 = (-1/9 : ℂ) ∧
    faceProduct 4 6 7 5 = (-1/9 : ℂ) ∧
    faceProduct 0 4 5 1 = (-1/9 : ℂ) ∧
    faceProduct 2 6 7 3 = (-1/9 : ℂ) ∧
    faceProduct 0 4 6 2 = (-1/9 : ℂ) ∧
    faceProduct 1 5 7 3 = (-1/9 : ℂ)

theorem dirac002_prepared_geometry : PreparedCubeGeometry := by
  unfold PreparedCubeGeometry
  exact ⟨tetra_wedge_companion_constant,
    all_face_products_negative⟩

/-!
DIRAC-002 declares this noncanonical action as the candidate starting law.  It
does not claim that the action or its normalization is uniquely forced by a
more primitive theory.  The certificate records exactly what is proved here:
positivity on the period-two C19 lattice and the complete prepared cube
geometry.
-/

structure Dirac002Certificate : Prop where
  positivePeriodicAction : ∀
      (state : State (PeriodicCubicSite 2))
      (velocity : Velocity (PeriodicCubicSite 2)),
    0 ≤ c19Hamiltonian chi0 chiKineticNormalization state velocity
      (periodicC19Geometry 2) ∧
    state = ⟨state.psi, state.chi⟩
  preparedGeometry : PreparedCubeGeometry

theorem dirac002_candidate_action_and_geometry : Dirac002Certificate where
  positivePeriodicAction := by
    intro state velocity
    exact dirac002_positive_periodic_c19_two_field_action 2
      chi0 chiKineticNormalization state velocity
      (by norm_num [chi0])
      (by rw [chi_kinetic_normalization_eq_1197]; norm_num)
  preparedGeometry := dirac002_prepared_geometry

end
end LeanDirac
