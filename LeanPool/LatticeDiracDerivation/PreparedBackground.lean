/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/PreparedBackground.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.CubeGeometry
public import LeanPool.LatticeDiracDerivation.NativeAction

/-! Conditional already-running eight-corner background; no formation claim. -/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section
open BigOperators Complex

def companion (corner : CubeCorner) : C3
  | 0 => -star (tetraCorner corner 1)
  | 1 => star (tetraCorner corner 0)
  | _ => 0

def unitArea : C3
  | 0 => 1
  | _ => 0

theorem wedge_planar_companion
    (u : C3) (hu2 : u 2 = 0) (hnorm : density u = 1) :
    wedge u (fun
      | 0 => -star (u 1)
      | 1 => star (u 0)
      | _ => 0) = unitArea := by
  funext component
  fin_cases component
  · apply Complex.ext
    · have hu2re := congrArg Complex.re hu2
      have hu2im := congrArg Complex.im hu2
      simp at hu2re hu2im
      simp [density, Fin.sum_univ_succ, Complex.normSq] at hnorm
      rw [hu2re, hu2im] at hnorm
      simp [wedge, unitArea] at ⊢
      nlinarith
    · simp [wedge, unitArea]
      ring
  · simp [wedge, unitArea, hu2]
  · simp [wedge, unitArea, hu2]

theorem tetra_wedge_companion_constant (corner : CubeCorner) :
    wedge (tetraCorner corner) (companion corner) = unitArea := by
  apply wedge_planar_companion
  · fin_cases corner <;>
      simp [tetraCorner, tetraRay0, tetraRay1, tetraRay2, tetraRay3,
        c3Of, c3Neg]
  · exact tetra_corner_density_one corner

theorem bond_zero_of_constant_area
    (chi0 : ℝ) (state : State Site) (edge : Bond Site)
    (hconstant : wedge (state.chi edge.source) (state.psi edge.source) =
      wedge (state.chi edge.target) (state.psi edge.target)) :
    exteriorAreaBond chi0 state edge = 0 := by
  unfold exteriorAreaBond
  rw [hconstant]
  simp [difference, density]

theorem running_family_balance
    (A R chi0 omega : ℝ)
    (hdensity : A ^ 2 + R ^ 2 = chi0 ^ 2)
    (hfrequency : omega = chi0) :
    omega ^ 2 * A = (R ^ 2 + A ^ 2) * A ∧
      (R ^ 2 + A ^ 2 - chi0 ^ 2) * R = 0 := by
  have hdensity' : R ^ 2 + A ^ 2 = chi0 ^ 2 := by nlinarith
  subst omega
  rw [hdensity']
  exact ⟨rfl, by ring⟩

theorem running_frequency_is_chi0
    (A R chi0 omega : ℝ) (hA : A ≠ 0)
    (hdensity : A ^ 2 + R ^ 2 = chi0 ^ 2)
    (hpsi : omega ^ 2 * A = (R ^ 2 + A ^ 2) * A)
    (homega : 0 ≤ omega) (hchi0 : 0 ≤ chi0) :
    omega = chi0 := by
  have hsquare0 : omega ^ 2 = R ^ 2 + A ^ 2 := mul_right_cancel₀ hA hpsi
  have hdensity' : R ^ 2 + A ^ 2 = chi0 ^ 2 := by nlinarith
  exact (sq_eq_sq₀ homega hchi0).mp (hsquare0.trans hdensity')

end
end LeanDirac
