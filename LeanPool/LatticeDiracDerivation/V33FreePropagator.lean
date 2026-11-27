/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation at commit 7b2a51cf933798eeb931731609fda0ffa81123fe.
Upstream source is dual-licensed under MIT or CC0 1.0; used here under MIT.
-/

module

public import LeanPool.LatticeDiracDerivation.V33GordonIdentity

/-!
# V3.3 Stage 8: free momentum-space resolvent

The inverse is proved away from the free pole.  This is an algebraic Green
operator for the derived free Hamiltonian, not an interacting propagator.
-/

@[expose] public section

namespace LeanDirac.V2

noncomputable section

/-- The free resolvent obtained from the factored Dirac operator. -/
def v33FreeResolvent
    (energy mass px py pz : ℂ) (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    (energy * z component +
      cubicalStandardHamiltonian mass px py pz z component) /
      (energy ^ 2 - (mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2))

/-- The free momentum-space Dirac operator. -/
def v33FreeDiracOperator
    (energy mass px py pz : ℂ) (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    energy * z component -
      cubicalStandardHamiltonian mass px py pz z component

theorem v33_free_resolvent_is_right_inverse
    (energy mass px py pz : ℂ)
    (hoff : energy ^ 2 - (mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) ≠ 0)
    (z : CubicalCell4) :
    v33FreeDiracOperator energy mass px py pz
        (v33FreeResolvent energy mass px py pz z) = z := by
  funext component
  fin_cases component <;>
    simp [v33FreeDiracOperator, v33FreeResolvent,
      cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    field_simp [hoff] <;> ring_nf <;>
    norm_num [Complex.I_sq] <;> ring

theorem v33_free_resolvent_is_left_inverse
    (energy mass px py pz : ℂ)
    (hoff : energy ^ 2 - (mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) ≠ 0)
    (z : CubicalCell4) :
    v33FreeResolvent energy mass px py pz
        (v33FreeDiracOperator energy mass px py pz z) = z := by
  funext component
  fin_cases component <;>
    simp [v33FreeDiracOperator, v33FreeResolvent,
      cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    field_simp [hoff] <;> ring_nf <;>
    norm_num [Complex.I_sq] <;> ring

/-- Certificate for the free resolvent and its inverse relation off shell. -/
structure V33FreePropagatorCertificate : Prop where
  rightInverse : ∀ energy mass px py pz,
    energy ^ 2 - (mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) ≠ 0 → ∀ z,
      v33FreeDiracOperator energy mass px py pz
          (v33FreeResolvent energy mass px py pz z) = z
  leftInverse : ∀ energy mass px py pz,
    energy ^ 2 - (mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) ≠ 0 → ∀ z,
      v33FreeResolvent energy mass px py pz
          (v33FreeDiracOperator energy mass px py pz z) = z

theorem v33_free_propagator : V33FreePropagatorCertificate where
  rightInverse := v33_free_resolvent_is_right_inverse
  leftInverse := v33_free_resolvent_is_left_inverse

end
end LeanDirac.V2
