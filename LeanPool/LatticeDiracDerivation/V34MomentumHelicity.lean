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

public import LeanPool.LatticeDiracDerivation.V34CovariantSpinors

/-!
# V3.4 Stage 4: arbitrary-momentum helicity

This stage replaces V3.3's axis-only check by the helicity operator obtained
from the same cube-derived Pauli response in an arbitrary nonzero momentum
direction.  The radius is constrained to be the momentum norm; it is not an
independent fitted scale.
-/

@[expose] public section

namespace LeanDirac.V2

noncomputable section

/-- The two-channel helicity operator for an arbitrary nonzero momentum direction. -/
def v34TwoChannelHelicity
    (radius px py pz : ℝ) (q : UniformCell2) : UniformCell2 :=
  fun component =>
    (-1 / (2 * radius) : ℂ) *
      positivePauliSpatial px py pz q component

/-- The upper two channels of a four-component cubical spinor. -/
def v34UpperChannels (z : CubicalCell4) : UniformCell2
  | 0 => z 0
  | _ => z 1

/-- The lower two channels of a four-component cubical spinor. -/
def v34LowerChannels (z : CubicalCell4) : UniformCell2
  | 0 => z 2
  | _ => z 3

/-- The four-component helicity operator induced by the two-channel action. -/
def v34MomentumHelicity
    (radius px py pz : ℝ) (z : CubicalCell4) : CubicalCell4
  | 0 => v34TwoChannelHelicity radius px py pz (v34UpperChannels z) 0
  | 1 => v34TwoChannelHelicity radius px py pz (v34UpperChannels z) 1
  | 2 => v34TwoChannelHelicity radius px py pz (v34LowerChannels z) 0
  | _ => v34TwoChannelHelicity radius px py pz (v34LowerChannels z) 1

/-- The projector onto a signed helicity branch. -/
def v34HelicityProjector
    (sign radius px py pz : ℝ) (z : CubicalCell4) : CubicalCell4 :=
  fun component =>
    (1 / 2 : ℂ) * z component +
      (sign : ℂ) * v34MomentumHelicity radius px py pz z component

theorem v34_two_channel_helicity_square
    (radius px py pz : ℝ)
    (hradius : radius ^ 2 = px ^ 2 + py ^ 2 + pz ^ 2)
    (hne : radius ≠ 0) (q : UniformCell2) :
    v34TwoChannelHelicity radius px py pz
        (v34TwoChannelHelicity radius px py pz q) =
      fun component => (1 / 4 : ℂ) * q component := by
  rw [show v34TwoChannelHelicity radius px py pz
      (v34TwoChannelHelicity radius px py pz q) =
      fun component =>
        ((-1 / (2 * radius) : ℂ) ^ 2) *
          positivePauliSpatial px py pz
            (positivePauliSpatial px py pz q) component by
    funext component
    fin_cases component <;>
      simp [v34TwoChannelHelicity, positive_pauli_spatial_apply_zero,
        positive_pauli_spatial_apply_one] <;> ring]
  rw [positive_pauli_spatial_square]
  funext component
  have hradiusC : (((px ^ 2 + py ^ 2 + pz ^ 2 : ℝ)) : ℂ) =
      (radius : ℂ) ^ 2 := by exact_mod_cast hradius.symm
  simp only
  rw [hradiusC]
  field_simp [hne]
  ring

theorem v34_momentum_helicity_square
    (radius px py pz : ℝ)
    (hradius : radius ^ 2 = px ^ 2 + py ^ 2 + pz ^ 2)
    (hpositive : 0 < radius) (z : CubicalCell4) :
    v34MomentumHelicity radius px py pz
        (v34MomentumHelicity radius px py pz z) =
      fun component => (1 / 4 : ℂ) * z component := by
  have hu := v34_two_channel_helicity_square
    radius px py pz hradius (ne_of_gt hpositive) (v34UpperChannels z)
  have hl := v34_two_channel_helicity_square
    radius px py pz hradius (ne_of_gt hpositive) (v34LowerChannels z)
  funext component
  fin_cases component
  · exact congrFun hu 0
  · exact congrFun hu 1
  · exact congrFun hl 0
  · exact congrFun hl 1

theorem v34_helicity_projectors_complete
    (radius px py pz : ℝ) (z : CubicalCell4) :
    (fun component =>
      v34HelicityProjector 1 radius px py pz z component +
        v34HelicityProjector (-1) radius px py pz z component) = z := by
  funext component
  simp [v34HelicityProjector]
  ring

theorem v34_momentum_helicity_linear
    (radius px py pz : ℝ) (a b : ℂ) (z w : CubicalCell4) :
    v34MomentumHelicity radius px py pz
        (fun component => a * z component + b * w component) =
      fun component =>
        a * v34MomentumHelicity radius px py pz z component +
          b * v34MomentumHelicity radius px py pz w component := by
  funext component
  fin_cases component <;>
    simp [v34MomentumHelicity, v34TwoChannelHelicity,
      v34UpperChannels, v34LowerChannels,
      positive_pauli_spatial_apply_zero,
      positive_pauli_spatial_apply_one] <;> ring

theorem v34_helicity_projector_idempotent
    (sign radius px py pz : ℝ)
    (hsign : sign ^ 2 = 1)
    (hradius : radius ^ 2 = px ^ 2 + py ^ 2 + pz ^ 2)
    (hpositive : 0 < radius) (z : CubicalCell4) :
    v34HelicityProjector sign radius px py pz
        (v34HelicityProjector sign radius px py pz z) =
      v34HelicityProjector sign radius px py pz z := by
  have hsq := v34_momentum_helicity_square
    radius px py pz hradius hpositive z
  have hsignC : (sign : ℂ) ^ 2 = 1 := by exact_mod_cast hsign
  have hlinear := v34_momentum_helicity_linear radius px py pz
    (1 / 2 : ℂ) (sign : ℂ) z
      (v34MomentumHelicity radius px py pz z)
  rw [show v34HelicityProjector sign radius px py pz
      (v34HelicityProjector sign radius px py pz z) =
      fun component =>
        (1 / 2 : ℂ) * v34HelicityProjector sign radius px py pz z component +
          (sign : ℂ) * v34MomentumHelicity radius px py pz
            (v34HelicityProjector sign radius px py pz z) component by rfl]
  rw [show v34MomentumHelicity radius px py pz
      (v34HelicityProjector sign radius px py pz z) =
      fun component =>
        (1 / 2 : ℂ) * v34MomentumHelicity radius px py pz z component +
          (sign : ℂ) * v34MomentumHelicity radius px py pz
            (v34MomentumHelicity radius px py pz z) component by
      exact hlinear]
  funext component
  have hsqc := congrFun hsq component
  simp only [v34HelicityProjector]
  rw [hsqc]
  ring_nf
  rw [hsignC]
  ring

theorem v34_helicity_projector_is_eigenbranch
    (sign radius px py pz : ℝ)
    (hsign : sign ^ 2 = 1)
    (hradius : radius ^ 2 = px ^ 2 + py ^ 2 + pz ^ 2)
    (hpositive : 0 < radius) (z : CubicalCell4) :
    v34MomentumHelicity radius px py pz
        (v34HelicityProjector sign radius px py pz z) =
      fun component =>
        (sign / 2 : ℂ) *
          v34HelicityProjector sign radius px py pz z component := by
  have hsq := v34_momentum_helicity_square
    radius px py pz hradius hpositive z
  have hsignC : (sign : ℂ) ^ 2 = 1 := by exact_mod_cast hsign
  rw [show v34MomentumHelicity radius px py pz
      (v34HelicityProjector sign radius px py pz z) =
      fun component =>
        (1 / 2 : ℂ) * v34MomentumHelicity radius px py pz z component +
          (sign : ℂ) * v34MomentumHelicity radius px py pz
            (v34MomentumHelicity radius px py pz z) component by
      exact v34_momentum_helicity_linear radius px py pz
        (1 / 2 : ℂ) (sign : ℂ) z
          (v34MomentumHelicity radius px py pz z)]
  funext component
  rw [congrFun hsq component]
  simp only [v34HelicityProjector]
  ring_nf
  rw [hsignC]
  ring

/-- Certificate for arbitrary-momentum helicity projectors and eigenbranches. -/
structure V34MomentumHelicityCertificate : Prop where
  square : ∀ radius px py pz,
    radius ^ 2 = px ^ 2 + py ^ 2 + pz ^ 2 → 0 < radius → ∀ z,
      v34MomentumHelicity radius px py pz
          (v34MomentumHelicity radius px py pz z) =
        fun component => (1 / 4 : ℂ) * z component
  complete : ∀ radius px py pz z,
    (fun component =>
      v34HelicityProjector 1 radius px py pz z component +
        v34HelicityProjector (-1) radius px py pz z component) = z
  idempotent : ∀ sign radius px py pz,
    sign ^ 2 = 1 → radius ^ 2 = px ^ 2 + py ^ 2 + pz ^ 2 → 0 < radius → ∀ z,
      v34HelicityProjector sign radius px py pz
          (v34HelicityProjector sign radius px py pz z) =
        v34HelicityProjector sign radius px py pz z
  eigenbranch : ∀ sign radius px py pz,
    sign ^ 2 = 1 → radius ^ 2 = px ^ 2 + py ^ 2 + pz ^ 2 → 0 < radius → ∀ z,
      v34MomentumHelicity radius px py pz
          (v34HelicityProjector sign radius px py pz z) =
        fun component =>
          (sign / 2 : ℂ) *
            v34HelicityProjector sign radius px py pz z component

theorem v34_momentum_helicity : V34MomentumHelicityCertificate where
  square := v34_momentum_helicity_square
  complete := v34_helicity_projectors_complete
  idempotent := v34_helicity_projector_idempotent
  eigenbranch := v34_helicity_projector_is_eigenbranch

end
end LeanDirac.V2
