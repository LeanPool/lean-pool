/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.ParabolicHolderVecOn
public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalProof
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssembly

/-!
# Local endpoint regularity

The local Escauriaza–Seregin–Šverák theorem `thm:ess-local`: a local weak
solution on the unit parabolic cylinder, with pressure in `L^{3/2}` and velocity
bounded in `L³` in space uniformly in time, agrees almost everywhere on the half
cylinder with a field that is parabolically Hölder continuous on its closure.
The regularity argument of `thm:ess-local` is combined with the blow-up limit
`prop:blowup-limit` at a point that is not good.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.Main

/-- The local Escauriaza–Seregin–Šverák regularity theorem `thm:ess-local`. -/
theorem essLocal :
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
    ∀ p : ParabolicPoint → ℝ,
      AEStronglyMeasurable u
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      AEStronglyMeasurable Du
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      AEStronglyMeasurable p
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      essSup
        (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
        (volume.restrict (Ioo (-1) 0)) < ⊤ →
      (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ →
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      essSup
        (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo (-1) 0)) < ⊤ →
      (∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
        HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
          (fun x => u (x, t) i) (fun x => Du (x, t) i)) →
      (∀ ψ : ParabolicPoint → ℝ,
        ψ ∈ spaceTimeTestFunction (V := ℝ)
          (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
        ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0) →
      (∀ φ : ParabolicPoint → Vec3,
        φ ∈ spaceTimeTestFunction (V := Vec3)
          (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
        ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u z i * u z j * spatialPartial (fun y => φ y i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du z i j * spatialPartial (fun y => φ y i) j z
            - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
            - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0) →
      ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict
            (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))] u ∧
          ParabolicHolderVecOn
            (closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))) w γ := by
  intro u Du p hu hDu hp hL2 henergy hpLp hL3 hgrad hS2 hS3
  exact essLocal_of_inputs hu hDu hp hL2 henergy hpLp hL3 hgrad hS2 hS3
    (blowupLimit_projection hu hDu hp hL2 henergy hpLp hL3 hgrad hS2 hS3)

end ESS.Main

end
