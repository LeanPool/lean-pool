/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalEnergyResult

/-!
# Source suitability for the blow-up limit

The local energy result supplies the suitable source solution used on the
smaller cylinder in `prop:blowup-limit`.
-/

public section

open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal


noncomputable section

namespace ESS

/-- The hypotheses of `thm:ess-local` make the source solution suitable on
the interior cylinder needed for `prop:blowup-limit`. -/
theorem blowup_limit_source_suitable
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0))))
    (hp : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0))))
    (hL2 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball 0 1,
      ‖u (x, t)‖ₑ ^ (2 : ℝ)) (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0))))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball 0 1) (fun x => u (x, t) i)
        (fun x => Du (x, t) i))
    (hS2 : ∀ ψ ∈ spaceTimeTestFunction (vec3Ball 0 1) (Ioo (-1) 0),
      ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
    (hS3 : ∀ φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball 0 1) (Ioo (-1) 0),
      ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0) :
    IsSuitableWeakSolution (vec3Ball 0 (3 / 4 : ℝ)) (Ioo (-1) 0) 3
      u Du p (0 : ParabolicPoint → Vec3) := by
  have hlocal := leiL4_of_essLocalData
    (r := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
    hu hDu hp hL2 henergy hpLp hL3 hgrad hS2 hS3
  exact hlocal.2.2

end ESS
