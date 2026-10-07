/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution

/-!
# Solenoidal tests in the strong weak equation

The pressure term in the pressure-inclusive equation vanishes for compactly
supported solenoidal tests (`lem:lps-H1-estimate`).
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The pressure-inclusive strong equation reduces to its pressure-free weak
form on every compactly supported solenoidal test field
(`lem:lps-H1-estimate`). -/
theorem lps_strong_solenoidal_weak_equation
    {a b : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : ESS.IsLpsStrongSolution a b u Du p)
    {φ : ParabolicPoint → Vec3}
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Set.univ (Ioo a b))
    (hdiv : ∀ z, ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z = 0) :
    ∫ z in spaceTimeSet Set.univ (Ioo a b),
      (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * spatialPartial (fun y => φ y i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * spatialPartial (fun y => φ y i) j z) = 0 := by
  rcases hU with ⟨_hab, _hslices, _hcont, _hderivs, _hp, hEquation⟩
  have hfull := hEquation φ hφ
  have hpoint (z : ParabolicPoint) :
      (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * spatialPartial (fun y => φ y i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * spatialPartial (fun y => φ y i) j z
        - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) =
      (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * spatialPartial (fun y => φ y i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * spatialPartial (fun y => φ y i) j z) := by
    rw [hdiv z]
    simp only [mul_zero, sub_zero]
  have hrewrite :
      (∫ z in spaceTimeSet Set.univ (Ioo a b),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)) =
      (∫ z in spaceTimeSet Set.univ (Ioo a b),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z)) := by
    apply integral_congr_ae
    filter_upwards [] with z
    exact hpoint z
  rw [← hrewrite]
  exact hfull

end ESS.LPS

end
