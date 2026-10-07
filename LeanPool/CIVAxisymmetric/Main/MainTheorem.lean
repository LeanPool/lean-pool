/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Hypotheses
public import LeanPool.CIVAxisymmetric.Main.AxisymmetricTheorem
public import LeanPool.CIVAxisymmetric.Reduction.MainTheoremAxisymmetry
public import LeanPool.CIVAxisymmetric.Reduction.AxisymmetricDerivativeCongruence

/-!
# The public statement `CIV.Main.mainTheorem`

This module proves the statement `CIV.mainTheorem` (`thm:main`). The proof is the printed one:
interior analyticity and the identity theorem make `u` axisymmetric on the unit cylinder
(`CIV.isAxisymmetricOn_unitCylinder_of_forceSpatiallyAnalytic`), so the bounds
`eq:interior:mean:bounds` on the angular mean are the bounds `eq:aniso:bounds` on `u`
(`CIV.anisotropicBounds_of_isAxisymmetricOn`), and `thm:aniso:main` (`CIV.Main.axisymmetricTheorem`)
makes `(0,0)` a regular point.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV
namespace Main

/-- The public statement of `thm:main`: under analytic forcing, the anisotropic bounds on the
angular mean and an axisymmetric core at every time, the solution is axisymmetric on the unit
cylinder and regular at the origin. -/
theorem mainTheorem (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (h : ℝ) (hh : 0 < h ∧ h < 1 / 2)
    (hMf : ForceC2Bounded f) (hfa : ForceSpatiallyAnalytic f)
    (C : ℝ) (hC : 0 < C) (hbounds : AnisotropicBounds C h (angularMean u))
    (hcore : ∀ t ∈ Ioo (-1 : ℝ) 0, ∃ ρ ∈ Ioo (0 : ℝ) 1,
      IsAxisymmetricOn u (spaceTimeSet (vec3Ball 0 ρ) {t})) :
    IsAxisymmetricOn u unitCylinder ∧ BoundedNearOrigin u := by
  have haxi := isAxisymmetricOn_unitCylinder_of_forceSpatiallyAnalytic hsol hu hp hf hfa hcore
  exact ⟨haxi, axisymmetricTheorem q u Du p f hsol henergy hu hp hf haxi h hh hMf C hC
    (anisotropicBounds_of_isAxisymmetricOn haxi hbounds)⟩

end Main
end CIV
