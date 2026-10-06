/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Main.MainTheorem
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CIVAxisymmetric.Statements.AngularMean
public import LeanPool.CIVAxisymmetric.Statements.AnisotropicBounds
public import LeanPool.CIVAxisymmetric.Statements.BoundedNearOrigin
public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import LeanPool.CIVAxisymmetric.Statements.ForceSpatiallyAnalytic
public import LeanPool.CIVAxisymmetric.Statements.GlobalEnergyClass
public import LeanPool.CIVAxisymmetric.Statements.IsAxisymmetricOn
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder

/-!
# Main Theorem

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- Theorem 1.1 (`thm:main`): regularity under anisotropic Type II bounds and analytic forcing. -/
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
    IsAxisymmetricOn u unitCylinder ∧ BoundedNearOrigin u :=
by exact CIV.Main.mainTheorem q u Du p f hsol henergy hu hp hf h hh hMf hfa C hC hbounds hcore

end CIV
