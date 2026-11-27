/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSourceWave
public import LeanPool.VacuumBellSeparation.FreeField.LorentzMap

/-!
# Literal complexification of the original spacetime automorphisms

Complex spacetime has the same one time and three spatial coordinates as
the manuscript's quadric. A real spacetime map is complexified on its
four coordinate vectors. This is an actual continuous complex-linear map,
with its real restriction and composition law proved explicitly.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Complex spacetime with underlying type `ℂ × (Fin 3 → ℂ)`. -/
abbrev ComplexSpacetime := ℂ × (Fin 3 → ℂ)

/-- Linear map for the complex spacetime of real, of type `Spacetime →ₗ[ℝ] ComplexSpacetime where
toFun x`. -/
noncomputable def complexSpacetimeOfReal : Spacetime →ₗ[ℝ] ComplexSpacetime where
  toFun x := ((x.1 : ℂ), fun i => (x.2 i : ℂ))
  map_add' x y := by ext <;> simp [Complex.ofReal_add]
  map_smul' a x := by ext <;> simp [Complex.ofReal_mul, Complex.real_smul]

theorem spacetime_coordinate_expansion (x : Spacetime) :
    x = x.1 • coordDir 0 + ∑ i : Fin 3, x.2 i • coordDir i.succ := by
  apply Prod.ext
  · simp [Fin.sum_univ_three, coordDir_zero, coordDir_succ]
  · ext i
    fin_cases i <;> simp [Fin.sum_univ_three, coordDir_zero, coordDir_succ]

/-- Complexified spacetime map of type `ComplexSpacetime →L[ℂ] ComplexSpacetime`. -/
noncomputable def complexifiedSpacetimeMap (Λ : Spacetime ≃L[ℝ] Spacetime) :
    ComplexSpacetime →L[ℂ] ComplexSpacetime :=
  (ContinuousLinearMap.fst ℂ ℂ (Fin 3 → ℂ)).smulRight
      (complexSpacetimeOfReal (Λ (coordDir 0))) +
    ∑ i : Fin 3,
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ ℂ (Fin 3 → ℂ))).smulRight
        (complexSpacetimeOfReal (Λ (coordDir i.succ)))

theorem complexifiedSpacetimeMap_apply (Λ : Spacetime ≃L[ℝ] Spacetime)
    (z : ComplexSpacetime) :
    complexifiedSpacetimeMap Λ z =
      z.1 • complexSpacetimeOfReal (Λ (coordDir 0)) +
        ∑ i : Fin 3, z.2 i • complexSpacetimeOfReal (Λ (coordDir i.succ)) := by
  simp [complexifiedSpacetimeMap]

theorem complexifiedSpacetimeMap_ofReal (Λ : Spacetime ≃L[ℝ] Spacetime)
    (x : Spacetime) :
    complexifiedSpacetimeMap Λ (complexSpacetimeOfReal x) = complexSpacetimeOfReal (Λ x) := by
  symm
  calc
    complexSpacetimeOfReal (Λ x) = complexSpacetimeOfReal
        (Λ (x.1 • coordDir 0 + ∑ i : Fin 3, x.2 i • coordDir i.succ)) :=
      congrArg (fun y => complexSpacetimeOfReal (Λ y)) (spacetime_coordinate_expansion x)
    _ = x.1 • complexSpacetimeOfReal (Λ (coordDir 0)) +
        ∑ i : Fin 3, x.2 i • complexSpacetimeOfReal (Λ (coordDir i.succ)) := by
      simp only [map_add, map_sum, map_smul]
    _ = complexifiedSpacetimeMap Λ (complexSpacetimeOfReal x) := by
      rw [complexifiedSpacetimeMap_apply]
      simp only [complexSpacetimeOfReal, LinearMap.coe_mk, AddHom.coe_mk,
        RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rfl

theorem complexifiedSpacetimeMap_trans (Λ Γ : Spacetime ≃L[ℝ] Spacetime)
    (z : ComplexSpacetime) :
    complexifiedSpacetimeMap (Λ.trans Γ) z =
      complexifiedSpacetimeMap Γ (complexifiedSpacetimeMap Λ z) := by
  rw [complexifiedSpacetimeMap_apply Λ, map_add, map_sum]
  simp only [map_smul, complexifiedSpacetimeMap_ofReal]
  rw [complexifiedSpacetimeMap_apply]
  rfl

/-- Spatial bilinear pairing with a real position, as an actual complex dual vector. -/
noncomputable def complexSpatialPhase (x : EuclideanSpace ℝ (Fin 3)) :
    ComplexSpacetime →L[ℂ] ℂ :=
  ∑ i : Fin 3, (x i : ℂ) •
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ ℂ (Fin 3 → ℂ)))

theorem complexSpatialPhase_apply (x : EuclideanSpace ℝ (Fin 3))
    (z : ComplexSpacetime) :
    complexSpatialPhase x z = spatialDot z.2 (fun i => (x i : ℂ)) := by
  simp [complexSpatialPhase, spatialDot, mul_comm]

end VacuumBellSeparation
