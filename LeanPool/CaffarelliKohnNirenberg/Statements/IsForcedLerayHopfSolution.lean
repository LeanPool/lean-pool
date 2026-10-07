/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.IsInJ
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.TestFunction
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradient
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Is Forced Leray Hopf Solution

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The finite-time forced Leray--Hopf conditions from `def:forced-leray-hopf`.
The shared time representative satisfies the energy class, weak continuity,
and initial trace clauses of `def:leray-hopf`, together with the forced
momentum and work inequalities. -/
@[expose]
def IsForcedLerayHopfSolution (T : ℝ) (a : Vec3 → Vec3)
    (f : ParabolicPoint → Vec3) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) : Prop :=
  0 < T ∧
    IsInJ a ∧
    MemLp f (2 : ℝ≥0∞)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
    AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
    AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
    essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤ ∧
    (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
    (∀ᵐ s ∂(volume.restrict (Ioo 0 T)), ∀ i : Fin 3,
      HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => u (x, s) i) (fun x => Du (x, s) i)) ∧
    (∀ᵐ s ∂(volume.restrict (Ioo 0 T)),
      ∀ ψ : WeakTestFunction (Set.univ : Set Vec3),
        ∫ x : Vec3, ∑ i : Fin 3, u (x, s) i * ψ.partialDeriv i x = 0) ∧
    (∀ w : Vec3 → Vec3, MemLp w (2 : ℝ≥0∞) volume →
      ContinuousOn
        (fun t : ℝ => ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i)
        (Icc 0 T)) ∧
    (∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
      (∀ z : ParabolicPoint,
        ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z = 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - ∑ i : Fin 3, f z i * φ z i = 0) ∧
    (∀ t₀ : ℝ, t₀ ∈ Icc 0 T →
      (ENNReal.ofReal (1 / 2 : ℝ) *
          (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀))) ^ (2 : ℝ))
        + ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
            ENNReal.ofReal (spatialGradientSq u Du z)) < ⊤ ∧
      ((ENNReal.ofReal (1 / 2 : ℝ) *
          (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀))) ^ (2 : ℝ))
        + ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
            ENNReal.ofReal (spatialGradientSq u Du z))).toReal ≤
        ((ENNReal.ofReal (1 / 2 : ℝ) *
          (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ)))).toReal +
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
            ∑ i : Fin 3, f z i * u z i) ∧
    Tendsto
      (fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t) - a x)) ^ (2 : ℝ))
      (nhdsWithin 0 (Ioi 0)) (nhds 0)

end CKN
