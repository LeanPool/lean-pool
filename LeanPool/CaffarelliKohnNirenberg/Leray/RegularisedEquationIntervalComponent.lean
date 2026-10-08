/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationIntervalWeak
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis

/-!
# Regularised Equation Interval Component

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Testing the vector weak momentum identity against a single-coordinate
field gives the corresponding scalar weak identity. -/
theorem regularisedInterval_scalarWeakMomentum_of_vector
    (T : ℝ) (u J : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Fin 3 → ℝ) (P : ParabolicPoint → ℝ)
    (hWeak : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (Set.univ : Set Vec3) (Set.Ioo 0 T) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T),
        (-(∑ k : Fin 3, u z k * timePartial (fun y => φ y k) z)
          - ∑ k : Fin 3, ∑ j : Fin 3,
            J z j * u z k * spatialPartial (fun y => φ y k) j z
          + ∑ k : Fin 3, ∑ j : Fin 3,
            D z k j * spatialPartial (fun y => φ y k) j z
          - P z * (∑ k : Fin 3, spatialPartial (fun y => φ y k) k z)) = 0)
    (i : Fin 3) (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (Set.univ : Set Vec3) (Set.Ioo 0 T)) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T),
      (-(u z i * timePartial ψ z)
        - ∑ j : Fin 3, J z j * u z i * spatialPartial ψ j z
        + ∑ j : Fin 3, D z i j * spatialPartial ψ j z
        - P z * spatialPartial ψ i z) = 0 := by
  classical
  let ψProd : Vec3 × ℝ → ℝ := fun z => ψ z
  let φProd : Vec3 × ℝ → Vec3 := fun z => ψProd z • CKN.basisVec i
  let φ : ParabolicPoint → Vec3 := fun z => φProd z
  have hφProd : φProd ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Set.Ioo 0 T) := by
    refine ⟨?_, ?_, ?_⟩
    · have heq : (fun z : Vec3 × ℝ => ψProd z • CKN.basisVec i) =
          ψProd • fun _ : Vec3 × ℝ => CKN.basisVec i := by
        funext z
        rfl
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Vec3 × ℝ => ψProd z • CKN.basisVec i)
      rw [heq]
      simpa [ψProd] using hψ.1.smul contDiff_const
    · exact hψ.2.1.smul_right
    · exact (tsupport_smul_subset_left ψProd (fun _ => CKN.basisVec i)).trans
        hψ.2.2
  have hφ : φ ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Set.Ioo 0 T) := by
    change φProd ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Set.Ioo 0 T)
    exact hφProd
  have h := hWeak φ hφ
  have hComp (k : Fin 3) : (fun z : ParabolicPoint => φ z k) =
      fun z => if k = i then ψ z else 0 := by
    funext z
    simp [φ, φProd, ψProd, CKN.basisVec, Pi.single_apply]
  have hTime (k : Fin 3) (z : ParabolicPoint) :
      timePartial (fun y : ParabolicPoint => φ y k) z =
        if k = i then timePartial ψ z else 0 := by
    rw [hComp k]
    by_cases hk : k = i
    · simp [hk]
    · simp [hk, timePartial]
  have hSpace (k j : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun y : ParabolicPoint => φ y k) j z =
        if k = i then spatialPartial ψ j z else 0 := by
    rw [hComp k]
    by_cases hk : k = i
    · simp [hk]
    · simp [hk, spatialPartial]
  simp_rw [hTime, hSpace] at h
  simpa [Finset.sum_ite_eq', Finset.sum_ite_irrel] using h

end CKN.Leray
