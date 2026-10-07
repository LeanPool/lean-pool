/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevBall
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Sobolev families of the components of a strong solution

`prop:lps-smoothing`: the weak first and second spatial derivatives of a strong solution
form an `L²(I; H²)` family for each velocity component.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The ordered family of a velocity component through order two: the component itself, its
first derivatives `Du z i j = ∂ⱼuᵢ` and its second derivatives `D2u z i j k = ∂ₖ∂ⱼuᵢ`. -/
@[expose] def lpsStrongFamily (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (i : Fin 3) :
    List (Fin 3) → Vec3 × ℝ → ℝ
  | [] => fun z => u z i
  | [j] => fun z => Du z i j
  | [j, k] => fun z => D2u z i j k
  | _ => fun _ => 0

/-- The weak derivatives of a strong solution form an `L²(I; H²)` family for each velocity
component (`prop:lps-smoothing`). -/
theorem lps_strong_isL2SobolevFamily {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (i : Fin 3) :
    IsL2SobolevFamilyOn 2 (Set.univ : Set Vec3) (Ioo t₀ T) (fun z => u z i)
      (lpsStrongFamily u Du D2u i) := by
  obtain ⟨-, -, -, -, hweak⟩ := hderiv
  have hcomp : ∀ (j : Fin 3), MemLp (fun z : ParabolicPoint => Du z i j) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) := by
    intro j
    exact memLp_pi_iff.mp (memLp_pi_iff.mp hDu i) j
  have hcomp2 : ∀ (j k : Fin 3), MemLp (fun z : ParabolicPoint => D2u z i j k) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))) := by
    intro j k
    exact memLp_pi_iff.mp (memLp_pi_iff.mp (memLp_pi_iff.mp hD2u i) j) k
  refine ⟨?_, ?_, ?_⟩
  · intro α hα
    match α, hα with
    | [], _ => exact memLp_pi_iff.mp hu i
    | [j], _ => exact hcomp j
    | [j, k], _ => exact hcomp2 j k
    | _ :: _ :: _ :: _, h => simp at h
  · exact Filter.EventuallyEq.rfl
  · intro α j hα φ hφ hφc hφI
    have hφ' : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo t₀ T) :=
      ⟨hφ, hφc, hφI⟩
    obtain ⟨h1, h2, -⟩ := hweak φ hφ'
    match α, hα with
    | [], _ => exact h1 i j
    | [j'], _ =>
        change ∫ p in (Set.univ : Set Vec3) ×ˢ Ioo t₀ T, Du p i j' * spatialPartial φ j p =
          -∫ p in (Set.univ : Set Vec3) ×ˢ Ioo t₀ T, D2u p i j' j * φ p
        exact h2 i j' j
    | _ :: _ :: _, h => simp at h

end ESS
