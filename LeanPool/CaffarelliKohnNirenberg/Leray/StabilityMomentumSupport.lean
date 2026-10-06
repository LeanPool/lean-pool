/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityDivergenceSupport
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MomentumIntegrand

/-!
# Stability Momentum Support

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- A weak momentum test has the same pairing on the whole carrier and on
any local box containing its compact support. -/
theorem stability_momentum_integral_eq_localBox
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (φ : Vec3 × ℝ → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I)
    (hKbox : tsupport (show ParabolicPoint → Vec3 from φ) ⊆
      spaceTimeSet Ω' J)
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) :
    (∫ z in spaceTimeSet Ω I,
      (-(∑ i, u z i * timePartial (fun w => φ w i) z))
        - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
        + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
        - p z * ∑ i, spatialPartial (fun w => φ w i) i z
        - ∑ i, (0 : ParabolicPoint → Vec3) z i * φ z i) =
    ∫ z in spaceTimeSet Ω' J,
      (-(∑ i, u z i * timePartial (fun w => φ w i) z))
        - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
        + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
        - p z * ∑ i, spatialPartial (fun w => φ w i) i z
        - ∑ i, (0 : ParabolicPoint → Vec3) z i * φ z i := by
  let F : ParabolicPoint → ℝ := fun z =>
    (-(∑ i, u z i * timePartial (fun w => φ w i) z))
      - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
      + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
      - p z * ∑ i, spatialPartial (fun w => φ w i) i z
      - ∑ i, (0 : ParabolicPoint → Vec3) z i * φ z i
  have hzero {z : ParabolicPoint}
      (hz : z ∉ tsupport (show ParabolicPoint → Vec3 from φ)) : F z = 0 := by
    have hzprod : (z : Vec3 × ℝ) ∉ tsupport φ := by
      intro hmem
      apply hz
      rw [tsupport_parabolic_eq]
      exact hmem
    have hzcomp (i : Fin 3) :
        (z : Vec3 × ℝ) ∉ tsupport (fun w => φ w i) := by
      intro hmem
      exact hzprod ((tsupport_component_subset φ i
        (fun _ h => by rw [h]; rfl)) hmem)
    have htime (i : Fin 3) : timePartial (fun w => φ w i) z = 0 :=
      timePartial_eq_zero_off_tsupport (hzcomp i)
    have hspace (i j : Fin 3) :
        spatialPartial (fun w => φ w i) j z = 0 :=
      spatialPartial_eq_zero_off_tsupport (hzcomp i) j
    simp [F, htime, hspace]
  have hglob : ∫ z in spaceTimeSet Ω I, F z = ∫ z, F z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    exact hzero (fun hmem => hz (tsupport_parabolic_subset_spaceTimeSet hφ hmem))
  have hloc : ∫ z in spaceTimeSet Ω' J, F z = ∫ z, F z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    exact hzero (fun hmem => hz (hKbox hmem))
  exact hglob.trans hloc.symm

end CKN
