/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

/-!
# Stability Divergence Support

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- A compactly supported divergence pairing has the same integral on the
whole carrier and on any local box containing the test support. -/
theorem stability_divergence_integral_eq_localBox
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hKbox : tsupport (show ParabolicPoint → ℝ from ψ) ⊆
      spaceTimeSet Ω' J)
    (f : ParabolicPoint → Vec3) :
    (∫ z in spaceTimeSet Ω I,
      ∑ i : Fin 3, f z i * spatialPartial ψ i z) =
    ∫ z in spaceTimeSet Ω' J,
      ∑ i : Fin 3, f z i * spatialPartial ψ i z := by
  let F : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, f z i * spatialPartial ψ i z
  have hzero {z : ParabolicPoint}
      (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ)) : F z = 0 := by
    have hz' : (z : Vec3 × ℝ) ∉ tsupport ψ := by
      intro hmem
      apply hz
      rw [tsupport_parabolic_eq]
      exact hmem
    exact Finset.sum_eq_zero fun i _ => by
      rw [spatialPartial_eq_zero_off_tsupport hz' i, mul_zero]
  have hglob : ∫ z in spaceTimeSet Ω I, F z = ∫ z, F z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    exact hzero (fun hmem => hz (tsupport_parabolic_subset_spaceTimeSet hψ hmem))
  have hloc : ∫ z in spaceTimeSet Ω' J, F z = ∫ z, F z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    exact hzero (fun hmem => hz (hKbox hmem))
  exact hglob.trans hloc.symm

end CKN
