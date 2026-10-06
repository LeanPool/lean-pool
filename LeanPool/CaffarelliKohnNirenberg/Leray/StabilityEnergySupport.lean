/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityEnergyPressure
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanGaussVector

/-!
# Stability Energy Support

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The weighted gradient term has the same integral on the carrier and on
a local box containing the test support. -/
theorem stability_energy_gradient_integral_eq_localBox
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hKbox : tsupport (show ParabolicPoint → ℝ from ψ) ⊆
      spaceTimeSet Ω' J)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3) :
    (∫ z in spaceTimeSet Ω I, spatialGradientSq v Dv z * ψ z) =
      ∫ z in spaceTimeSet Ω' J, spatialGradientSq v Dv z * ψ z := by
  let F : ParabolicPoint → ℝ := fun z => spatialGradientSq v Dv z * ψ z
  have hzero {z : ParabolicPoint}
      (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ)) : F z = 0 := by
    have hψzero : ψ z = 0 := by
      by_contra hne
      exact hz (subset_tsupport _ hne)
    simp [F, hψzero]
  have hglob : ∫ z in spaceTimeSet Ω I, F z = ∫ z, F z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    exact hzero (fun hmem => hz (tsupport_parabolic_subset_spaceTimeSet hψ hmem))
  have hloc : ∫ z in spaceTimeSet Ω' J, F z = ∫ z, F z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    exact hzero (fun hmem => hz (hKbox hmem))
  exact hglob.trans hloc.symm

/-- The right side of the zero-force local energy inequality is supported
where its test is supported. -/
theorem stability_energy_rhs_integral_eq_localBox
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hKbox : tsupport (show ParabolicPoint → ℝ from ψ) ⊆
      spaceTimeSet Ω' J)
    (v : ParabolicPoint → Vec3)
    (r : ParabolicPoint → ℝ) :
    (∫ z in spaceTimeSet Ω I,
      vec3EuclideanNorm (v z) ^ 2 *
          (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
        (vec3EuclideanNorm (v z) ^ 2 + 2 * r z) *
          ∑ i, v z i * spatialPartial ψ i z +
        2 * (∑ i, (0 : ParabolicPoint → Vec3) z i * v z i) * ψ z) =
      ∫ z in spaceTimeSet Ω' J,
        vec3EuclideanNorm (v z) ^ 2 *
            (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
          (vec3EuclideanNorm (v z) ^ 2 + 2 * r z) *
            ∑ i, v z i * spatialPartial ψ i z +
          2 * (∑ i, (0 : ParabolicPoint → Vec3) z i * v z i) * ψ z := by
  let F : ParabolicPoint → ℝ := fun z =>
    vec3EuclideanNorm (v z) ^ 2 *
        (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
      (vec3EuclideanNorm (v z) ^ 2 + 2 * r z) *
        ∑ i, v z i * spatialPartial ψ i z +
      2 * (∑ i, (0 : ParabolicPoint → Vec3) z i * v z i) * ψ z
  have hzero {z : ParabolicPoint}
      (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ)) : F z = 0 := by
    have hzprod : (z : Vec3 × ℝ) ∉ tsupport ψ := by
      intro hmem
      exact hz (by rwa [tsupport_parabolic_eq])
    have htime : timePartial ψ z = 0 :=
      timePartial_eq_zero_off_tsupport hzprod
    have hspace (i : Fin 3) : spatialPartial ψ i z = 0 :=
      spatialPartial_eq_zero_off_tsupport hzprod i
    have hsecond (i : Fin 3) : spatialSecondPartial ψ i i z = 0 :=
      spatialSecondPartial_eq_zero_off_tsupport hzprod i i
    simp [F, htime, hspace, hsecond]
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
