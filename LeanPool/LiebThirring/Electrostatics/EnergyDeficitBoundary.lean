/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitGeometry
public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitIdentity

/-!
# Directed boundary expression for the nearest-nucleus deficit

The nearest-distance factor turns outward inverse-cubic flux into inverse-fourth flux.

The half nearest-charge integral has exactly the `Z²/(8π)` directed coefficient.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LiebThirring

/-- The nearest-distance factor turns outward inverse-cubic flux into inverse-fourth flux. -/
theorem nearestKernel_mul_faceFlux {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) {k l : Fin M} {y : Position}
    (hy : y ∈ voronoiFace R k l) :
    (nearestNucleusDistance R y)⁻¹ * ENNReal.ofReal (nuclearFaceFlux R k l y) =
      ENNReal.ofReal (nuclearHalfDistance R k l / ‖y - R k‖ ^ 4) := by
  have ha := nuclearHalfDistance_pos R hR hy.1
  have hr : 0 < ‖y - R k‖ :=
    ha.trans_le (nuclearHalfDistance_le_norm_on_bisector R hR hy.1 hy.2.1)
  rw [nearestNucleusDistance_eq_of_mem_voronoiFace R hy,
    nuclearFaceFlux_on_face R hR hy, ← ENNReal.ofReal_inv_of_pos hr,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
  congr 1
  field_simp

/-- The half nearest-charge integral has exactly the `Z²/(8π)` directed coefficient. -/
theorem half_nearestIntegral_eq_directed_inverse_fourth {M : ℕ}
    (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R) :
    (∫⁻ y, (Z : ℝ≥0∞) * (nearestNucleusDistance R y)⁻¹
      ∂voronoiFaceMeasure R hR (Z : ℝ)) / 2 =
      ENNReal.ofReal ((Z : ℝ) ^ 2 / (8 * Real.pi)) *
        ∑ k : Fin M, ∑ l : {l : Fin M // l ≠ k},
          ∫⁻ y in voronoiFace R k l.val,
            ENNReal.ofReal (nuclearHalfDistance R k l.val / ‖y - R k‖ ^ 4)
            ∂bisectorSurfaceMeasure R hR k l.val l.property.symm := by
  have hm : Measurable (fun y : Position => (nearestNucleusDistance R y)⁻¹) :=
    (measurable_nearestNucleusDistance R).inv
  rw [lintegral_const_mul _ hm]
  have hdir := lintegral_voronoiFaceMeasure_directed R hR (NNReal.coe_nonneg Z)
    (fun y => (nearestNucleusDistance R y)⁻¹) hm
  change (∫⁻ y, (nearestNucleusDistance R y)⁻¹ ∂voronoiFaceMeasure R hR (Z : ℝ)) = _ at hdir
  rw [hdir]
  have hb (k : Fin M) (l : {l : Fin M // l ≠ k}) :
      (∫⁻ y in voronoiFace R k l.val,
        (nearestNucleusDistance R y)⁻¹ *
          ENNReal.ofReal (inner ℝ (bisectorNormal R k l.val) (y - R k) / ‖y - R k‖ ^ 3)
        ∂bisectorSurfaceMeasure R hR k l.val l.property.symm) =
      ∫⁻ y in voronoiFace R k l.val,
        ENNReal.ofReal (nuclearHalfDistance R k l.val / ‖y - R k‖ ^ 4)
        ∂bisectorSurfaceMeasure R hR k l.val l.property.symm := by
    exact setLIntegral_congr_fun (measurableSet_voronoiFace R k l.val)
      fun y hy => nearestKernel_mul_faceFlux R hR hy
  simp_rw [hb]
  rw [← mul_assoc, ENNReal.mul_div_right_comm]
  congr 1
  have hz : (Z : ℝ≥0∞) = ENNReal.ofReal (Z : ℝ) := ENNReal.coe_nnreal_eq Z
  rw [hz, ← ENNReal.ofReal_mul (NNReal.coe_nonneg Z), ← ENNReal.ofReal_ofNat (n := 2),
    ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  field_simp
  ring

/-- Exact energy normalization with the directed boundary integral, conditional only on the
potential identity. -/
theorem half_energy_add_directed_boundary_eq_repulsion_of_potential_eq {M : ℕ}
    (hM : 1 ≤ M) (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (hPhi : ∀ x, screenedPotential Z R x =
      coulombPotential (voronoiFaceMeasure R hR (Z : ℝ)) x) :
    coulombEnergy (voronoiFaceMeasure R hR (Z : ℝ)) (voronoiFaceMeasure R hR (Z : ℝ)) / 2 +
      ENNReal.ofReal ((Z : ℝ) ^ 2 / (8 * Real.pi)) *
        (∑ k : Fin M, ∑ l : {l : Fin M // l ≠ k},
          ∫⁻ y in voronoiFace R k l.val,
            ENNReal.ofReal (nuclearHalfDistance R k l.val / ‖y - R k‖ ^ 4)
            ∂bisectorSurfaceMeasure R hR k l.val l.property.symm) =
      nuclearRepulsion (fun _ => Z) R := by
  rw [← half_nearestIntegral_eq_directed_inverse_fourth]
  exact half_energy_add_half_nearestIntegral_eq_repulsion_of_potential_eq hM Z R hR hPhi

end LiebThirring

end
