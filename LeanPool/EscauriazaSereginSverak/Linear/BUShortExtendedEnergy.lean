/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellCaccioppoli
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEnergyL2

/-!
# Local integrability of extended quadratic energy

The local full square-integrability hypothesis makes velocity and
gradient energies integrable on each bounded cylinder.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Full local quadratic data imply integrability of velocity and
spatial-gradient energies on each bounded subset of the extended domain. -/
theorem bu_short_extended_energy_integrable_on
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2}
      (Ioo (1 / 2 : ℝ) (3 / 2)) v Dv D2v Dtv)
    (hlocal : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (1 / 2 : ℝ) (3 / 2)) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
    (S : Set ParabolicPoint)
    (hS : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo (1 / 2 : ℝ) (3 / 2)))
    (hSb : Bornology.IsBounded S) :
    IntegrableOn (fun z => vec3EuclideanNorm (v z) ^ 2) S volume ∧
      IntegrableOn (fun z => spatialGradientSq v Dv z) S volume := by
  have hfull := hlocal S hS hSb
  have hVfin : (∫⁻ z in S, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply (lintegral_mono ?_).trans_lt hfull
    intro z
    exact le_add_of_nonneg_right (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity) |>.trans
        (le_add_of_nonneg_right (by positivity)))
  have hDvfin : (∫⁻ z in S, ‖Dv z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply (lintegral_mono ?_).trans_lt hfull
    intro z
    exact le_add_of_nonneg_left (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity) |>.trans
        (le_add_of_nonneg_right (by positivity)))
  have hVloc := hweak.1.mono_set hS
  have hDvloc := hweak.2.1.mono_set hS
  have hVmem : MemLp v 2 (volume.restrict S) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (μ := volume.restrict S)
      (by norm_num) (by norm_num)
      hVloc.aestronglyMeasurable).2
    simpa using hVfin
  have hDvmem : MemLp Dv 2 (volume.restrict S) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (μ := volume.restrict S)
      (by norm_num) (by norm_num)
      hDvloc.aestronglyMeasurable).2
    simpa using hDvfin
  exact bu_memLp_quadratic_energy_integrable S v Dv hVmem hDvmem

end ESS
