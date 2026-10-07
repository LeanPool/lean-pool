/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortDensityContinuity
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortExtendedEnergy
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShiftedCellCover
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortAverageBox

/-!
# Local integrability of weighted cell energy

Bounded scalar factors preserve the local quadratic energy integral on
cell fragments in the high normal strip.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Extended local quadratic data make the rescaled energy integrable
on each shifted dyadic cell fragment in the high strip. -/
theorem bu_short_cell_fragment_energy_integrable
    (scale : ℝ) (hscale : 0 < scale)
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048)
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
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    IntegrableOn (fun z =>
      vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z)
      (buShortShiftedDyadicCell k m ell ∩ buShortHighStrip scale)
      volume := by
  let Cell := buShortShiftedDyadicCell k m ell
  let S := Cell ∩ buShortHighStrip scale
  let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
  let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
  have hδ : 0 < δ :=
    (half_pos (Foundation.buSmallTimeDyadicScale_pos k)).trans
      (bu_short_dyadic_cell_center_time_bounds k m ell).1
  have hSub : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo (1 / 2 : ℝ) (3 / 2)) := by
    intro z hz
    have hp := bu_short_high_strip_subset_positive scale hscale hz.2
    exact ⟨hp.1, ⟨hz.2.2.1, hz.2.2.2.trans (by norm_num)⟩⟩
  have hBound : Bornology.IsBounded S := by
    apply (bu_short_average_box_bounded Y δ hδ).subset
    intro z hz
    exact bu_short_shifted_dyadic_cell_average k m ell hz.1
  have hInts := bu_short_extended_energy_integrable_on hweak hlocal S hSub hBound
  exact hInts.1.add hInts.2

/-- A continuous scalar factor bounded on the cell fragment multiplies
its locally integrable quadratic energy (`lem:bu-small-time`). -/
theorem bu_short_cell_fragment_density_integrable
    (scale : ℝ) (hscale : 0 < scale)
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048)
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
    (W : ParabolicPoint → ℝ)
    (hWcont : ContinuousOn W
      {z : ParabolicPoint | 0 < z.1 2 ∧ 0 < z.2})
    (C : ℝ) (hWbound : ∀ z ∈
      buShortShiftedDyadicCell k m ell ∩ buShortHighStrip scale,
      ‖W z‖ ≤ C) :
    IntegrableOn (fun z => W z *
      (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z))
      (buShortShiftedDyadicCell k m ell ∩ buShortHighStrip scale)
      volume := by
  let S := buShortShiftedDyadicCell k m ell ∩ buShortHighStrip scale
  have hS : MeasurableSet S :=
    (bu_short_shifted_dyadic_cell_measurable k m ell).inter
      (buShortHighStrip_measurable scale)
  have hSpos : S ⊆ {z : ParabolicPoint | 0 < z.1 2 ∧ 0 < z.2} := by
    intro z hz
    exact bu_short_high_strip_subset_positive scale hscale hz.2
  exact bu_short_integrable_mul_bounded_on S hS _ W
    (bu_short_cell_fragment_energy_integrable scale hscale k m ell hweak hlocal)
    (hWcont.mono hSpos) C hWbound

end ESS
