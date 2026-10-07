/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureSpaceTimeCore

/-!
# Space-time pressure on `L^r`

This file sums the nine bounded component operators and chooses a measurable
representative of their space-time pressure.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- A tensor of space-time `L^r` classes, used by `def:riesz-pressure`. -/
abbrev RieszPressureSpaceTimeTensorLp (r : ℝ) :=
  Fin 3 → Fin 3 → Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))

/-- The space-time pressure class formed from the nine double Riesz transforms,
used by `def:riesz-pressure`. -/
@[expose]
def rieszPressureSpaceTimeClass (r : ℝ) (hr : 1 < r)
    (F : RieszPressureSpaceTimeTensorLp r) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) := by
  letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  exact ∑ i : Fin 3, ∑ j : Fin 3, rieszPressureSpaceTimeComponent r hr i j (F i j)

/-- A jointly measurable representative of the space-time pressure class,
used by `def:riesz-pressure`. -/
@[expose]
def rieszPressureSpaceTimeRepresentative (r : ℝ) (hr : 1 < r)
    (F : RieszPressureSpaceTimeTensorLp r) : Vec3 × ℝ → ℝ := by
  letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  exact (Lp.aestronglyMeasurable (rieszPressureSpaceTimeClass r hr F)).aemeasurable.mk
    (rieszPressureSpaceTimeClass r hr F)

/-- The representative selected for space-time pressure is measurable,
used by `def:riesz-pressure`. -/
theorem rieszPressureSpaceTimeRepresentative_measurable (r : ℝ) (hr : 1 < r)
    (F : RieszPressureSpaceTimeTensorLp r) :
    Measurable (rieszPressureSpaceTimeRepresentative r hr F) := by
  exact (Lp.aestronglyMeasurable (rieszPressureSpaceTimeClass r hr F)).aemeasurable.measurable_mk

/-- The space-time pressure representative belongs to `L^r`, used by
`def:riesz-pressure`. -/
theorem rieszPressureSpaceTimeRepresentative_memLp (r : ℝ) (hr : 1 < r)
    (F : RieszPressureSpaceTimeTensorLp r) :
    MemLp (rieszPressureSpaceTimeRepresentative r hr F) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)) := by
  have hAE := (Lp.aestronglyMeasurable (rieszPressureSpaceTimeClass r hr F)).aemeasurable.ae_eq_mk
  exact (memLp_congr_ae hAE.symm).2 (Lp.memLp (rieszPressureSpaceTimeClass r hr F))

/-- The nine component bounds give the space-time `L^r` bound, used by
`eq:riesz-spacetime-bound`. -/
theorem rieszPressureSpaceTimeClass_norm_le (r : ℝ) (hr : 1 < r)
    (F : RieszPressureSpaceTimeTensorLp r) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    ‖rieszPressureSpaceTimeClass r hr F‖ ≤
      rieszPressureOperatorBound r hr * ∑ i : Fin 3, ∑ j : Fin 3, ‖F i j‖ := by
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  calc
    ‖rieszPressureSpaceTimeClass r hr F‖ ≤
        ∑ i : Fin 3, ∑ j : Fin 3,
          ‖rieszPressureSpaceTimeComponent r hr i j (F i j)‖ := by
      dsimp [rieszPressureSpaceTimeClass]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          rieszPressureOperatorBound r hr * ‖F i j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      calc
        ‖rieszPressureSpaceTimeComponent r hr i j (F i j)‖ ≤
            ‖rieszPressureSpaceTimeComponent r hr i j‖ * ‖F i j‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ rieszPressureOperatorBound r hr * ‖F i j‖ :=
          mul_le_mul_of_nonneg_right (rieszPressureSpaceTimeComponent_norm_le r hr i j)
            (norm_nonneg _)
    _ = rieszPressureOperatorBound r hr *
          ∑ i : Fin 3, ∑ j : Fin 3, ‖F i j‖ := by
      simp only [Finset.mul_sum]

/-- Convert a jointly measurable tensor with `L^r` space-time components to
its canonical tensor of `L^r` classes, used by `def:riesz-pressure`. -/
@[expose]
def rieszPressureSpaceTimeTensorToLp (r : ℝ) (_hr : 1 < r)
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ))) : RieszPressureSpaceTimeTensorLp r := by
  letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal _hr.le⟩
  exact fun i j => (hF i j).toLp (F i j)

/-- For a raw tensor with space-time `L^r` components, the pressure class
obeys `eq:riesz-spacetime-bound` in the corresponding `L^r` norms. -/
theorem rieszPressureSpaceTime_bound (r : ℝ) (hr : 1 < r)
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ))) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    ‖rieszPressureSpaceTimeClass r hr (rieszPressureSpaceTimeTensorToLp r hr F hF)‖ ≤
      rieszPressureOperatorBound r hr * ∑ i : Fin 3, ∑ j : Fin 3,
        ‖(hF i j).toLp (F i j)‖ := by
  exact rieszPressureSpaceTimeClass_norm_le r hr
    (rieszPressureSpaceTimeTensorToLp r hr F hF)

/-- The jointly measurable pressure associated with a tensor whose components
belong to space-time `L^r`, used by `def:riesz-pressure`. -/
@[expose]
def rieszPressureSpaceTime (r : ℝ) (hr : 1 < r)
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ))) : Vec3 × ℝ → ℝ :=
  rieszPressureSpaceTimeRepresentative r hr (rieszPressureSpaceTimeTensorToLp r hr F hF)

/-- The function-valued space-time pressure is measurable, used by
`def:riesz-pressure`. -/
theorem rieszPressureSpaceTime_measurable (r : ℝ) (hr : 1 < r)
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ))) :
    Measurable (rieszPressureSpaceTime r hr F hF) :=
  rieszPressureSpaceTimeRepresentative_measurable r hr
    (rieszPressureSpaceTimeTensorToLp r hr F hF)

/-- The function-valued space-time pressure belongs to `L^r`, used by
`def:riesz-pressure`. -/
theorem rieszPressureSpaceTime_memLp (r : ℝ) (hr : 1 < r)
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ))) :
    MemLp (rieszPressureSpaceTime r hr F hF) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)) :=
  rieszPressureSpaceTimeRepresentative_memLp r hr
    (rieszPressureSpaceTimeTensorToLp r hr F hF)

end CKN.Leray

end
