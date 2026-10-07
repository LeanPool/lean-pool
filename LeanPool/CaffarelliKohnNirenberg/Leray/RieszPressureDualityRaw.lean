/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureDualityLp

/-!
# Function representatives in Riesz pressure duality

The measurable representative of the pressure satisfies the same pairing as
its canonical space-time `L^r` class.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The measurable space-time pressure representative satisfies the full
duality formula, used by `lem:riesz-duality`. -/
theorem rieszPressureSpaceTime_duality
    (r : ℝ) (hr : 1 < r) (q : ℝ) (hq : 1 < q)
    (hHolder : r.HolderConjugate q)
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)))
    (g : Vec3 × ℝ → ℝ)
    (hg : MemLp g (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ))) :
    ∫ z, rieszPressureSpaceTime r hr F hF z * g z =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ z, F i j z *
        (rieszPressureSpaceTimeComponent q hq j i (hg.toLp g) :
          Vec3 × ℝ → ℝ) z := by
  have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq.le⟩
  let Fclass := rieszPressureSpaceTimeTensorToLp r hr F hF
  have hPae : (rieszPressureSpaceTimeClass r hr Fclass :
      Vec3 × ℝ → ℝ) =ᵐ[volume]
      rieszPressureSpaceTimeRepresentative r hr Fclass :=
    (Lp.aestronglyMeasurable (rieszPressureSpaceTimeClass r hr Fclass)).aemeasurable.ae_eq_mk
  have hGae : ((hg.toLp g : Lp ℝ (ENNReal.ofReal q)
      (volume : Measure (Vec3 × ℝ))) : Vec3 × ℝ → ℝ) =ᵐ[volume] g :=
    hg.coeFn_toLp
  have hClass := rieszPressureSpaceTimeClass_duality r hr q hq hHolder Fclass (hg.toLp g)
  calc
    ∫ z, rieszPressureSpaceTime r hr F hF z * g z =
        ∫ z, (rieszPressureSpaceTimeClass r hr Fclass :
          Vec3 × ℝ → ℝ) z * ((hg.toLp g : Lp ℝ (ENNReal.ofReal q)
            (volume : Measure (Vec3 × ℝ))) : Vec3 × ℝ → ℝ) z := by
              apply integral_congr_ae
              filter_upwards [hPae.symm, hGae.symm] with z hP hgz
              simp only [rieszPressureSpaceTime, rieszPressureSpaceTimeRepresentative] at hP ⊢
              rw [hP, hgz]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ z,
          (Fclass i j : Vec3 × ℝ → ℝ) z *
            (rieszPressureSpaceTimeComponent q hq j i (hg.toLp g) :
              Vec3 × ℝ → ℝ) z := hClass
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ z, F i j z *
          (rieszPressureSpaceTimeComponent q hq j i (hg.toLp g) :
            Vec3 × ℝ → ℝ) z := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          apply integral_congr_ae
          have hFae := (hF i j).coeFn_toLp
          have hClassInput : Fclass i j = (hF i j).toLp (F i j) := rfl
          have hFclassAE : (Fclass i j : Vec3 × ℝ → ℝ) =ᵐ[volume] F i j := by
            rw [hClassInput]
            exact hFae
          filter_upwards [hFclassAE] with z hz
          exact congrArg (fun y : ℝ => y *
            (rieszPressureSpaceTimeComponent q hq j i (hg.toLp g) :
              Vec3 × ℝ → ℝ) z) hz

end CKN.Leray

end
