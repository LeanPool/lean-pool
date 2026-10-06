/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszFarBound

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- The canonical space-time Riesz pressure is additive as an almost-everywhere
defined function of its tensor input. -/
theorem blowup_rieszPressureSpaceTime_add_ae
    (F G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ))) :
    let H : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
      fun i j z => F i j z + G i j z
    let hH : ∀ i j, MemLp (H i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := fun i j => (hF i j).add (hG i j)
    CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) H hH =ᵐ[volume]
      fun z => CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ)
          (by norm_num) F hF z +
        CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ)
          (by norm_num) G hG z := by
  let : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
  let H : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
    fun i j z => F i j z + G i j z
  let hH : ∀ i j, MemLp (H i j) (ENNReal.ofReal (3 / 2 : ℝ))
    (volume : Measure (Vec3 × ℝ)) := fun i j => (hF i j).add (hG i j)
  let PF := CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF
  let PG := CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) G hG
  let PH := CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) H hH
  let CF := CKN.Leray.rieszPressureSpaceTimeClass (3 / 2 : ℝ) (by norm_num)
    (CKN.Leray.rieszPressureSpaceTimeTensorToLp (3 / 2 : ℝ) (by norm_num) F hF)
  let CG := CKN.Leray.rieszPressureSpaceTimeClass (3 / 2 : ℝ) (by norm_num)
    (CKN.Leray.rieszPressureSpaceTimeTensorToLp (3 / 2 : ℝ) (by norm_num) G hG)
  let CH := CKN.Leray.rieszPressureSpaceTimeClass (3 / 2 : ℝ) (by norm_num)
    (CKN.Leray.rieszPressureSpaceTimeTensorToLp (3 / 2 : ℝ) (by norm_num) H hH)
  have hclass : CH = CF + CG := by
    dsimp [CH, CF, CG, CKN.Leray.rieszPressureSpaceTimeClass,
      CKN.Leray.rieszPressureSpaceTimeTensorToLp]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← map_add]
    congr 1
  have hFae : PF =ᵐ[volume] (CF : Vec3 × ℝ → ℝ) := by
    exact (Lp.aestronglyMeasurable CF).aemeasurable.ae_eq_mk.symm
  have hGae : PG =ᵐ[volume] (CG : Vec3 × ℝ → ℝ) := by
    exact (Lp.aestronglyMeasurable CG).aemeasurable.ae_eq_mk.symm
  have hHae : PH =ᵐ[volume] (CH : Vec3 × ℝ → ℝ) := by
    exact (Lp.aestronglyMeasurable CH).aemeasurable.ae_eq_mk.symm
  filter_upwards [hFae, hGae, hHae, Lp.coeFn_add CF CG] with z hf hg hh hadd
  dsimp [PH, PF, PG] at *
  calc
    CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) H hH z =
      (CH : Vec3 × ℝ → ℝ) z := hh
    _ = ((CF + CG : Lp ℝ (ENNReal.ofReal (3 / 2 : ℝ))
        (volume : Measure (Vec3 × ℝ))) : Vec3 × ℝ → ℝ) z := by rw [hclass]
    _ = (CF : Vec3 × ℝ → ℝ) z + (CG : Vec3 × ℝ → ℝ) z := hadd
    _ = _ := by rw [hf, hg]

end ESS
