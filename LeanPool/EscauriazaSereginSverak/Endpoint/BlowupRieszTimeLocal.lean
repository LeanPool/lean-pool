/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszFarVelocity

/-!
# Blowup Riesz Time Local

Pressure reconstruction and convergence bounds for the rescaled sequence.
-/

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- Restricting a tensor to a measurable time set does not change its Riesz
pressure on that set, as a space-time almost-everywhere identity. -/
theorem blowup_rieszPressureSpaceTime_time_indicator_ae
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (J : Set ℝ) (hJ : MeasurableSet J) :
    let S : Set (Vec3 × ℝ) := Set.univ ×ˢ J
    let G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
      fun i j => S.indicator (F i j)
    let hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) :=
        fun i j => (hF i j).indicator
          (MeasurableSet.univ.prod hJ)
    S.indicator (CKN.Leray.rieszPressureSpaceTime
      (3 / 2 : ℝ) (by norm_num) F hF) =ᵐ[volume]
      S.indicator (CKN.Leray.rieszPressureSpaceTime
        (3 / 2 : ℝ) (by norm_num) G hG) := by
  let : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
  let S : Set (Vec3 × ℝ) := Set.univ ×ˢ J
  have hS : MeasurableSet S := MeasurableSet.univ.prod hJ
  let G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => S.indicator (F i j)
  let hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (3 / 2 : ℝ))
    (volume : Measure (Vec3 × ℝ)) := fun i j => (hF i j).indicator hS
  let PF := CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF
  let PG := CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) G hG
  have hSliceF := ae_restrict_of_ae (s := J)
    (CKN.Leray.rieszPressureSpaceTime_slice_ae_eq
      (3 / 2 : ℝ) (by norm_num) F hF)
  have hSliceG := ae_restrict_of_ae (s := J)
    (CKN.Leray.rieszPressureSpaceTime_slice_ae_eq
      (3 / 2 : ℝ) (by norm_num) G hG)
  have hSectionJ : ∀ᵐ t ∂(volume : Measure ℝ).restrict J,
      (fun x : Vec3 => PF (x,t)) =ᵐ[volume]
        fun x : Vec3 => PG (x,t) := by
    filter_upwards [hSliceF, hSliceG, self_mem_ae_restrict hJ] with
      t ⟨hFt, hPF⟩ ⟨hGt, hPG⟩ htJ
    have hinput (i j : Fin 3) :
        (hFt i j).toLp (fun x : Vec3 => F i j (x,t)) =
          (hGt i j).toLp (fun x : Vec3 => G i j (x,t)) := by
      apply MemLp.toLp_congr
      filter_upwards [] with x
      exact (Set.indicator_of_mem (show (x,t) ∈ S from ⟨Set.mem_univ _, htJ⟩)
        (F i j)).symm
    have hclass : CKN.Leray.rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
        (fun i j => (hFt i j).toLp (fun x : Vec3 => F i j (x,t))) =
      CKN.Leray.rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
        (fun i j => (hGt i j).toLp (fun x : Vec3 => G i j (x,t))) := by
      congr 1
      funext i j
      exact hinput i j
    filter_upwards [hPF, hPG] with x hf hg
    exact hf.trans ((congrArg (fun q : Lp ℝ
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure Vec3) =>
        (q : Vec3 → ℝ) x) hclass).trans hg.symm)
  have hSection : ∀ᵐ t ∂(volume : Measure ℝ),
      (fun x : Vec3 => S.indicator PF (x,t)) =ᵐ[volume]
        fun x : Vec3 => S.indicator PG (x,t) := by
    have hImp := (ae_restrict_iff' hJ).mp hSectionJ
    filter_upwards [hImp] with t ht
    by_cases htJ : t ∈ J
    · filter_upwards [ht htJ] with x hx
      simp only [Set.indicator_of_mem (show (x,t) ∈ S from ⟨Set.mem_univ _, htJ⟩)]
      exact hx
    · filter_upwards [] with x
      have hx : (x,t) ∉ S := fun hm => htJ hm.2
      simp only [Set.indicator_of_notMem hx]
  have hPFmeas : Measurable PF :=
    CKN.Leray.rieszPressureSpaceTime_measurable (3 / 2 : ℝ)
      (by norm_num) F hF
  have hPGmeas : Measurable PG :=
    CKN.Leray.rieszPressureSpaceTime_measurable (3 / 2 : ℝ)
      (by norm_num) G hG
  exact CKN.Leray.ae_eq_of_ae_time_sections
    (hPFmeas.indicator hS) (hPGmeas.indicator hS) hSection

end ESS
