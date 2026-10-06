/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureTwoRadius

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- A time-restricted tensor is the sum of its near and exterior spatial
parts, pointwise. -/
theorem blowup_tensor_time_near_far
    (F : Vec3 × ℝ → ℝ) (L : ℝ) (J : Set ℝ) :
    (Set.univ ×ˢ J).indicator F =
      fun z => ((CKN.euclideanBall 0 L) ×ˢ J).indicator F z +
        ((CKN.euclideanBall 0 L)ᶜ ×ˢ J).indicator F z := by
  funext z
  by_cases ht : z.2 ∈ J
  · by_cases hx : z.1 ∈ CKN.euclideanBall 0 L
    · simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht, hx]
    · simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht, hx]
  · simp [Set.indicator_of_notMem, ht]

/-- The chosen pressure representative does not depend on the proof that its
tensor components belong to `L^(3/2)`. -/
theorem blowup_rieszPressureSpaceTime_congr
    {F G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hFG : F = G) :
    CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF =
      CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) G hG := by
  subst G
  rfl

/-- The Riesz pressure of a time-restricted tensor splits almost everywhere
into near and far pressures for every spatial radius. -/
theorem blowup_rieszPressure_time_near_far_ae
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (L : ℝ) (J : Set ℝ) (hJ : MeasurableSet J) :
    let S : Set (Vec3 × ℝ) := Set.univ ×ˢ J
    let A : Set (Vec3 × ℝ) := CKN.euclideanBall 0 L ×ˢ J
    let B : Set (Vec3 × ℝ) := (CKN.euclideanBall 0 L)ᶜ ×ˢ J
    let Ftime : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => S.indicator (F i j)
    let Fnear : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => A.indicator (F i j)
    let Ffar : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => B.indicator (F i j)
    let hTime : ∀ i j, MemLp (Ftime i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      fun i j => (hF i j).indicator (MeasurableSet.univ.prod hJ)
    let hNear : ∀ i j, MemLp (Fnear i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      fun i j => (hF i j).indicator ((CKN.isOpen_euclideanBall 0 L).measurableSet.prod hJ)
    let hFar : ∀ i j, MemLp (Ffar i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      fun i j => (hF i j).indicator
        ((CKN.isOpen_euclideanBall 0 L).measurableSet.compl.prod hJ)
    CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) Ftime hTime
      =ᵐ[volume]
      fun z => CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ)
          (by norm_num) Fnear hNear z +
        CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ)
          (by norm_num) Ffar hFar z := by
  let S : Set (Vec3 × ℝ) := Set.univ ×ˢ J
  let A : Set (Vec3 × ℝ) := CKN.euclideanBall 0 L ×ˢ J
  let B : Set (Vec3 × ℝ) := (CKN.euclideanBall 0 L)ᶜ ×ˢ J
  let Ftime : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => S.indicator (F i j)
  let Fnear : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => A.indicator (F i j)
  let Ffar : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => B.indicator (F i j)
  let hTime : ∀ i j, MemLp (Ftime i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    fun i j => (hF i j).indicator (MeasurableSet.univ.prod hJ)
  let hNear : ∀ i j, MemLp (Fnear i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    fun i j => (hF i j).indicator ((CKN.isOpen_euclideanBall 0 L).measurableSet.prod hJ)
  let hFar : ∀ i j, MemLp (Ffar i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    fun i j => (hF i j).indicator
      ((CKN.isOpen_euclideanBall 0 L).measurableSet.compl.prod hJ)
  let H : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
    fun i j z => Fnear i j z + Ffar i j z
  let hH : ∀ i j, MemLp (H i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    fun i j => (hNear i j).add (hFar i j)
  have hTensor : H = Ftime := by
    funext i j
    exact (blowup_tensor_time_near_far (F i j) L J).symm
  have hPressure : CKN.Leray.rieszPressureSpaceTime
      (3 / 2 : ℝ) (by norm_num) H hH =
      CKN.Leray.rieszPressureSpaceTime
        (3 / 2 : ℝ) (by norm_num) Ftime hTime :=
    blowup_rieszPressureSpaceTime_congr hH hTime hTensor
  change CKN.Leray.rieszPressureSpaceTime
      (3 / 2 : ℝ) (by norm_num) Ftime hTime =ᵐ[volume]
    fun z => CKN.Leray.rieszPressureSpaceTime
        (3 / 2 : ℝ) (by norm_num) Fnear hNear z +
      CKN.Leray.rieszPressureSpaceTime
        (3 / 2 : ℝ) (by norm_num) Ffar hFar z
  rw [← hPressure]
  exact blowup_rieszPressureSpaceTime_add_ae Fnear Ffar hNear hFar

/-- On a fixed time set, the full Riesz pressure equals the sum of the near
and exterior pressures. -/
theorem blowup_rieszPressure_full_near_far_on_time_ae
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (L : ℝ) (J : Set ℝ) (hJ : MeasurableSet J) :
    let S : Set (Vec3 × ℝ) := Set.univ ×ˢ J
    let A : Set (Vec3 × ℝ) := CKN.euclideanBall 0 L ×ˢ J
    let B : Set (Vec3 × ℝ) := (CKN.euclideanBall 0 L)ᶜ ×ˢ J
    let Fnear : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => A.indicator (F i j)
    let Ffar : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => B.indicator (F i j)
    let hNear : ∀ i j, MemLp (Fnear i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      fun i j => (hF i j).indicator ((CKN.isOpen_euclideanBall 0 L).measurableSet.prod hJ)
    let hFar : ∀ i j, MemLp (Ffar i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      fun i j => (hF i j).indicator
        ((CKN.isOpen_euclideanBall 0 L).measurableSet.compl.prod hJ)
    S.indicator (CKN.Leray.rieszPressureSpaceTime
      (3 / 2 : ℝ) (by norm_num) F hF) =ᵐ[volume]
      S.indicator (fun z => CKN.Leray.rieszPressureSpaceTime
          (3 / 2 : ℝ) (by norm_num) Fnear hNear z +
        CKN.Leray.rieszPressureSpaceTime
          (3 / 2 : ℝ) (by norm_num) Ffar hFar z) := by
  let S : Set (Vec3 × ℝ) := Set.univ ×ˢ J
  let A : Set (Vec3 × ℝ) := CKN.euclideanBall 0 L ×ˢ J
  let B : Set (Vec3 × ℝ) := (CKN.euclideanBall 0 L)ᶜ ×ˢ J
  let Fnear : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => A.indicator (F i j)
  let Ffar : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => B.indicator (F i j)
  let hNear : ∀ i j, MemLp (Fnear i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    fun i j => (hF i j).indicator ((CKN.isOpen_euclideanBall 0 L).measurableSet.prod hJ)
  let hFar : ∀ i j, MemLp (Ffar i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    fun i j => (hF i j).indicator
      ((CKN.isOpen_euclideanBall 0 L).measurableSet.compl.prod hJ)
  have hLocal := blowup_rieszPressureSpaceTime_time_indicator_ae F hF J hJ
  have hSplit := blowup_rieszPressure_time_near_far_ae F hF L J hJ
  filter_upwards [hLocal, hSplit] with z hl hs
  by_cases ht : z.2 ∈ J
  · simp only [Set.mem_prod, Set.mem_univ, true_and, ht,
      Set.indicator_of_mem] at hl ⊢
    exact hl.trans hs
  · have hznot : z ∉ S := fun hm => ht hm.2
    have hznot' : z ∉ (Set.univ ×ˢ J) := hznot
    simp only [Set.indicator_of_notMem hznot']

/-- On every spatial ball over the selected time set, the full pressure is
the sum of the near and exterior pressures almost everywhere. -/
theorem blowup_rieszPressure_full_near_far_local_ae
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (L R : ℝ) (J : Set ℝ) (hJ : MeasurableSet J) :
    let A : Set (Vec3 × ℝ) := CKN.euclideanBall 0 L ×ˢ J
    let B : Set (Vec3 × ℝ) := (CKN.euclideanBall 0 L)ᶜ ×ˢ J
    let Fnear : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => A.indicator (F i j)
    let Ffar : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => B.indicator (F i j)
    let hNear : ∀ i j, MemLp (Fnear i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      fun i j => (hF i j).indicator ((CKN.isOpen_euclideanBall 0 L).measurableSet.prod hJ)
    let hFar : ∀ i j, MemLp (Ffar i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      fun i j => (hF i j).indicator
        ((CKN.isOpen_euclideanBall 0 L).measurableSet.compl.prod hJ)
    (fun z => CKN.Leray.rieszPressureSpaceTime
      (3 / 2 : ℝ) (by norm_num) F hF z) =ᵐ[
      (volume : Measure (Vec3 × ℝ)).restrict (CKN.euclideanBall 0 R ×ˢ J)]
      fun z => CKN.Leray.rieszPressureSpaceTime
          (3 / 2 : ℝ) (by norm_num) Fnear hNear z +
        CKN.Leray.rieszPressureSpaceTime
          (3 / 2 : ℝ) (by norm_num) Ffar hFar z := by
  let C : Set (Vec3 × ℝ) := CKN.euclideanBall 0 R ×ˢ J
  have hC : MeasurableSet C := (CKN.isOpen_euclideanBall 0 R).measurableSet.prod hJ
  have hFull := blowup_rieszPressure_full_near_far_on_time_ae F hF L J hJ
  filter_upwards [ae_restrict_of_ae (s := C) hFull,
    self_mem_ae_restrict hC] with z hz hzC
  have hzS : z ∈ (Set.univ : Set Vec3) ×ˢ J := ⟨Set.mem_univ _, hzC.2⟩
  simpa only [Set.indicator_of_mem hzS] using hz

end ESS
