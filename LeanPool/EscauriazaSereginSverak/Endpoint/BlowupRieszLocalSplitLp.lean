/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszDecomposition

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- The near and exterior pressure decomposition holds as an equality in
local `L^(3/2)` on a bounded cylinder. -/
theorem blowup_rieszPressure_full_near_far_local_Lp
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (L R : ℝ) (J : Set ℝ) (hJ : MeasurableSet J) :
    let C : Set (Vec3 × ℝ) := CKN.euclideanBall 0 R ×ˢ J
    let A : Set (Vec3 × ℝ) := CKN.euclideanBall 0 L ×ˢ J
    let B : Set (Vec3 × ℝ) := (CKN.euclideanBall 0 L)ᶜ ×ˢ J
    let Fnear : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => A.indicator (F i j)
    let Ffar : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => B.indicator (F i j)
    let hNear : ∀ i j, MemLp (Fnear i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      fun i j => (hF i j).indicator ((CKN.isOpen_euclideanBall 0 L).measurableSet.prod hJ)
    let hFar : ∀ i j, MemLp (Ffar i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      fun i j => (hF i j).indicator
        ((CKN.isOpen_euclideanBall 0 L).measurableSet.compl.prod hJ)
    let p := CKN.Leray.rieszPressureSpaceTime
      (3 / 2 : ℝ) (by norm_num) F hF
    let pn := CKN.Leray.rieszPressureSpaceTime
      (3 / 2 : ℝ) (by norm_num) Fnear hNear
    let pf := CKN.Leray.rieszPressureSpaceTime
      (3 / 2 : ℝ) (by norm_num) Ffar hFar
    let hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict C) :=
      (CKN.Leray.rieszPressureSpaceTime_memLp
        (3 / 2 : ℝ) (by norm_num) F hF).mono_measure Measure.restrict_le_self
    let hn : MemLp pn (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict C) :=
      (CKN.Leray.rieszPressureSpaceTime_memLp
        (3 / 2 : ℝ) (by norm_num) Fnear hNear).mono_measure Measure.restrict_le_self
    let hf : MemLp pf (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict C) :=
      (CKN.Leray.rieszPressureSpaceTime_memLp
        (3 / 2 : ℝ) (by norm_num) Ffar hFar).mono_measure Measure.restrict_le_self
    hp.toLp p = hn.toLp pn + hf.toLp pf := by
  let : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
  let C : Set (Vec3 × ℝ) := CKN.euclideanBall 0 R ×ˢ J
  let A : Set (Vec3 × ℝ) := CKN.euclideanBall 0 L ×ˢ J
  let B : Set (Vec3 × ℝ) := (CKN.euclideanBall 0 L)ᶜ ×ˢ J
  let Fnear : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => A.indicator (F i j)
  let Ffar : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => B.indicator (F i j)
  let hNear : ∀ i j, MemLp (Fnear i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    fun i j => (hF i j).indicator ((CKN.isOpen_euclideanBall 0 L).measurableSet.prod hJ)
  let hFar : ∀ i j, MemLp (Ffar i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    fun i j => (hF i j).indicator
      ((CKN.isOpen_euclideanBall 0 L).measurableSet.compl.prod hJ)
  let p := CKN.Leray.rieszPressureSpaceTime
    (3 / 2 : ℝ) (by norm_num) F hF
  let pn := CKN.Leray.rieszPressureSpaceTime
    (3 / 2 : ℝ) (by norm_num) Fnear hNear
  let pf := CKN.Leray.rieszPressureSpaceTime
    (3 / 2 : ℝ) (by norm_num) Ffar hFar
  let hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict C) :=
    (CKN.Leray.rieszPressureSpaceTime_memLp
      (3 / 2 : ℝ) (by norm_num) F hF).mono_measure Measure.restrict_le_self
  let hn : MemLp pn (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict C) :=
    (CKN.Leray.rieszPressureSpaceTime_memLp
      (3 / 2 : ℝ) (by norm_num) Fnear hNear).mono_measure Measure.restrict_le_self
  let hf : MemLp pf (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict C) :=
    (CKN.Leray.rieszPressureSpaceTime_memLp
      (3 / 2 : ℝ) (by norm_num) Ffar hFar).mono_measure Measure.restrict_le_self
  have hsplit := blowup_rieszPressure_full_near_far_local_ae F hF L R J hJ
  apply Lp.ext
  filter_upwards [hp.coeFn_toLp, hn.coeFn_toLp, hf.coeFn_toLp,
    hsplit, Lp.coeFn_add (hn.toLp pn) (hf.toLp pf)] with z hz hzn hzf hs hadd
  calc
    (hp.toLp p : Vec3 × ℝ → ℝ) z = p z := hz
    _ = pn z + pf z := hs
    _ = (hn.toLp pn : Vec3 × ℝ → ℝ) z +
        (hf.toLp pf : Vec3 × ℝ → ℝ) z := by rw [hzn, hzf]
    _ = ((hn.toLp pn + hf.toLp pf : Lp ℝ
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict C)) :
          Vec3 × ℝ → ℝ) z := hadd.symm

end ESS
