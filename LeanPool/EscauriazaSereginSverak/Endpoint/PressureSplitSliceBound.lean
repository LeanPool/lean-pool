/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitVelocityLp
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszSliceBound

/-!
# Fixed pressure slice bound

The tensor slices inherit the quadratic bound from the velocity slices, and
the spatial Riesz operator gives the corresponding pressure estimate.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

private theorem pressureSplitTensor_slice_lpNorm_bound
    {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ))
      (volume.restrict pressureSplitTime) < ⊤) :
    ∀ᵐ t ∂(volume.restrict pressureSplitTime), ∀ i j : Fin 3,
      lpNorm (fun x : Vec3 => pressureSplitTensor u i j (x,t))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
          pressureSplitVelocityLpBound u ^ 2 := by
  let M : ℝ := pressureSplitVelocityLpBound u
  let v : Vec3 × ℝ → Vec3 := pressureSplitVelocityExtension u
  have hVel := pressureSplitVelocityExtension_slice_memLp_bound hu hL3
  have hMnonneg : 0 ≤ M := by
    dsimp [M, pressureSplitVelocityLpBound]
    exact ENNReal.toReal_nonneg
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hinput : ∀ᵐ t ∂(volume.restrict pressureSplitTime),
      ∀ i j : Fin 3,
        lpNorm (fun x : Vec3 => pressureSplitTensor u i j (x,t))
          (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ M ^ 2 := by
    filter_upwards [hVel, self_mem_ae_restrict measurableSet_Ioo] with
      t ⟨hvt, hvtBound⟩ htJ i j
    let w : Vec3 → Vec3 := fun x => v (x,t)
    have hvt' : MemLp w 3 volume := by simpa only [w, v] using hvt
    have hvtBound' : eLpNorm w 3 volume ≤ ENNReal.ofReal M := by
      simpa only [w, v, M] using hvtBound
    have hi : AEStronglyMeasurable (fun x : Vec3 => w x i) volume :=
      (continuous_apply i).comp_aestronglyMeasurable hvt'.aestronglyMeasurable
    have hj : AEStronglyMeasurable (fun x : Vec3 => w x j) volume :=
      (continuous_apply j).comp_aestronglyMeasurable hvt'.aestronglyMeasurable
    have hmul : eLpNorm (fun x : Vec3 => w x i * w x j)
        (3 / 2 : ℝ≥0∞) volume ≤
          eLpNorm (fun x : Vec3 => w x i) 3 volume *
            eLpNorm (fun x : Vec3 => w x j) 3 volume := by
      simpa only [hcoeff, show ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) by norm_num] using
        (CKN.Foundation.Measure.eLpNorm_mul_le_three_three hi hj)
    have hcompI : eLpNorm (fun x : Vec3 => w x i) 3 volume ≤
        ENNReal.ofReal M := by
      have h := blowup_component_eLpNorm_le volume 3 w
        hvt'.aestronglyMeasurable i
      exact h.trans hvtBound'
    have hcompJ : eLpNorm (fun x : Vec3 => w x j) 3 volume ≤
        ENNReal.ofReal M := by
      have h := blowup_component_eLpNorm_le volume 3 w
        hvt'.aestronglyMeasurable j
      exact h.trans hvtBound'
    have hproductBound : eLpNorm (fun x : Vec3 => w x i * w x j)
        (3 / 2 : ℝ≥0∞) volume ≤ ENNReal.ofReal M * ENNReal.ofReal M := by
      calc
        _ ≤ eLpNorm (fun x : Vec3 => w x i) 3 volume *
            eLpNorm (fun x : Vec3 => w x j) 3 volume := hmul
        _ ≤ ENNReal.ofReal M * ENNReal.ofReal M := by gcongr
    have hslice : (fun x : Vec3 => pressureSplitTensor u i j (x,t)) =
        fun x : Vec3 => w x i * w x j := by
      funext x
      by_cases hx : x ∈ pressureSplitBall
      · change (spaceTimeSet pressureSplitBall pressureSplitTime).indicator
          (fun z : ParabolicPoint => u z i * u z j)
          (parabolicHomeomorph.symm (x,t)) = w x i * w x j
        have hmem : parabolicHomeomorph.symm (x,t) ∈
            spaceTimeSet pressureSplitBall pressureSplitTime := by
          change (parabolicHomeomorph.symm (x,t)).1 ∈ pressureSplitBall ∧
            (parabolicHomeomorph.symm (x,t)).2 ∈ pressureSplitTime
          simpa only [parabolicHomeomorph_symm_apply] using
            (show x ∈ pressureSplitBall ∧ t ∈ pressureSplitTime from ⟨hx, htJ⟩)
        rw [Set.indicator_of_mem hmem]
        simp [w, v, pressureSplitVelocityExtension, hx]
      · change (spaceTimeSet pressureSplitBall pressureSplitTime).indicator
          (fun z : ParabolicPoint => u z i * u z j)
          (parabolicHomeomorph.symm (x,t)) = w x i * w x j
        have hnot : parabolicHomeomorph.symm (x,t) ∉
            spaceTimeSet pressureSplitBall pressureSplitTime := by
          intro hz
          change (parabolicHomeomorph.symm (x,t)).1 ∈ pressureSplitBall ∧
            (parabolicHomeomorph.symm (x,t)).2 ∈ pressureSplitTime at hz
          have hx' : x ∈ pressureSplitBall := by
            simpa only [parabolicHomeomorph_symm_apply] using hz.1
          exact hx hx'
        rw [Set.indicator_of_notMem hnot]
        simp [w, v, pressureSplitVelocityExtension, hx]
    rw [hslice, hcoeff]
    have hMlt : ENNReal.ofReal M < ⊤ :=
      lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
    have hMtop : ENNReal.ofReal M * ENNReal.ofReal M < ⊤ :=
      ENNReal.mul_lt_top hMlt hMlt
    change (eLpNorm (fun x : Vec3 => w x i * w x j)
      (3 / 2 : ℝ≥0∞) volume).toReal ≤ M ^ 2
    calc
      _ ≤ (ENNReal.ofReal M * ENNReal.ofReal M).toReal :=
        ENNReal.toReal_mono hMtop.ne hproductBound
      _ = M ^ 2 := by
        rw [ENNReal.toReal_mul]
        simp only [ENNReal.toReal_ofReal hMnonneg]
        ring
  exact hinput

/-- The fixed whole-space pressure has an essentially uniform spatial
`L^(3/2)` bound on the source time interval. -/
theorem pressureSplitRieszPressure_slice_bound
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hDu : AEStronglyMeasurable Du (volume.restrict pressureSplitDomain))
    (henergy : (∫⁻ z in pressureSplitDomain,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ))
      (volume.restrict pressureSplitTime) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict pressureSplitTime), ∀ i : Fin 3,
      HasWeakGradientOn pressureSplitBall (fun x => u (x,t) i)
        (fun x => Du (x,t) i)) :
    ∀ᵐ t ∂(volume.restrict pressureSplitTime),
      MemLp (fun x : Vec3 => pressureSplitRieszPressure
        (pressureSplitTensor u)
        (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad) ((x,t) : ParabolicPoint))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      eLpNorm (fun x : Vec3 => pressureSplitRieszPressure
        (pressureSplitTensor u)
        (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad) ((x,t) : ParabolicPoint))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
        ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound
          (3 / 2 : ℝ) (by norm_num) * (9 * pressureSplitVelocityLpBound u ^ 2)) := by
  let F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := pressureSplitTensor u
  let hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) :=
    pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
  have hinput := pressureSplitTensor_slice_lpNorm_bound hu hL3
  have hpressure := blowup_rieszPressureSpaceTime_slice_norm_bound
    F hF (pressureSplitVelocityLpBound u ^ 2) hinput
  have hpressureEq (t : ℝ) :
      (fun x : Vec3 => pressureSplitRieszPressure (pressureSplitTensor u) hF
        ((x,t) : ParabolicPoint)) =
      (fun x : Vec3 => CKN.Leray.rieszPressureSpaceTime
        (3 / 2 : ℝ) (by norm_num) F hF (x,t)) := by
    funext x
    change CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
      (pressureSplitTensor u) hF (parabolicHomeomorph ((x,t) : ParabolicPoint)) =
        CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF (x,t)
    rfl
  filter_upwards [hpressure] with t ht
  rw [← hpressureEq t] at ht
  simpa only [F, hF, pressureSplitTime] using ht

end ESS

end
