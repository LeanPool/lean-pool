/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitHarmonicity
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszFarVelocity

/-!
# Velocity slices for the fixed pressure split

The assumed essential supremum of the local cubic velocity mass controls the
whole-space `L³` norms of its zero-extended spatial slices.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The `L³` slice bound associated with the local cubic velocity mass in
`lem:pressure-split`. -/
@[expose] def pressureSplitVelocityLpBound (u : ParabolicPoint → Vec3) : ℝ :=
  ((essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
    ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ))
    (volume.restrict pressureSplitTime)) ^ (1 / 3 : ℝ)).toReal

/-- The velocity on each time slice, extended by zero outside the source ball. -/
@[expose] def pressureSplitVelocityExtension (u : ParabolicPoint → Vec3) :
    Vec3 × ℝ → Vec3 := fun z =>
  pressureSplitBall.indicator (fun x : Vec3 => u ((x,z.2) : ParabolicPoint)) z.1

/-- Almost every zero-extended velocity slice belongs to `L³` and has norm
bounded by `pressureSplitVelocityLpBound`. -/
theorem pressureSplitVelocityExtension_slice_memLp_bound
    {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ))
      (volume.restrict pressureSplitTime) < ⊤) :
    ∀ᵐ t ∂(volume.restrict pressureSplitTime),
      MemLp (fun x : Vec3 => pressureSplitVelocityExtension u (x,t))
        3 volume ∧
      eLpNorm (fun x : Vec3 => pressureSplitVelocityExtension u (x,t))
        3 volume ≤ ENNReal.ofReal (pressureSplitVelocityLpBound u) := by
  let μx : Measure Vec3 := volume.restrict pressureSplitBall
  let μt : Measure ℝ := volume.restrict pressureSplitTime
  let A : ℝ≥0∞ := essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
    ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ)) μt
  let N : ℝ≥0∞ := A ^ (1 / 3 : ℝ)
  have hA : A < ⊤ := by simpa [A, μt] using hL3
  have hN : N < ⊤ := by
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA.ne
  have hM : ENNReal.ofReal (pressureSplitVelocityLpBound u) = N := by
    simp only [pressureSplitVelocityLpBound, A, N, μt]
    exact ENNReal.ofReal_toReal hN.ne
  have hBallMeas : MeasurableSet pressureSplitBall :=
    (isOpen_vec3Ball (0 : Vec3) 1).measurableSet
  have hparaMeas : MeasurableSet pressureSplitDomain := by
    exact (isOpen_spaceTimeSet pressureSplitBall pressureSplitTime
      (isOpen_vec3Ball (0 : Vec3) 1) isOpen_Ioo).measurableSet
  have hpre : parabolicHomeomorph.symm ⁻¹' pressureSplitDomain =
      pressureSplitProductDomain := by
    ext z
    rfl
  have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage
    hparaMeas
  rw [hpre] at hmp
  have hmeasure : μx.prod μt =
      (volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain := by
    dsimp [μx, μt]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
    simp only [pressureSplitProductDomain]
  have huProd : AEStronglyMeasurable (fun z : Vec3 × ℝ => u z)
      (μx.prod μt) := by
    have h := hu.comp_measurePreserving hmp
    change AEStronglyMeasurable
      (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) _ at h
    have heq : (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) =
        fun z => u z := by
      funext z
      cases z
      rfl
    rw [heq] at h
    rw [hmeasure]
    exact h
  have huSlice : ∀ᵐ t ∂μt,
      AEStronglyMeasurable (fun x : Vec3 => u ((x,t) : ParabolicPoint)) μx := by
    simpa only [Function.comp_def] using huProd.prodMk_right
  have hAt : ∀ᵐ t ∂μt,
      (∫⁻ x in pressureSplitBall,
        ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ)) ≤ A := by
    simpa only [A, μt] using
      (ENNReal.ae_le_essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
        ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ)))
  have hAtop : ∀ᵐ t ∂μt,
      (∫⁻ x in pressureSplitBall,
        ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ)) < ⊤ := by
    filter_upwards [hAt] with t ht
    exact lt_of_le_of_lt ht hA
  filter_upwards [huSlice, hAt, hAtop] with t ht hmass hmassTop
  let v : Vec3 → Vec3 := fun x => pressureSplitVelocityExtension u (x,t)
  have hvMeas : AEStronglyMeasurable v volume := by
    change AEStronglyMeasurable
      (pressureSplitBall.indicator (fun x : Vec3 => u ((x,t) : ParabolicPoint))) volume
    exact (aestronglyMeasurable_indicator_iff hBallMeas).2 ht
  have hvpoint (x : Vec3) : ‖v x‖ₑ ^ (3 : ℝ) ≤
      pressureSplitBall.indicator
        (fun y : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u ((y,t) : ParabolicPoint))) ^
          (3 : ℝ)) x := by
    by_cases hx : x ∈ pressureSplitBall
    · have hvx : v x = u ((x,t) : ParabolicPoint) := by
        simp [v, pressureSplitVelocityExtension, Set.indicator_of_mem hx]
      rw [hvx, Set.indicator_of_mem hx]
      rw [← ofReal_norm]
      exact ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal
          (norm_le_vec3EuclideanNorm (u ((x,t) : ParabolicPoint))))
        (by norm_num)
    · have hvx : v x = 0 := by
        simp [v, pressureSplitVelocityExtension, Set.indicator_of_notMem hx]
      rw [hvx, Set.indicator_of_notMem hx]
      simp
  have hmassV : (∫⁻ x : Vec3, ‖v x‖ₑ ^ (3 : ℝ)) ≤ A := by
    calc
      _ ≤ ∫⁻ x, pressureSplitBall.indicator
            (fun y : Vec3 => ENNReal.ofReal
              (vec3EuclideanNorm (u ((y,t) : ParabolicPoint))) ^ (3 : ℝ)) x :=
          lintegral_mono fun x => hvpoint x
      _ = ∫⁻ x in pressureSplitBall,
          ENNReal.ofReal (vec3EuclideanNorm (u ((x,t) : ParabolicPoint))) ^
            (3 : ℝ) := by rw [lintegral_indicator hBallMeas]
      _ ≤ A := hmass
  have hformula : eLpNorm v 3 volume ^ (3 : ℝ) =
      ∫⁻ x : Vec3, ‖v x‖ₑ ^ (3 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num) (by norm_num) hvMeas,
      ← ENNReal.rpow_mul]
    norm_num
  have hnormpow : eLpNorm v 3 volume ^ (3 : ℝ) < ⊤ := by
    rw [hformula]
    exact lt_of_le_of_lt hmassV hA
  have hnormfin : eLpNorm v 3 volume < ⊤ :=
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 3)).mp hnormpow
  have hvMem : MemLp v 3 volume := by
    rw [memLp_iff]
    exact hnormfin
  have hrootEq : eLpNorm v 3 volume =
      (∫⁻ x : Vec3, ‖v x‖ₑ ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
    calc
      _ = (eLpNorm v 3 volume ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
        rw [← ENNReal.rpow_mul]
        norm_num
      _ = _ := congrArg (fun a : ℝ≥0∞ => a ^ (1 / 3 : ℝ)) hformula
  have hbound : eLpNorm v 3 volume ≤ N := by
    rw [hrootEq]
    exact ENNReal.rpow_le_rpow hmassV (by norm_num)
  refine ⟨?_, ?_⟩
  · simpa only [v] using hvMem
  · simpa only [v, hM] using hbound

end ESS

end
