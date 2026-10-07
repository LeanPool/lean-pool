/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitSliceBound
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureIntegrability

/-!
# Fixed pressure split estimates

The whole-space pressure slice estimate, harmonicity, and interior estimate
give the fixed decomposition used in `lem:pressure-split`.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The harmonic part of the fixed pressure split has an integrable interior
spatial supremum, bounded by its local space-time `L^(3/2)` mass. -/
theorem pressureSplit_remainder_harmonic_interior_bound
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hDu : AEStronglyMeasurable Du (volume.restrict pressureSplitDomain))
    (hpmeas : AEStronglyMeasurable p (volume.restrict pressureSplitDomain))
    (hL2 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ‖u (x,t)‖ₑ ^ (2 : ℝ)) (volume.restrict pressureSplitTime) < ⊤)
    (henergy : (∫⁻ z in pressureSplitDomain,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict pressureSplitDomain))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ))
      (volume.restrict pressureSplitTime) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict pressureSplitTime), ∀ i : Fin 3,
      HasWeakGradientOn pressureSplitBall (fun x => u (x,t) i)
        (fun x => Du (x,t) i))
    (hdiv : ∀ χ : Vec3 × ℝ → ℝ,
      χ ∈ spaceTimeTestFunction (V := ℝ) pressureSplitBall pressureSplitTime →
      ∫ z in pressureSplitDomain,
        ∑ i : Fin 3, u z i * spatialPartial χ i z = 0)
    (hMomentum : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) pressureSplitBall pressureSplitTime →
      ∫ z in pressureSplitDomain,
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0) :
    let p₁ := pressureSplitRieszPressure (pressureSplitTensor u)
      (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad)
    let p₂ := pressureSplitRemainder p p₁
    MemLp (fun z : Vec3 × ℝ => p₂ (parabolicHomeomorph.symm z))
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) ∧
      (∀ᵐ t ∂(volume.restrict pressureSplitTime),
        CKN.Foundation.Heat.WeaklyHarmonicOn pressureSplitBall
          (fun x : Vec3 => p₂ (x,t))) ∧
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        (∫⁻ t in pressureSplitTime,
          eLpNorm (fun x : Vec3 => p₂ (x,t)) ⊤
            (volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ))) ^ (3 / 2 : ℝ)) ≤
          C * eLpNorm (fun z : Vec3 × ℝ => p₂ (z.1,z.2))
            (3 / 2 : ℝ≥0∞)
            ((volume.restrict (CKN.euclideanBall 0 1)).prod
              (volume.restrict pressureSplitTime)) ^ (3 / 2 : ℝ) := by
  dsimp only
  let p₁ : ParabolicPoint → ℝ := pressureSplitRieszPressure
    (pressureSplitTensor u) (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad)
  let p₂ : ParabolicPoint → ℝ := pressureSplitRemainder p p₁
  have hp₂global := pressureSplit_remainder_memLp_product hu hDu henergy hp hL3 hgrad
  have hharm := pressureSplitRemainder_harmonic_slices
    hu hDu hpmeas hL2 henergy hp hL3 hgrad hdiv hMomentum
  have hlocal : MemLp (fun z : Vec3 × ℝ => p₂ (z.1,z.2))
      (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict pressureSplitTime)) := by
    have hrestrict := hp₂global.restrict pressureSplitProductDomain
    have hmeasure : (volume.restrict pressureSplitBall).prod
        (volume.restrict pressureSplitTime) =
          (volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
      simp only [pressureSplitProductDomain]
    rw [← hmeasure] at hrestrict
    have heq : (fun z : Vec3 × ℝ =>
        pressureSplitRemainder p p₁ (parabolicHomeomorph.symm z)) =
          fun z => p₂ (z.1,z.2) := by
      funext z
      simp [p₂, p₁]
    have hrestrict' : MemLp
        (fun z : Vec3 × ℝ => p₂ (z.1,z.2))
        (ENNReal.ofReal (3 / 2 : ℝ))
        ((volume.restrict pressureSplitBall).prod
          (volume.restrict pressureSplitTime)) := by
      exact (memLp_congr_ae
        (Eventually.of_forall fun z => (congrFun heq z).symm)).2 hrestrict
    have hball : pressureSplitBall = CKN.euclideanBall 0 1 := by
      rw [pressureSplitBall, CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
        (by norm_num : (0 : ℝ) < 1)]
    simpa only [pressureSplitTime, hball] using hrestrict'
  have hharm' : ∀ᵐ t ∂(volume.restrict pressureSplitTime),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p₂ (x,t)) := by
    simpa only [pressureSplitBall, CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
      (by norm_num : (0 : ℝ) < 1)] using hharm
  have hlocal' : MemLp (fun z : Vec3 × ℝ => p₂ (z.1,z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict pressureSplitTime)) := by
    have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hcoeff] at hlocal
    exact hlocal
  obtain ⟨C, hC, hbound⟩ := blowupHarmonicPressure_bound
    (J := pressureSplitTime) p₂ hlocal' hharm'
  exact ⟨by simpa only [p₂, p₁] using hp₂global, by simpa only [p₂] using hharm,
    C, hC, by simpa only [pressureSplitTime, p₂] using hbound⟩

end ESS

end
