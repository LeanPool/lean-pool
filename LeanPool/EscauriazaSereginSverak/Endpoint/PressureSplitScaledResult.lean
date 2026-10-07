/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitSpacetimeBound
public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitScaledBound
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupGeometry

/-!
# Linear scale bound for the fixed pressure remainder

The fixed harmonic remainder has a time-integrated spatial supremum bound;
parabolic rescaling converts it to the critical linear factor in the radius.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

private theorem pressureSplit_boundedRegion_eventually_inner
    {Ω : Set Vec3} (hΩ : Bornology.IsBounded Ω)
    (x₀ : Vec3) (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      ∀ x ∈ Ω, CKN.scalingSpace r x₀ x ∈
        CKN.euclideanBall 0 (3 / 4 : ℝ) := by
  have hx₀norm : vec3EuclideanNorm x₀ ≤ 1 / 2 := by
    rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] at hx₀
    simpa only [Set.mem_ofPred_eq, sub_zero] using hx₀
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall
    (0 : Vec3)).mp hΩ
  let K : ℝ := Real.sqrt 3 * max R 0
  have hK : 0 ≤ K := mul_nonneg (Real.sqrt_nonneg _) (le_max_right _ _)
  have hnorm_bound : ∀ x ∈ Ω, vec3EuclideanNorm x ≤ K := by
    intro x hx
    have hdist : dist x 0 ≤ R := Metric.mem_closedBall.mp (hR hx)
    have hnorm : ‖x‖ ≤ R := by simpa [dist_eq_norm] using hdist
    calc
      vec3EuclideanNorm x ≤ Real.sqrt 3 * ‖x‖ :=
        CKN.Foundation.Parabolic.vec3EuclideanNorm_le_sqrt_three_mul_norm x
      _ ≤ Real.sqrt 3 * R :=
        mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
      _ ≤ K := mul_le_mul_of_nonneg_left (le_max_left R 0)
        (Real.sqrt_nonneg _)
  let δ : ℝ := 1 / (4 * (K + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ x hx
  have hδK : δ * K < 1 / 4 := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * (K + 1))]
    nlinarith only [hK]
  have hrK : r * K < 1 / 4 := by
    calc
      r * K ≤ δ * K := mul_le_mul_of_nonneg_right hrδ.le hK
      _ < 1 / 4 := hδK
  have hscaleNorm : vec3EuclideanNorm (r • x) ≤ r * K := by
    rw [vec3EuclideanNorm_smul, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (hnorm_bound x hx) hr.le
  have hsum : vec3EuclideanNorm (x₀ + r • x) ≤
      vec3EuclideanNorm x₀ + r * K := by
    exact (vec3EuclideanNorm_add_le x₀ (r • x)).trans
      (add_le_add_right hscaleNorm _)
  have hlt : vec3EuclideanNorm x₀ + r * K < 3 / 4 := by
    linarith only [hx₀norm, hrK]
  apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by norm_num : (0 : ℝ) < 3 / 4)).mpr
  change CKN.vecEuclideanNorm (CKN.scalingSpace r x₀ x - 0) < 3 / 4
  rw [CKN.scalingSpace, sub_zero]
  have hnormEq : CKN.vecEuclideanNorm (x₀ + r • x) =
      vec3EuclideanNorm (x₀ + r • x) := by
    simp [CKN.vecEuclideanNorm, vec3EuclideanNorm, vecNormSq, vecDot, pow_two]
  rw [hnormEq]
  exact lt_of_le_of_lt hsum hlt

/-- The zero-extended fixed pressure remainder has the critical linear
scale bound on every bounded measurable spatial region. -/
theorem pressureSplit_remainder_mixed_scale_bound
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
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0)
    (x₀ : Vec3) (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (t₀ : ℝ) {Ω : Set Vec3} (hΩmeas : MeasurableSet Ω)
    (hΩbounded : Bornology.IsBounded Ω) :
    let F := pressureSplitTensor u
    let hF := pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
    let p₁ := pressureSplitRieszPressure F hF
    let p₂ := pressureSplitRemainder p p₁
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ r : ℝ, 0 < r → r < δ →
        (∫⁻ t : ℝ,
          eLpNorm (fun x : Vec3 => parabolicRescalePressure x₀ t₀ r
            (goodPointDomain.indicator p₂) (x,t)) ⊤
            (volume.restrict Ω) ^ (3 / 2 : ℝ)) ≤
          C * (ENNReal.ofReal r *
            ((eLpNorm (fun z : Vec3 × ℝ => p (z.1,z.2))
              (3 / 2 : ℝ≥0∞)
              ((volume.restrict (CKN.euclideanBall 0 1)).prod
                (volume.restrict (Ioo (-1 : ℝ) 0))) ^ (3 / 2 : ℝ)) +
              ENNReal.ofReal (pressureSplitVelocityLpBound u ^ 3))) := by
  dsimp only
  let F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := pressureSplitTensor u
  let hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) :=
    pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
  let p₁ : ParabolicPoint → ℝ := pressureSplitRieszPressure F hF
  let p₂ : ParabolicPoint → ℝ := pressureSplitRemainder p p₁
  obtain ⟨C, hC, hsource⟩ := pressureSplit_remainder_supLp_bound
    hu hDu hpmeas hL2 henergy hp hL3 hgrad hdiv hMomentum
  obtain ⟨δ, hδ, hΩimage⟩ := pressureSplit_boundedRegion_eventually_inner
    hΩbounded x₀ hx₀
  let μ : Measure (Vec3 × ℝ) :=
    (volume.restrict (CKN.euclideanBall 0 1)).prod
      (volume.restrict (Ioo (-1 : ℝ) 0))
  let D : Set (Vec3 × ℝ) := pressureSplitProductDomain
  have hball : CKN.euclideanBall (0 : Vec3) 1 = pressureSplitBall := by
    rw [pressureSplitBall, CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
      (by norm_num : (0 : ℝ) < 1)]
  have hmeasure : μ = (volume : Measure (Vec3 × ℝ)).restrict D := by
    dsimp [μ, D]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
    simp only [pressureSplitProductDomain, pressureSplitTime, hball]
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hp₂global := pressureSplit_remainder_memLp_product
    hu hDu henergy hp hL3 hgrad
  have hp₂μ₀ : MemLp (fun z : Vec3 × ℝ => p₂ (z.1,z.2))
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    have hrestrict := hp₂global.restrict D
    rw [hmeasure]
    apply (memLp_congr_ae ?_).2 hrestrict
    filter_upwards [] with z
    simp [p₂, p₁, F, pressureSplitRemainder,
      parabolicHomeomorph_symm_apply, pressureSplitRieszPressure]
  have hp₂ : MemLp (fun z : Vec3 × ℝ => p₂ (z.1,z.2))
      (3 / 2 : ℝ≥0∞) μ := by
    rw [← hcoeff]
    exact hp₂μ₀
  have hbound : ∀ r : ℝ, 0 < r → r < δ →
      (∫⁻ t : ℝ,
        eLpNorm (fun x : Vec3 => parabolicRescalePressure x₀ t₀ r
          (goodPointDomain.indicator p₂) (x,t)) ⊤
          (volume.restrict Ω) ^ (3 / 2 : ℝ)) ≤
        C * (ENNReal.ofReal r *
          ((eLpNorm (fun z : Vec3 × ℝ => p (z.1,z.2))
            (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ)) +
            ENNReal.ofReal (pressureSplitVelocityLpBound u ^ 3))) := by
    intro r hr hrδ
    have hscaled := blowupPressureRemainder_mixed_sup_scale_bound
      p₂ hp₂ x₀ t₀ r hr hΩmeas (hΩimage r hr hrδ)
    calc
      _ ≤ ENNReal.ofReal r *
          (∫⁻ s : ℝ, blowupHarmonicSupExtended p₂ s ^ (3 / 2 : ℝ)) := hscaled
      _ ≤ ENNReal.ofReal r *
          (C * ((eLpNorm (fun z : Vec3 × ℝ => p (z.1,z.2))
            (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ)) +
            ENNReal.ofReal (pressureSplitVelocityLpBound u ^ 3))) := by
        gcongr
      _ = C * (ENNReal.ofReal r *
          ((eLpNorm (fun z : Vec3 × ℝ => p (z.1,z.2))
            (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ)) +
            ENNReal.ofReal (pressureSplitVelocityLpBound u ^ 3))) := by
        ac_rfl
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro r hr hrδ
  simpa only [μ] using hbound r hr hrδ

end ESS

end
