/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureMeasSource

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- The fixed pressure split bounds the rescaled pressure mass on every
bounded open past cylinder. -/
theorem blowupPressure_eventually_mass_bound_pastBox
    (p p₁ : ParabolicPoint → ℝ)
    (hp₁ : AEStronglyMeasurable p₁
      (volume.restrict (Set.univ ×ˢ Ioo (-1 : ℝ) 0)))
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hsource : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable (fun x : Vec3 => p₁ (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => p₁ (x,s)) (3 / 2 : ℝ≥0∞) volume ≤ M)
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p (z.1,z.2) - p₁ (z.1,z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))))
    (hharm : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p (x,t) - p₁ (x,t)))
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) (hR : 0 < R) (ha : a < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      MemLp (blowupPressure x₀ t₀ (r k) p) (3 / 2 : ℝ≥0∞)
        ((volume : Measure ParabolicPoint).restrict
          (vec3Ball 0 R ×ˢ Ioo a 0)) ∧
      (∫ (z : ParabolicPoint) in vec3Ball 0 R ×ˢ Ioo a 0,
        |blowupPressure x₀ t₀ (r k) p z| ^ (3 / 2 : ℝ)
        ∂(volume : Measure ParabolicPoint)) ≤ C := by
  obtain ⟨B, hB, hbound⟩ :=
    blowupPressure_eventually_bounded_pastBox
      p p₁ hp₁ M hM hsource hp₂ hharm
      x₀ t₀ r hx₀ ht₀ hr hr0 R a hR ha
  refine ⟨B.toReal ^ (3 / 2 : ℝ), by positivity, ?_⟩
  filter_upwards [hbound] with k hk
  let C := vec3Ball (0 : Vec3) R ×ˢ Ioo a 0
  let μ : Measure ParabolicPoint := volume.restrict C
  have hpm : AEStronglyMeasurable
      (blowupPressure x₀ t₀ (r k) p) μ :=
    (blowupPressure_aestronglyMeasurable_of_split
      p p₁ hp₁ hp₂ x₀ t₀ (r k) (hr k)).restrict
  have hmem : MemLp (blowupPressure x₀ t₀ (r k) p)
      (3 / 2 : ℝ≥0∞) μ := by
    rw [memLp_iff]
    exact hk.trans_lt hB
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have h := blowup_integral_norm_rpow_le_of_eLpNorm_le
    μ (blowupPressure x₀ t₀ (r k) p) (3 / 2)
    (by norm_num) (hcoeff ▸ hmem) B hB (hcoeff ▸ hk)
  exact ⟨hmem, by simpa only [C, μ, Real.norm_eq_abs] using h⟩

end ESS
