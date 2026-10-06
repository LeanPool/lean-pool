/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupVelocityMeas

public section

open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- A uniform source velocity slice bound gives a uniform local space-time
`L³` bound for every sufficiently small positive Navier–Stokes rescaling. -/
theorem blowupRescaledVelocity_eventually_bounded_pastBox
    (u : ParabolicPoint → Vec3)
    (hu : AEStronglyMeasurable u (volume : Measure ParabolicPoint))
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hsource : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable (fun x : Vec3 => u (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,s))) 3 volume ≤ M)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ᶠ k in atTop,
        eLpNorm (fun z => vec3EuclideanNorm
          (parabolicRescaleVelocity x₀ t₀ (r k) u z))
          3 (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ B := by
  let J := Ioo a 0
  let C := vec3Ball (0 : Vec3) R ×ˢ J
  let μfull : Measure (Vec3 × ℝ) :=
    (volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict J)
  let B : ℝ≥0∞ := (volume J * M ^ (3 : ℝ)) ^ (1 / 3 : ℝ)
  have hJmeas : MeasurableSet J := measurableSet_Ioo
  have hJfin : volume J < ⊤ := by dsimp [J]; simp
  have hB : B < ⊤ := by
    dsimp [B]
    apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    exact (ENNReal.mul_lt_top hJfin
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM.ne)).ne
  have htimeLim : Tendsto (fun k => (r k) ^ 2 * (-a)) atTop (nhds 0) := by
    simpa using (hr0.pow 2).mul_const (-a)
  have htime : ∀ᶠ k in atTop, (r k) ^ 2 * (-a) < 3 / 4 :=
    htimeLim.eventually (eventually_lt_nhds (by norm_num))
  have hmeasure : volume.restrict C ≤ μfull := by
    change (volume.prod volume).restrict C ≤ μfull
    rw [show μfull = (volume.prod volume).restrict
        ((Set.univ : Set Vec3) ×ˢ J) by
      simp only [μfull, Measure.prod_restrict]]
    exact Measure.restrict_mono (Set.prod_mono (Set.subset_univ _) Subset.rfl) le_rfl
  refine ⟨B, hB, ?_⟩
  filter_upwards [htime] with k htk
  have hJ : J ⊆ CKN.rescaledTime (r k) t₀ (Ioo (-1 : ℝ) 0) :=
    blowupPastInterval_subset_source t₀ (r k) a ht₀ (hr k) htk
  let g : ParabolicPoint → ℝ := fun z =>
    vec3EuclideanNorm (parabolicRescaleVelocity x₀ t₀ (r k) u z)
  have hgm : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => g (z.1,z.2)) μfull :=
    blowupRescaledVelocity_norm_aestronglyMeasurable_prod
      u hu x₀ t₀ (r k) (hr k) J
  have hmass := blowupRescaledVelocity_spaceTime_mass_bound
    u x₀ t₀ (r k) (hr k) J hJ M hsource hgm
  have heq : eLpNorm g 3 μfull =
      (∫⁻ z : Vec3 × ℝ, ENNReal.ofReal (g (z.1,z.2)) ^ (3 : ℝ)
        ∂μfull) ^ (1 / 3 : ℝ) := by
    change eLpNorm (fun z : Vec3 × ℝ => g (z.1,z.2)) 3 μfull = _
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (3 : ℝ≥0∞) ≠ 0)
      (by finiteness : (3 : ℝ≥0∞) ≠ ⊤) hgm]
    norm_num
    simp only [Real.enorm_eq_ofReal_abs, g,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
  calc
    eLpNorm g 3 (volume.restrict C) ≤ eLpNorm g 3 μfull :=
      eLpNorm_mono_measure g hmeasure
    _ = (∫⁻ z : Vec3 × ℝ, ENNReal.ofReal (g (z.1,z.2)) ^ (3 : ℝ)
        ∂μfull) ^ (1 / 3 : ℝ) := heq
    _ ≤ B := by
      dsimp [B]
      exact ENNReal.rpow_le_rpow (by simpa only [g, μfull] using hmass)
        (by norm_num)

end ESS
