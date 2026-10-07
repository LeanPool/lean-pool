/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureAssembly

/-!
# Blowup Pressure Uniform

Pressure bounds and convergence estimates for the rescaled sequence.
-/

public section

open MeasureTheory Filter Set CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- A uniform whole-space source pressure slice bound gives a uniform local
space-time bound for its parabolic rescalings. -/
theorem blowupRieszPressure_eventually_bounded_pastBox
    (p₁ : ParabolicPoint → ℝ)
    (hp₁ : AEStronglyMeasurable p₁
      (volume.restrict (Set.univ ×ˢ Ioo (-1 : ℝ) 0)))
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hsource : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable (fun x : Vec3 => p₁ (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => p₁ (x,s)) (3 / 2 : ℝ≥0∞) volume ≤ M)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ᶠ k in atTop,
        eLpNorm (blowupRieszPressure x₀ t₀ (r k) p₁)
          (3 / 2 : ℝ≥0∞)
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ B := by
  let J := Ioo a 0
  let C := vec3Ball (0 : Vec3) R ×ˢ J
  let μfull : Measure (Vec3 × ℝ) :=
    (volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict J)
  let B : ℝ≥0∞ := (volume J * M ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)
  have hJmeas : MeasurableSet J := measurableSet_Ioo
  have hJfin : volume J < ⊤ := by
    dsimp [J]
    simp
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
  let P := blowupRieszPressure x₀ t₀ (r k) p₁
  have hPm : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => P (z.1,z.2)) μfull := by
    have h := blowupRieszPressure_aestronglyMeasurable
      p₁ hp₁ x₀ t₀ (r k) (hr k)
    have h' := h.restrict (s := ((Set.univ : Set Vec3) ×ˢ J : Set ParabolicPoint))
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod] at h'
    change AEStronglyMeasurable (fun z : Vec3 × ℝ => P (z.1,z.2))
      ((volume.prod volume).restrict ((Set.univ : Set Vec3) ×ˢ J)) at h'
    simpa only [μfull, Measure.prod_restrict] using h'
  have hmass := blowupRieszPressure_spaceTime_mass_bound
    p₁ hp₁ x₀ t₀ (r k) (hr k) J hJmeas hJ M hsource
  have heq : eLpNorm P (3 / 2 : ℝ≥0∞) μfull =
      (∫⁻ z : Vec3 × ℝ, ENNReal.ofReal |P z| ^ (3 / 2 : ℝ)
        ∂μfull) ^ (2 / 3 : ℝ) := by
    change eLpNorm (fun z : Vec3 × ℝ => P (z.1,z.2))
      (3 / 2 : ℝ≥0∞) μfull =
      (∫⁻ z : Vec3 × ℝ, ENNReal.ofReal |P (z.1,z.2)| ^ (3 / 2 : ℝ)
        ∂μfull) ^ (2 / 3 : ℝ)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0)
      (by finiteness : (3 / 2 : ℝ≥0∞) ≠ ⊤) hPm]
    norm_num
    simp only [Real.enorm_eq_ofReal_abs]
  calc
    eLpNorm P (3 / 2 : ℝ≥0∞) (volume.restrict C) ≤
        eLpNorm P (3 / 2 : ℝ≥0∞) μfull :=
      eLpNorm_mono_measure P hmeasure
    _ = (∫⁻ z : Vec3 × ℝ, ENNReal.ofReal |P z| ^ (3 / 2 : ℝ)
          ∂μfull) ^ (2 / 3 : ℝ) := heq
    _ ≤ B := by
      dsimp [B]
      exact ENNReal.rpow_le_rpow (by simpa only [P, μfull] using hmass)
        (by norm_num)

/-- The fixed harmonic pressure split gives an eventual local
`L^(3/2)` bound for the full rescaled pressure. -/
theorem blowupPressure_eventually_bounded_pastBox
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
    ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ᶠ k in atTop,
        eLpNorm (blowupPressure x₀ t₀ (r k) p)
          (3 / 2 : ℝ≥0∞)
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ B := by
  let C := vec3Ball 0 R ×ˢ Ioo a 0
  have hsplit := blowup_pressure_split_eventually_pastBox
    p p₁ x₀ t₀ r hx₀ ht₀ hr hr0 R a
  have hsplitAE : ∀ᶠ k in atTop,
      blowupPressure x₀ t₀ (r k) p =ᵐ[volume.restrict C]
        fun z => blowupRieszPressure x₀ t₀ (r k) p₁ z +
          blowupPressureRemainder x₀ t₀ (r k) p p₁ z := by
    filter_upwards [hsplit] with k hk
    filter_upwards [ae_restrict_mem
      ((isOpen_vec3Ball 0 R).measurableSet.prod measurableSet_Ioo)] with z hz
    exact hk z hz
  exact blowup_pressure_eventually_bounded_of_split (volume.restrict C)
    (fun k => blowupPressure x₀ t₀ (r k) p)
    (fun k => blowupRieszPressure x₀ t₀ (r k) p₁)
    (fun k => blowupPressureRemainder x₀ t₀ (r k) p p₁)
    hsplitAE
    (blowupRieszPressure_eventually_bounded_pastBox
      p₁ hp₁ M hM hsource x₀ t₀ r ht₀ hr hr0 R a)
    (blowupPressureRemainder_eLpNorm_tendsto_zero_pastBox
      p p₁ hp₂ hharm x₀ t₀ r hx₀ hr hr0 R a hR ha)

end ESS
