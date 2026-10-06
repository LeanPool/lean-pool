/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblySourcePressure
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyStageEnergy
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupCompactnessSource

/-!
# Strong L³ convergence of the blow-up velocities up to time zero

Local strong L² convergence of the rescaled trace below time zero, the
uniform L^(10/3) bound, and agreement of the trace with the zero-extended
rescaled velocity give strong L³ convergence of the blow-up velocities on
every bounded cylinder with open top at time zero (`prop:blowup-limit`).
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Strong local L³ convergence of the blow-up velocities, including the
top strip, from strong local L² convergence of the rescaled trace. -/
theorem blowupLimitAssembly_strong_Lthree
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hpmeas : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL2 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ‖u (x,t)‖ₑ ^ (2 : ℝ)) (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1) (fun x => u (x,t) i)
        (fun x => Du (x,t) i))
    (hS2 : ∀ ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
    (hS3 : ∀ φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (nhds 0))
    {um : ParabolicPoint → Vec3} (hum : Measurable um)
    (hu_um : u =ᵐ[volume.restrict
      (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))] um)
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3) (hWmeas : Measurable W)
    (htrace : ∀ᵐ t ∂(volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)),
      ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (fun x => W (x,⟨t,ht⟩)) =ᵐ[volume.restrict
          (vec3Ball (0 : Vec3) (3 / 4 : ℝ))] (fun x => u (x,t)))
    (U : ParabolicPoint → Vec3)
    (hlocal : ∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆ univ ×ˢ Iio 0 →
      Tendsto (fun k => eLpNorm
        (fun z => blowupLimitTraceRescaling W x₀ t₀ (r k) z - U z) 2
        (volume.restrict Q)) atTop (nhds 0))
    (R a : ℝ) (hR : 0 < R) (ha : a < 0) :
    Tendsto (fun k => eLpNorm (fun z => blowupVelocity x₀ t₀ (r k) u z - U z) 3
      (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0))) atTop (nhds 0) := by
  obtain ⟨hSuit, hind, hp₁, ⟨Mᵤ, hMᵤ, hsU⟩, ⟨Mₚ, hMₚ, hsP⟩, hp₂, hharm⟩ :=
    blowupLimitAssembly_source_pressure_data hu hDu hpmeas hL2 henergy hpLp hL3
      hgrad hS2 hS3
  have hxnorm : vec3EuclideanNorm x₀ ≤ 1 / 2 := by
    rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] at hx₀
    simpa only [Set.mem_ofPred_eq, sub_zero] using hx₀
  have hspaceLim : Tendsto (fun k => r k * R) atTop (nhds 0) := by
    simpa only [zero_mul] using hr0.mul_const R
  have htimeLim : Tendsto (fun k => (r k) ^ 2 * (-a)) atTop (nhds 0) := by
    simpa using (hr0.pow 2).mul_const (-a)
  have hspace : ∀ᶠ k in atTop, r k * R < 1 / 4 :=
    hspaceLim.eventually (eventually_lt_nhds (by norm_num))
  have htime : ∀ᶠ k in atTop, (r k) ^ 2 * (-a) < 1 / 4 :=
    htimeLim.eventually (eventually_lt_nhds (by norm_num))
  have hlocalParab : ∀ b : ℝ, b < 0 →
      Tendsto (fun k => eLpNorm
        (fun z => parabolicRescaleVelocity x₀ t₀ (r k) u z - U z) 2
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a b))) atTop (nhds 0) := by
    intro b hb
    set Q : Set (Vec3 × ℝ) := closure (vec3Ball (0 : Vec3) R) ×ˢ Icc a b
    have hQ : IsCompact Q := (isCompact_closure_vec3Ball hR).prod isCompact_Icc
    have hQI : Q ⊆ univ ×ˢ Iio 0 := fun z hz => ⟨mem_univ _, hz.2.2.trans_lt hb⟩
    have hsub : vec3Ball (0 : Vec3) R ×ˢ Ioo a b ⊆ Q :=
      prod_mono subset_closure Ioo_subset_Icc_self
    have hsub' : vec3Ball (0 : Vec3) R ×ˢ Ioo a b ⊆ vec3Ball (0 : Vec3) R ×ˢ Ioo a 0 :=
      prod_mono subset_rfl (Ioo_subset_Ioo_right hb.le)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hlocal Q hQ hQI)
    · exact Eventually.of_forall fun k => zero_le
    · filter_upwards [hspace, htime] with k hsk htk
      have hae := blowupLimitAssembly_trace_ae_eq_blowupVelocity hum hu_um W hWmeas
        htrace hxnorm ht₀ (hr k) hsk htk
      have heqOn := (blowupFields_eq_rescale_on_cylinder u Du p x₀ t₀ (r k) R a
        hxnorm ht₀ (hr k) hsk (by linarith only [htk])).1
      have hmeas : MeasurableSet (vec3Ball (0 : Vec3) R ×ˢ Ioo a b) :=
        (isOpen_vec3Ball _ _).measurableSet.prod measurableSet_Ioo
      calc
        eLpNorm (fun z => parabolicRescaleVelocity x₀ t₀ (r k) u z - U z) 2
            (volume.restrict (vec3Ball 0 R ×ˢ Ioo a b)) =
            eLpNorm (fun z => blowupLimitTraceRescaling W x₀ t₀ (r k) z - U z) 2
              (volume.restrict (vec3Ball 0 R ×ˢ Ioo a b)) := by
          apply eLpNorm_congr_ae
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub' hae,
            ae_restrict_mem hmeas] with z hz hzC
          rw [hz, heqOn (hsub' hzC)]
        _ ≤ eLpNorm (fun z => blowupLimitTraceRescaling W x₀ t₀ (r k) z - U z) 2
              (volume.restrict Q) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hsub)
  have hparab := blowupRescale_strong_Lthree_to_time_zero_of_local_Ltwo u Du p _
    hSuit hind Mᵤ hMᵤ hsU hp₁ Mₚ hMₚ hsP hp₂ hharm x₀ t₀ r hx₀ ht₀ hr hr0
    R a hR ha U hlocalParab
  apply hparab.congr'
  filter_upwards [hspace, htime] with k hsk htk
  have heqOn := (blowupFields_eq_rescale_on_cylinder u Du p x₀ t₀ (r k) R a
    hxnorm ht₀ (hr k) hsk (by linarith only [htk])).1
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem
    ((isOpen_vec3Ball (0 : Vec3) R).measurableSet.prod measurableSet_Ioo)] with z hz
  rw [heqOn hz]

end ESS

end
