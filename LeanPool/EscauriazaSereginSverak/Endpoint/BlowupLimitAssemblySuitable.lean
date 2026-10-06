/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyLimitSlices
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyStageEnergy
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblySourcePressure
public import LeanPool.CaffarelliKohnNirenberg.Leray.Stability
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Suitability of the blow-up limit

The rescaled source solutions are suitable on each fixed bounded past
cylinder from some index on; with the local convergences of velocity,
gradient, and pressure, `thm:stability` of the CKN manuscript makes the blow-up limit suitable
there (`prop:blowup-limit`, the suitability step).
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A global L³ slice bound gives a local L² slice bound by Hölder's
inequality. -/
theorem blowupLimitAssembly_lintegral_sq_le_of_Lthree
    (g : Vec3 → Vec3) (hg : AEStronglyMeasurable g volume) (Ω' : Set Vec3)
    (M : ℝ≥0∞)
    (h3 : eLpNorm (fun x => vec3EuclideanNorm (g x)) 3 volume ≤ M) :
    (∫⁻ x in Ω', ‖g x‖ₑ ^ (2 : ℝ)) ≤ (M * volume Ω' ^ (1 / 6 : ℝ)) ^ (2 : ℝ) := by
  set μ : Measure Vec3 := volume.restrict Ω'
  have hsq : eLpNorm g ((2 : NNReal) : ℝ≥0∞) μ ^ ((2 : NNReal) : ℝ) =
      ∫⁻ x, ‖g x‖ₑ ^ ((2 : NNReal) : ℝ) ∂μ :=
    eLpNorm_nnreal_pow_eq_lintegral (by norm_num) hg.restrict
  have h2 : eLpNorm g 2 μ ≤ eLpNorm g 3 μ * μ univ ^
      (1 / (2 : ℝ≥0∞).toReal - 1 / (3 : ℝ≥0∞).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hg.restrict
  have h3' : eLpNorm g 3 μ ≤ M := by
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    refine (eLpNorm_mono hg fun x => ?_).trans h3
    rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact norm_le_vec3EuclideanNorm _
  have hexp : (1 / (2 : ℝ≥0∞).toReal - 1 / (3 : ℝ≥0∞).toReal) = (1 / 6 : ℝ) := by
    norm_num
  rw [hexp, Measure.restrict_apply_univ] at h2
  have hsq' : (∫⁻ x in Ω', ‖g x‖ₑ ^ (2 : ℝ)) = eLpNorm g 2 μ ^ (2 : ℝ) := by
    simpa using hsq.symm
  rw [hsq']
  gcongr
  exact h2.trans (by gcongr)

private theorem blowupLimitAssembly_localBox_geometry
    (R a : ℝ) (hR : 0 < R) (ha : a < 0) :
    ∀ Ω' J, localBox (vec3Ball (0 : Vec3) R) (Ioo a 0) Ω' J →
      spaceTimeSet Ω' J ⊆ vec3Ball (0 : Vec3) R ×ˢ Ioo a 0 ∧
      IsCompact (closure Ω' ×ˢ closure J) ∧
      closure Ω' ×ˢ closure J ⊆ (univ : Set Vec3) ×ˢ Iio (0 : ℝ) ∧
      spaceTimeSet Ω' J ⊆ closure Ω' ×ˢ closure J ∧
      MeasurableSet (spaceTimeSet Ω' J) := by
  intro Ω' J hbox
  obtain ⟨hΩo, hΩc, hΩsub, hJo, hJc, hJsub⟩ := hbox
  refine ⟨?_, hΩc.prod hJc, ?_, prod_mono subset_closure subset_closure,
    hΩo.measurableSet.prod hJo.measurableSet⟩
  · exact prod_mono (subset_closure.trans hΩsub) (subset_closure.trans hJsub)
  · intro z hz
    exact ⟨mem_univ _, (hJsub hz.2).2⟩

/-- The blow-up limit is a suitable weak solution on every bounded past
cylinder, by `thm:stability` of the CKN manuscript applied to a tail of the rescaled source
solutions. -/
theorem blowupLimitAssembly_limit_suitable
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
    (Mt : ℝ)
    (hsourceW : ∀ t,
      MemLp ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
        (fun x => W (x,t))) 3 volume ∧
      eLpNorm (fun x => vec3EuclideanNorm
        ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
          (fun y => W (y,t)) x)) 3 volume ≤ ENNReal.ofReal Mt)
    (Dm : ParabolicPoint → Fin 3 → Vec3)
    (hDmEq : goodPointDomain.indicator Dm =ᵐ[volume] goodPointDomain.indicator Du)
    (U : ParabolicPoint → Vec3) (DU : ParabolicPoint → Fin 3 → Vec3)
    (q : ParabolicPoint → ℝ)
    (hDU : ∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆ univ ×ˢ Iio 0 →
      MemLp DU 2 (volume.restrict Q))
    (hconvU : ∀ R : ℝ, 0 < R → ∀ a : ℝ, a < 0 →
      Tendsto (fun k => eLpNorm (fun z => blowupVelocity x₀ t₀ (r k) u z - U z) 3
        (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0))) atTop (nhds 0))
    (hconvD : ∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆ univ ×ˢ Iio 0 →
      ∀ i j : Fin 3, ∀ w : Vec3 × ℝ → ℝ, MemLp w 2 (volume.restrict Q) →
      Tendsto (fun k => ∫ z in Q, blowupGradient x₀ t₀ (r k) Dm z i j * w z) atTop
        (nhds (∫ z in Q, DU z i j * w z)))
    (hconvP : ∀ R : ℝ, 0 < R → ∀ a : ℝ, a < 0 →
      Tendsto (fun k => eLpNorm (fun z => blowupPressure x₀ t₀ (r k) p z - q z)
        (3 / 2 : ℝ≥0∞) (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)))
        atTop (nhds 0))
    (R a : ℝ) (hR : 0 < R) (ha : a < 0) :
    IsSuitableWeakSolution (vec3Ball 0 R) (Ioo a 0) 3 U DU q
      (0 : ParabolicPoint → Vec3) := by
  obtain ⟨hSuit, -⟩ := blowupLimitAssembly_source_pressure_data hu hDu hpmeas hL2
    henergy hpLp hL3 hgrad hS2 hS3
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
  have hsuitEv := blowupRescale_eventually_suitable_on_cylinder u Du p hSuit
    x₀ t₀ R a r hx₀ ht₀ hr hr0 hR ha
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hspace.and (htime.and hsuitEv))
  set C : Set ParabolicPoint := vec3Ball (0 : Vec3) R ×ˢ Ioo a 0
  have hCm : MeasurableSet C := (isOpen_vec3Ball _ _).measurableSet.prod measurableSet_Ioo
  have heqOn : ∀ n : ℕ,
      Set.EqOn (blowupVelocity x₀ t₀ (r (n + K)) u)
        (parabolicRescaleVelocity x₀ t₀ (r (n + K)) u) C ∧
      Set.EqOn (blowupGradient x₀ t₀ (r (n + K)) Du)
        (parabolicRescaleGradient x₀ t₀ (r (n + K)) Du) C ∧
      Set.EqOn (blowupPressure x₀ t₀ (r (n + K)) p)
        (parabolicRescalePressure x₀ t₀ (r (n + K)) p) C := by
    intro n
    obtain ⟨hs, ht, _⟩ := hK (n + K) (Nat.le_add_left K n)
    exact blowupFields_eq_rescale_on_cylinder u Du p x₀ t₀ (r (n + K)) R a hxnorm ht₀
      (hr _) hs (by linarith only [ht])
  have hboxsub := blowupLimitAssembly_localBox_geometry R a hR ha
  refine stability_suitable_limit
    (fun n => parabolicRescaleVelocity x₀ t₀ (r (n + K)) u)
    (fun n => parabolicRescaleGradient x₀ t₀ (r (n + K)) Du)
    (fun n => parabolicRescalePressure x₀ t₀ (r (n + K)) p) U DU q
    (fun n => (hK (n + K) (Nat.le_add_left K n)).2.2) ?_ ?_ ?_ ?_ ?_
  · -- uniform local slice bound
    intro Ω' J hbox
    obtain ⟨hsubC, -, -, -, hSm⟩ := hboxsub Ω' J hbox
    refine ⟨(ENNReal.ofReal Mt * volume Ω' ^ (1 / 6 : ℝ)) ^ (2 : ℝ), ?_, fun n => ?_⟩
    · have hΩvol : volume Ω' < ⊤ :=
        lt_of_le_of_lt (measure_mono subset_closure) hbox.2.1.measure_lt_top
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hΩvol.ne)).ne
    obtain ⟨hs, ht, _⟩ := hK (n + K) (Nat.le_add_left K n)
    have hae := blowupLimitAssembly_trace_ae_eq_blowupVelocity hum hu_um W hWmeas
      htrace hxnorm ht₀ (hr (n + K)) hs ht
    have hslices := blowupLimitAssembly_ae_slices_of_ae_spaceTime
      (Ω := Ω') (I := J) (ae_restrict_of_ae_restrict_of_subset hsubC hae)
    have hbd : ∀ᵐ t ∂(volume.restrict J), (∫⁻ x in Ω',
        ‖parabolicRescaleVelocity x₀ t₀ (r (n + K)) u (x,t)‖ₑ ^ (2 : ℝ)) ≤
        (ENNReal.ofReal Mt * volume Ω' ^ (1 / 6 : ℝ)) ^ (2 : ℝ) := by
      filter_upwards [hslices, ae_restrict_mem hbox.2.2.2.1.measurableSet] with t ht' htJ
      have hVmeas : Measurable (fun x : Vec3 =>
          blowupLimitTraceRescaling W x₀ t₀ (r (n + K)) (x,t)) :=
        (measurable_blowupLimitTraceRescaling W hWmeas x₀ t₀ _).comp
          measurable_prodMk_right
      calc
        (∫⁻ x in Ω', ‖parabolicRescaleVelocity x₀ t₀ (r (n + K)) u (x,t)‖ₑ ^ (2 : ℝ)) =
            ∫⁻ x in Ω', ‖blowupLimitTraceRescaling W x₀ t₀ (r (n + K)) (x,t)‖ₑ ^
              (2 : ℝ) := by
          apply lintegral_congr_ae
          filter_upwards [ht', ae_restrict_mem hbox.1.measurableSet] with x hx hxΩ
          have hxC : ((x,t) : ParabolicPoint) ∈ C := hsubC ⟨hxΩ, htJ⟩
          rw [hx, (heqOn n).1 hxC]
        _ ≤ (ENNReal.ofReal Mt * volume Ω' ^ (1 / 6 : ℝ)) ^ (2 : ℝ) :=
          blowupLimitAssembly_lintegral_sq_le_of_Lthree _ hVmeas.aestronglyMeasurable
            Ω' _ (blowupLimitAssembly_trace_slice_Lthree W Mt hsourceW x₀ t₀ _ (hr _) t)
    exact essSup_le_of_ae_le _ hbd
  · -- strong local velocity convergence
    intro Ω' J hbox
    obtain ⟨hsubC, -, -, -, -⟩ := hboxsub Ω' J hbox
    have hlim := (hconvU R hR a ha).comp (tendsto_add_atTop_nat K)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    · exact fun n => zero_le
    · intro n
      calc
        eLpNorm (parabolicRescaleVelocity x₀ t₀ (r (n + K)) u - U) 3
            (volume.restrict (spaceTimeSet Ω' J)) ≤
            eLpNorm (parabolicRescaleVelocity x₀ t₀ (r (n + K)) u - U) 3
              (volume.restrict C) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hsubC)
        _ = eLpNorm (fun z => blowupVelocity x₀ t₀ (r (n + K)) u z - U z) 3
              (volume.restrict C) := by
          apply eLpNorm_congr_ae
          filter_upwards [ae_restrict_mem hCm] with z hz
          simp only [Pi.sub_apply, (heqOn n).1 hz]
  · -- square integrability of the limit gradient
    intro Ω' J hbox
    obtain ⟨-, hQc, hQI, hsubQ, -⟩ := hboxsub Ω' J hbox
    exact (hDU _ hQc hQI).mono_measure (Measure.restrict_mono_set volume hsubQ)
  · -- weak gradient convergence
    intro Ω' J hbox i j w hw
    obtain ⟨hsubC, hQc, hQI, hsubQ, hSm⟩ := hboxsub Ω' J hbox
    set S : Set (Vec3 × ℝ) := Ω' ×ˢ J
    set Q : Set (Vec3 × ℝ) := closure Ω' ×ˢ closure J
    have hprodEq : (volume.restrict Ω').prod (volume.restrict J) =
        (volume : Measure (Vec3 × ℝ)).restrict S := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
    have hSm' : MeasurableSet S :=
      hbox.1.measurableSet.prod hbox.2.2.2.1.measurableSet
    have hsubQ' : S ⊆ Q := prod_mono subset_closure subset_closure
    rw [hprodEq] at hw ⊢
    have hw' : MemLp (S.indicator w) 2 (volume.restrict Q) :=
      ((memLp_indicator_iff_restrict hSm').2 hw).restrict Q
    have hlim := (hconvD Q hQc hQI i j (S.indicator w) hw').comp
      (tendsto_add_atTop_nat K)
    have hind : ∀ F : Vec3 × ℝ → ℝ,
        (∫ z in Q, F z * S.indicator w z) = ∫ z in S, F z * w z := by
      intro F
      have hpt : (fun z => F z * S.indicator w z) = S.indicator (fun z => F z * w z) := by
        funext z
        by_cases hz : z ∈ S
        · simp [indicator_of_mem hz]
        · simp [indicator_of_notMem hz]
      rw [hpt, setIntegral_indicator hSm', inter_eq_right.mpr hsubQ']
    simp only [Function.comp_def, hind] at hlim
    apply hlim.congr'
    filter_upwards [] with n
    apply integral_congr_ae
    have hae := blowupLimitAssembly_blowupGradient_ae_eq hDmEq x₀ t₀ (r (n + K)) (hr _)
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hSm] with z hz hzS
    have hzC : ((z.1, z.2) : ParabolicPoint) ∈ C := hsubC hzS
    change blowupGradient x₀ t₀ (r (n + K)) Dm z i j * w z =
      parabolicRescaleGradient x₀ t₀ (r (n + K)) Du (z.1, z.2) i j * w z
    rw [hz, ← (heqOn n).2.1 hzC]
  · -- strong local pressure convergence
    intro Ω' J hbox
    obtain ⟨hsubC, -, -, -, -⟩ := hboxsub Ω' J hbox
    have hlim := (hconvP R hR a ha).comp (tendsto_add_atTop_nat K)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    · exact fun n => zero_le
    · intro n
      calc
        eLpNorm (parabolicRescalePressure x₀ t₀ (r (n + K)) p - q) (3 / 2 : ℝ≥0∞)
            (volume.restrict (spaceTimeSet Ω' J)) ≤
            eLpNorm (parabolicRescalePressure x₀ t₀ (r (n + K)) p - q) (3 / 2 : ℝ≥0∞)
              (volume.restrict C) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hsubC)
        _ = eLpNorm (fun z => blowupPressure x₀ t₀ (r (n + K)) p z - q z)
              (3 / 2 : ℝ≥0∞) (volume.restrict C) := by
          apply eLpNorm_congr_ae
          filter_upwards [ae_restrict_mem hCm] with z hz
          simp only [Pi.sub_apply, (heqOn n).2.2 hz]

end ESS

end
