/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyExhaustion
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyStages
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyStrong
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblySuitable
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyTrace
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyLimitSlices
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyPressure
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitPairingAllTests
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitSliceBounds
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitBadPoint
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupVelocityMeas
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureMeasSource

/-!
# The blow-up limit

`prop:blowup-limit` in the form used by the proof of `thm:ess-local`:
at a point that is not good, every sequence of scales tending to zero has a
blow-up limit that is a suitable weak solution on every bounded past
cylinder, has weak spatial gradients on almost every slice, lies in
L^∞((-T,0); L³) for every T, has a pressure in L^(3/2) on every past slab,
has zero terminal trace, and cannot vanish on the past of the unit cylinder
(the bad-point lower bound).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem blowupLimitAssembly_badPoint_contradiction
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hbad : ¬ IsGoodPoint ε₀ u p (x₀,t₀))
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (nhds 0))
    (hind : AEStronglyMeasurable (goodPointDomain.indicator u) volume)
    (hpmeas : ∀ k, AEStronglyMeasurable (blowupPressure x₀ t₀ (r k) p)
      (volume : Measure ParabolicPoint))
    (U : ParabolicPoint → Vec3)
    (hU0 : U =ᵐ[volume.restrict
      (spaceTimeSet Set.univ (Ioo (-2 : ℝ) 0))] 0)
    (hconvU : ∀ R : ℝ, 0 < R → ∀ a : ℝ, a < 0 →
      Tendsto (fun k => eLpNorm (fun z => blowupVelocity x₀ t₀ (r k) u z - U z) 3
        (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0))) atTop (nhds 0))
    {q : ParabolicPoint → ℝ}
    (hconvP : ∀ R : ℝ, 0 < R → ∀ a : ℝ, a < 0 →
      Tendsto (fun k => eLpNorm (fun z => blowupPressure x₀ t₀ (r k) p z - q z)
        (3 / 2 : ℝ≥0∞) (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)))
        atTop (nhds 0))
    (hqzero : q =ᵐ[volume.restrict
      (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 0)] 0) : False := by
  have hlower := blowup_limit_bad_point_lower_bound ε₀ u p x₀ t₀ r hx₀ ht₀ hbad hr hr0
  have hQ1 : goodPointPastCylinder 0 0 1 = vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 0 := by
    rw [goodPointPastCylinder]
    congr 1
    norm_num
  have hQ1m : MeasurableSet (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 0) :=
    (isOpen_vec3Ball _ _).measurableSet.prod measurableSet_Ioo
  have hQ1sub : vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 0 ⊆
      spaceTimeSet Set.univ (Ioo (-2 : ℝ) 0) := fun z hz =>
    ⟨mem_univ _, by linarith only [hz.2.1], hz.2.2⟩
  have hU0' : U =ᵐ[volume.restrict (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 0)] 0 :=
    ae_restrict_of_ae_restrict_of_subset hQ1sub hU0
  have hvmeas : ∀ k, AEStronglyMeasurable (blowupVelocity x₀ t₀ (r k) u)
      (volume : Measure ParabolicPoint) := fun k =>
    blowupRescaledVelocity_aestronglyMeasurable _ hind x₀ t₀ (r k) (hr k)
  have hzero := blowup_limit_zero_alternative
    (fun k => blowupVelocity x₀ t₀ (r k) u)
    (fun k => blowupPressure x₀ t₀ (r k) p)
    (fun k => (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      (hvmeas k)).restrict)
    (fun k => (hpmeas k).restrict) ?_ ?_
  · have hlower' : Tendsto (fun k => goodPointEnergy
        (blowupVelocity x₀ t₀ (r k) u) (blowupPressure x₀ t₀ (r k) p) 0 0 1)
        atTop (nhds 0) := hzero
    have hlim : ENNReal.ofReal (ε₀ / 8) ≤ 0 := ge_of_tendsto hlower' hlower
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε₀ / 8) :=
      ENNReal.ofReal_pos.mpr (by linarith only [hε₀])
    exact absurd (hpos.trans_le hlim) (lt_irrefl 0)
  · rw [hQ1]
    have hlim3 : Tendsto (fun k => ENNReal.ofReal (Real.sqrt 3) *
        eLpNorm (fun z => blowupVelocity x₀ t₀ (r k) u z - U z) 3
          (volume.restrict (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 0)))
        atTop (nhds 0) := by
      have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.sqrt 3))
        (hconvU 1 one_pos (-1) (by norm_num)) (Or.inr ENNReal.ofReal_ne_top)
      rwa [mul_zero] at h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim3
    · exact fun k => zero_le
    · intro k
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
          (hvmeas k)).restrict
      filter_upwards [hU0'] with z hz
      have hz' : U z = 0 := hz
      rw [hz', sub_zero, Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      exact vec3EuclideanNorm_le_sqrt_three_mul_norm _
  · rw [hQ1]
    apply (hconvP 1 one_pos (-1) (by norm_num)).congr'
    filter_upwards [] with k
    apply eLpNorm_congr_ae
    filter_upwards [hqzero] with z hz
    have hz' : q z = 0 := hz
    rw [hz', sub_zero]

/-- The blow-up limit at a point that is not good (`prop:blowup-limit`),
under the hypotheses of `thm:ess-local`. -/
theorem blowupLimit_projection
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hp : AEStronglyMeasurable p
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL2 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i))
    (hS2 : ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
    (hS3 : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0) :
    ∀ (ε₀ : ℝ), 0 < ε₀ →
      ∀ (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ),
        x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)) →
        t₀ ∈ Icc (-(1 / 4 : ℝ)) 0 →
        ¬ IsGoodPoint ε₀ u p (x₀, t₀) →
        (∀ k, 0 < r k) → Tendsto r atTop (nhds 0) →
        ∃ (U : ParabolicPoint → Vec3)
          (DU : ParabolicPoint → Fin 3 → Vec3)
          (q : ParabolicPoint → ℝ),
          Measurable U ∧
          (∀ (R a : ℝ), 0 < R → a < 0 →
            IsSuitableWeakSolution (vec3Ball 0 R) (Ioo a 0) 3
              U DU q (0 : ParabolicPoint → Vec3)) ∧
          (∀ᵐ t ∂(volume.restrict (Ioo (-2 : ℝ) 0)),
            ∀ i : Fin 3,
              HasWeakGradientOn Set.univ
                (fun x : Vec3 => U (x, t) i)
                (fun x : Vec3 => DU (x, t) i)) ∧
          (∀ T : ℝ, 0 < T →
            essSup (fun t : ℝ => eLpNorm
              (fun x : Vec3 => vec3EuclideanNorm (U (x, t)))
              (3 : ℝ≥0∞) volume)
              (volume.restrict (Ioo (-T) 0)) < ⊤) ∧
          (∀ T : ℝ, 0 < T →
            MemLp q (3 / 2 : ℝ≥0∞)
              (volume.restrict
                (spaceTimeSet Set.univ (Ioo (-T) 0)))) ∧
          HasZeroDistributionalVelocityTrace U ∧
          (U =ᵐ[volume.restrict
              (spaceTimeSet Set.univ (Ioo (-2 : ℝ) 0))] 0 →
            Tendsto (fun k =>
              goodPointEnergy (blowupVelocity x₀ t₀ (r k) u)
                (blowupPressure x₀ t₀ (r k) p) 0 0 1)
              atTop (nhds 0)) := by
  intro ε₀ hε₀ x₀ t₀ r hx₀ ht₀ hbad hr hr0
  obtain ⟨v, W, hvbound, hWm, hW, htrace, -, hformula⟩ :=
    blowup_limit_source_pairing_formulas_with_trace hu hDu henergy hpLp hL3 hgrad hS3
  set Mt : ℝ := (weakContL3MomentBound (u := u)).toReal
  have hsourceW := blowupLimitAssembly_trace_indicator_bound v W Mt hvbound hW
  obtain ⟨Dm, hDm, -, hDmEq⟩ := blowupLimitAssembly_exists_measurable_version hDu
  obtain ⟨um, hum, hu_um, -⟩ := blowupLimitAssembly_exists_measurable_version hu
  have hxnorm : vec3EuclideanNorm x₀ ≤ 1 / 2 := by
    have h := hx₀
    rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] at h
    simpa only [Set.mem_ofPred_eq, sub_zero] using h
  set f : ℕ → ParabolicPoint → Vec3 := fun n => blowupLimitTraceRescaling W x₀ t₀ (r n)
  set Df : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n => blowupGradient x₀ t₀ (r n) Dm
  have hfm : ∀ n, Measurable (f n) := fun n =>
    measurable_blowupLimitTraceRescaling W hWm x₀ t₀ (r n)
  have hDfm : ∀ n, Measurable (Df n) := fun n =>
    measurable_blowupLimitAssembly_blowupGradient hDm x₀ t₀ (r n)
  have hstage := blowupLimitAssembly_trace_stages hu hDu hp hL2 henergy hpLp hL3 hgrad
    hS2 hS3 x₀ t₀ r hx₀ ht₀ hr hr0 v W hWm hW htrace hformula Dm hDm hDmEq
  obtain ⟨φ, hφ, U, hU, DU, hDU, hD1, hD2, hD3, hD4, hD5⟩ :=
    blowupLimitAssembly_exhaustion_compactness f Df hfm hDfm
      (fun C hC => blowupLimitAssembly_trace_compact_slice_bound W Mt hsourceW x₀ t₀ r hr
        C hC) hstage
  set r' : ℕ → ℝ := fun k => r (φ k)
  have hr' : ∀ k, 0 < r' k := fun k => hr (φ k)
  have hr0' : Tendsto r' atTop (nhds 0) := hr0.comp hφ.tendsto_atTop
  have hconvU : ∀ R : ℝ, 0 < R → ∀ a : ℝ, a < 0 →
      Tendsto (fun k => eLpNorm (fun z => blowupVelocity x₀ t₀ (r' k) u z - U z) 3
        (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0))) atTop (nhds 0) :=
    fun R hR a ha => blowupLimitAssembly_strong_Lthree hu hDu hp hL2 henergy hpLp hL3
      hgrad hS2 hS3 x₀ t₀ r' hx₀ ht₀ hr' hr0' hum hu_um W hWm htrace U hD2 R a hR ha
  -- the critical slice bound of the limit
  have hconvV : ∀ N : ℕ, Tendsto (fun k => eLpNorm (fun z => f (φ k) z - U z) 3
      (volume.restrict (vec3Ball (0 : Vec3) ((N : ℝ) + 1) ×ˢ
        Ioo (-((N : ℝ) + 1)) 0))) atTop (nhds 0) := by
    intro N
    set R : ℝ := (N : ℝ) + 1
    have hR : 0 < R := by positivity
    apply (hconvU R hR (-R) (by linarith only [hR])).congr'
    have hspaceLim : Tendsto (fun k => r' k * R) atTop (nhds 0) := by
      simpa only [zero_mul] using hr0'.mul_const R
    have htimeLim : Tendsto (fun k => (r' k) ^ 2 * (-(-R))) atTop (nhds 0) := by
      simpa using (hr0'.pow 2).mul_const (-(-R))
    filter_upwards [hspaceLim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      htimeLim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
      with k hsk htk
    have hae := blowupLimitAssembly_trace_ae_eq_blowupVelocity hum hu_um W hWm htrace
      hxnorm ht₀ (hr' k) hsk htk
    apply eLpNorm_congr_ae
    filter_upwards [hae] with z hz
    simp only [f, r'] at hz ⊢
    rw [hz]
  have hUslice := blowupLimitAssembly_slice_Lthree_of_local_convergence U hU
    (fun k => f (φ k)) (fun k => hfm (φ k)) (ENNReal.ofReal Mt)
    (fun k t => blowupLimitAssembly_trace_slice_Lthree W Mt hsourceW x₀ t₀ (r (φ k))
      (hr _) t) hconvV
  -- the pressure limit
  obtain ⟨q, -, hqMem, hconvP, hqzero⟩ := blowupLimitAssembly_pressure_limit hu hDu hp hL2
    henergy hpLp hL3 hgrad hS2 hS3 x₀ t₀ r' hx₀ ht₀ hr' hr0' U hU (ENNReal.ofReal Mt)
    ENNReal.ofReal_lt_top hUslice hconvU
  refine ⟨U, DU, q, hU, ?_, ?_, ?_, hqMem, ?_, ?_⟩
  · -- suitability
    intro R a hR ha
    exact blowupLimitAssembly_limit_suitable hu hDu hp hL2 henergy hpLp hL3 hgrad hS2 hS3
      x₀ t₀ r' hx₀ ht₀ hr' hr0' hum hu_um W hWm htrace Mt hsourceW Dm hDmEq U DU q hD5
      hconvU hD3 hconvP R a hR ha
  · -- weak gradients
    exact ae_restrict_of_ae_restrict_of_subset
      (fun t ht => (ht.2 : t < 0)) hD4
  · -- the critical slice bound
    intro T hT
    refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := Mt))
    exact essSup_le_of_ae_le _
      (ae_restrict_of_ae_restrict_of_subset (fun t ht => (ht.2 : t < 0)) hUslice)
  · -- the zero terminal trace
    have ht₀' : t₀ ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0 :=
      ⟨by linarith only [ht₀.1], ht₀.2⟩
    apply blowupLimitAssembly_zero_trace U (fun k => f (φ k)) hD1
    · intro ψ hψ hψc
      set w : Vec3 → L2Vec3 := fun x => WithLp.toLp 2 (ψ x)
      have hw : ContDiff ℝ (⊤ : ℕ∞) w :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp hψ
      have hwc : HasCompactSupport w := hψc.comp_left (by simp)
      have hwsupp : tsupport w ⊆ tsupport ψ := tsupport_comp_subset (by simp) ψ
      obtain ⟨ρ, hρ⟩ := (hψc : IsCompact (tsupport ψ)).exists_bound_of_continuousOn
        CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.continuousOn
      obtain ⟨m, hm⟩ := exists_nat_gt ρ
      have hsub : tsupport ψ ⊆ vec3Ball (0 : Vec3) ((m : ℝ) + 1) := by
        intro x hx
        have h := hρ x hx
        rw [Real.norm_eq_abs] at h
        rw [mem_vec3Ball, sub_zero]
        linarith only [(le_abs_self _).trans h, hm]
      obtain ⟨N, -, -, hmod⟩ := hstage m
      obtain ⟨A, B, θ, hA, hB, hθ, hbound⟩ := hmod (tsupport ψ) hψc hsub (-1) 0
        (fun t ht => ⟨by
          have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith only [ht.1, this], ht.2⟩) w hw hwc hwsupp
      refine ⟨A, B, θ, hA, hB, hθ, ?_⟩
      filter_upwards [eventually_ge_atTop N] with k hk s t hs ht
      exact hbound (φ k) (hk.trans (hφ.id_le k)) s t hs ht
    · intro ψ hψ hψc
      apply blowupLimitAssembly_pairing_tendsto_zero_of_unit_balls
        (fun k x => f (φ k) (x, 0))
        (fun k => ((hfm (φ k)).comp measurable_prodMk_right).aestronglyMeasurable)
        _ ψ hψ.continuous hψc
      intro c
      have h := blowup_limit_trace_terminal_rescaling_tendsto_zero W
        (fun t => (hsourceW t).1) ⟨t₀, ht₀'⟩ x₀ c r' hr' hr0'
      apply h.congr'
      filter_upwards [] with k
      congr 1
      funext x
      by_cases hx : x₀ + r' k • x ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ)
      · simp [f, r', blowupLimitTraceRescaling, blowupLimitTraceZeroExtension,
          parabolicTranslate, parabolicScale, hx, ht₀']
      · simp [f, r', blowupLimitTraceRescaling, blowupLimitTraceZeroExtension,
          parabolicTranslate, parabolicScale, hx]
  · -- the bad-point alternative
    intro hU0
    exfalso
    obtain ⟨-, hind, hp₁, -, -, hp₂, -⟩ := blowupLimitAssembly_source_pressure_data hu hDu
      hp hL2 henergy hpLp hL3 hgrad hS2 hS3
    have hpmeas : ∀ k, AEStronglyMeasurable (blowupPressure x₀ t₀ (r' k) p)
        (volume : Measure ParabolicPoint) := fun k =>
      blowupPressure_aestronglyMeasurable_of_split p _ hp₁ hp₂ x₀ t₀ (r' k) (hr' k)
    exact blowupLimitAssembly_badPoint_contradiction ε₀ hε₀ x₀ t₀ r' hx₀ ht₀ hbad
      hr' hr0' hind hpmeas U hU0 hconvU hconvP (hqzero hU0)

end ESS

end
