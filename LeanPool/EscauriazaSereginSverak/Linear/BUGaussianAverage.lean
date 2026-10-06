/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianAverageBase
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianAverageTools
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianFactorBound
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianErrorAssembly
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianFinalBridge
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCutoff
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCutoffBridge
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCutoffSupport
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianChangeBack
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianData
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianOperatorLocalized
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCarleman
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianParameters
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianInitialTrace
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianShellCaccioppoli
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianRadialMass
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianWeights
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEnergyL2
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortHeatL2
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEarlyIntegral
public import LeanPool.EscauriazaSereginSverak.Linear.UCTrace
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests

/-!
# The Gaussian average estimate for backward uniqueness

The cutoff equals the translated field on the normalized averaging box in
`lem:bu-gaussian`.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

private theorem buGaussian_initial_error_cancel
    (ε W q : ℝ) (hε : ε ≠ 0) (hW : W ≠ 0) :
    (256 / ε ^ 2) * (W * ((q / (256 * W)) * ε ^ 2)) = q := by
  field_simp [hε, hW]

private theorem carleman_energy_controls_average_box
    {Q K : Set ParabolicPoint} (hQ : MeasurableSet Q)
    (hQsub : Q ⊆ K) {V E : ParabolicPoint → ℝ}
    (hV : Integrable V (volume.restrict Q))
    (hE : Integrable E (volume.restrict K))
    (hEnonneg : 0 ≤ᵐ[volume.restrict K] E)
    (hdensity : ∀ z ∈ Q, Real.exp (-(3 / 2 : ℝ)) * V z ≤ E z) :
    Real.exp (-(3 / 2 : ℝ)) * (∫ z in Q, V z) ≤ ∫ z in K, E z ∧
      (∫ z in K, E z) ≤ c₀ * (∫ z in K, H z) := by
  have hEQ : Integrable E (volume.restrict Q) :=
    hE.mono_measure (Measure.restrict_mono hQsub le_rfl)
  have hdensityInt := setIntegral_mono_on (hV.const_mul _)
    hEQ hQ hdensity
  have hQtoK := setIntegral_mono_set hE hEnonneg (ae_of_all _ hQsub)
  calc
    _ = ∫ z in Q, Real.exp (-(3 / 2 : ℝ)) * V z := by
      rw [integral_const_mul]
    _ ≤ ∫ z in Q, E z := hdensityInt
    _ ≤ ∫ z in K, E z := hQtoK

private theorem gaussian_average_tail_error_integrals
    {K S₁ Sinit : Set ParabolicPoint}
    (hKmeas : MeasurableSet K) (hKfinite : volume K < ⊤)
    {ρ T : ℝ} (hKvolume : (volume K).toReal ≤ 12 * ρ ^ 3)
    (hTnonneg : 0 ≤ T) (hKsubS₁ : K ⊆ S₁)
    {lateMass initialMass shellMass radialMass Vsrc : ParabolicPoint → ℝ}
    (hLateMassInt : Integrable lateMass (volume.restrict K))
    (hLatePoint : ∀ z ∈ K, lateMass z ≤ T)
    (ε δ Wmax Ebase : ℝ) (hε : 0 < ε) (hWmax : 0 < Wmax)
    (hInitialMassInt : Integrable initialMass (volume.restrict K))
    (hInitialIntegral : (∫ z in K, initialMass z) ≤
      Wmax * (∫ z in Sinit, Vsrc z))
    (hInitialTrace : (∫ z in Sinit, Vsrc z) / ε ^ 2 < δ)
    (hCancel : (256 / ε ^ 2) * (Wmax * (δ * ε ^ 2)) = Ebase)
    (hBaseBound : Ebase ≤ T)
    (hShellMassInt : Integrable shellMass (volume.restrict K))
    (hRadialIntK : Integrable radialMass (volume.restrict K))
    (hShellPoint : ∀ z ∈ K, shellMass z ≤ radialMass z)
    (hRadialInt : Integrable radialMass (volume.restrict S₁))
    (hRadialNonneg : 0 ≤ᵐ[volume.restrict S₁] radialMass)
    (hRadialTail : (∫ z in S₁, radialMass z) ≤ 24 * ρ ^ 3 * T) :
    (∫ z in K, lateMass z) ≤ 12 * ρ ^ 3 * T ∧
    (256 / ε ^ 2) * (∫ z in K, initialMass z) ≤ T ∧
    (∫ z in K, shellMass z) ≤ 24 * ρ ^ 3 * T := by
  have hconstInt : Integrable (fun _ : ParabolicPoint => T)
      (volume.restrict K) := integrableOn_const hKfinite.ne
  have hlate := setIntegral_mono_on hLateMassInt hconstInt hKmeas hLatePoint
  rw [setIntegral_const] at hlate
  have hvol := mul_le_mul_of_nonneg_left hKvolume hTnonneg
  have hlate' : (∫ z in K, lateMass z) ≤ T * (volume K).toReal := by
    simpa [Measure.real, smul_eq_mul, mul_comm] using hlate
  have hεsq : 0 < ε ^ 2 := by positivity
  have hmass : (∫ z in Sinit, Vsrc z) ≤ δ * ε ^ 2 :=
    (div_le_iff₀ hεsq).mp hInitialTrace.le
  have hcoeff : 0 ≤ 256 / ε ^ 2 := by positivity
  have hInitialStep1 : (256 / ε ^ 2) * (∫ z in K, initialMass z) ≤
      (256 / ε ^ 2) * (Wmax * (∫ z in Sinit, Vsrc z)) :=
    mul_le_mul_of_nonneg_left hInitialIntegral hcoeff
  have hInitialStep2 : (256 / ε ^ 2) * (Wmax * (∫ z in Sinit, Vsrc z)) ≤
      (256 / ε ^ 2) * (Wmax * (δ * ε ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ hcoeff
    exact mul_le_mul_of_nonneg_left hmass hWmax.le
  have hInitial : (256 / ε ^ 2) * (∫ z in K, initialMass z) ≤ T :=
    (hInitialStep1.trans (hInitialStep2.trans (le_of_eq hCancel))).trans hBaseBound
  have hShell1 := setIntegral_mono_on hShellMassInt hRadialIntK
    hKmeas hShellPoint
  have hShell2 := setIntegral_mono_set hRadialInt hRadialNonneg
    (ae_of_all _ hKsubS₁)
  have hLateFinal : (∫ z in K, lateMass z) ≤ 12 * ρ ^ 3 * T := by
    calc
      _ ≤ T * (volume K).toReal := hlate'
      _ ≤ T * (12 * ρ ^ 3) := hvol
      _ = 12 * ρ ^ 3 * T := by ring
  exact ⟨hLateFinal, hInitial, hShell1.trans (hShell2.trans hRadialTail)⟩

private theorem gaussian_late_weighted_mass_point_bound
    (A barA β ρ a scale Tbound : ℝ) (x : Vec3)
    (v : ParabolicPoint → Vec3) (hA : 0 ≤ A)
    (hAmax : A ≤ 1 / (10 : ℝ) ^ 12) (hAbar : A ≤ barA)
    (hscaleSqLe : scale ^ 2 ≤ 1 / 4)
    (haeq : a = β * ρ ^ 2 / buGaussianH)
    (hTbound : Tbound = Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
      Real.exp (-2 * β * ρ ^ 2)) (hTboundNonneg : 0 ≤ Tbound)
    (z : ParabolicPoint) (hslow : 3 / 2 ≤ z.2) (hshi : z.2 ≤ 2)
    (hgrowth : vec3EuclideanNorm (v z) ≤
      Real.exp (2 * A * vec3EuclideanNorm x ^ 2 +
        2 * A * scale ^ 2 * vec3EuclideanNorm z.1 ^ 2)) :
    ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2 ≤ Tbound := by
  have hsmall := buGaussian_source_spatial_absorption
    hA hAmax hscaleSqLe hslow hshi
  have hendpoint := buGaussian_time_weight_endpoint haeq
  have hpoint := buGaussian_omega2_pointwise_bound
    (a := a) (β := β) (ρ := ρ) (A := A) (barA := barA)
    (scale := scale) (s := z.2) (x := x) (y := z.1)
    (by linarith : 0 ≤ a) hA hAbar hslow hshi hsmall hendpoint
    (v z) hgrowth
  have hpoint' : ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2 ≤
      Tbound * Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (8 * z.2)) := by
    simpa [hTbound, ucGaussianWeight] using hpoint
  have hspos : 0 < z.2 := by linarith only [hslow]
  have hexp : Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (8 * z.2)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hfrac : 0 ≤ vec3EuclideanNorm z.1 ^ 2 / (8 * z.2) := by positivity
    simpa only [neg_div] using neg_nonpos.mpr hfrac
  have hmul := mul_le_mul_of_nonneg_left hexp hTboundNonneg
  exact hpoint'.trans (by simpa using hmul)

private theorem gaussian_average_cutoff_error_major
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W V G car heat shell late initial : α → ℝ}
    {Shell Late Initial : Set α} (c scale shell0 shell1 ε : ℝ)
    (hε : ε ≠ 0)
    (hError : ∀ᵐ z ∂μ, heat z ≤
      72 * (c * scale) ^ 2 * car z +
        4 * W z * (shell z ^ 2 + late z ^ 2 + initial z ^ 2))
    (hW : ∀ᵐ z ∂μ, 0 ≤ W z)
    (hV : ∀ z, 0 ≤ V z) (hG : ∀ z, 0 ≤ G z)
    (hShell : ∀ z, shell z = if z ∈ Shell then
      shell0 * Real.sqrt (V z) + shell1 * Real.sqrt (G z) else 0)
    (hLate : ∀ z, late z = if z ∈ Late then 32 * Real.sqrt (V z) else 0)
    (hInitial : ∀ z, initial z = if z ∈ Initial then
      (8 / ε) * Real.sqrt (V z) else 0) :
    ∀ᵐ z ∂μ, heat z ≤ 72 * (c * scale) ^ 2 * car z +
      8 * shell0 ^ 2 * Shell.indicator (fun z => W z * V z) z +
      8 * shell1 ^ 2 * Shell.indicator (fun z => W z * G z) z +
      4096 * Late.indicator (fun z => W z * V z) z +
      (256 / ε ^ 2) * Initial.indicator (fun z => W z * V z) z := by
  filter_upwards [hError, hW] with z hErrorz hWz
  have hVnonneg := hV z
  have hGnonneg := hG z
  have hShellSq : 4 * W z * shell z ^ 2 ≤
      8 * shell0 ^ 2 * Shell.indicator (fun z => W z * V z) z +
        8 * shell1 ^ 2 * Shell.indicator (fun z => W z * G z) z := by
    by_cases hz : z ∈ Shell
    · rw [hShell, if_pos hz]
      have htwo : (shell0 * Real.sqrt (V z) +
          shell1 * Real.sqrt (G z)) ^ 2 ≤
          2 * shell0 ^ 2 * V z + 2 * shell1 ^ 2 * G z := by
        have hdiff := sq_nonneg
          (shell0 * Real.sqrt (V z) - shell1 * Real.sqrt (G z))
        have hsqrtV := Real.sq_sqrt hVnonneg
        have hsqrtG := Real.sq_sqrt hGnonneg
        nlinarith only [hdiff, hsqrtV, hsqrtG]
      have hmul := mul_le_mul_of_nonneg_left htwo hWz
      simp [Set.indicator, hz] at hmul ⊢
      nlinarith only [hmul]
    · rw [hShell, if_neg hz]
      simp [Set.indicator, hz]
  have hLateSq : 4 * W z * late z ^ 2 =
      4096 * Late.indicator (fun z => W z * V z) z := by
    by_cases hz : z ∈ Late
    · rw [hLate, if_pos hz]
      simp [Set.indicator, hz, Real.sq_sqrt hVnonneg]
      ring
    · rw [hLate, if_neg hz]
      simp [Set.indicator, hz]
  have hInitialSq : 4 * W z * initial z ^ 2 =
      (256 / ε ^ 2) * Initial.indicator (fun z => W z * V z) z := by
    by_cases hz : z ∈ Initial
    · rw [hInitial, if_pos hz]
      simp [Set.indicator, hz, Real.sq_sqrt hVnonneg]
      field_simp [hε] <;> ring
    · rw [hInitial, if_neg hz]
      simp [Set.indicator, hz]
  nlinarith only [hErrorz, hShellSq, hLateSq, hInitialSq]

private theorem gaussian_carleman_cutoff_mass_lower
    {U K Q : Set ParabolicPoint}
    (hUmeas : MeasurableSet U) (hKmeas : MeasurableSet K)
    (hQmeas : MeasurableSet Q) (hKsubU : K ⊆ U) (hQsubK : Q ⊆ K)
    {V E H : ParabolicPoint → ℝ} (c₀ : ℝ)
    (hVint : Integrable V (volume.restrict Q))
    (hEint : Integrable E (volume.restrict K))
    (hEnonneg : 0 ≤ᵐ[volume.restrict K] E)
    (hCarleman : (∫ z in U, E z) ≤ c₀ * (∫ z in U, H z))
    (hEzero : ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      z ∈ U → z ∉ K → E z = 0)
    (hHzero : ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      z ∈ U → z ∉ K → H z = 0)
    (hdensity : ∀ z ∈ Q, Real.exp (-(3 / 2 : ℝ)) * V z ≤ E z) :
    Real.exp (-(3 / 2 : ℝ)) * (∫ z in Q, V z) ≤ ∫ z in K, E z ∧
      (∫ z in K, E z) ≤ c₀ * (∫ z in K, H z) := by
  have hEeq := setIntegral_eq_of_zero_off hUmeas hKmeas hKsubU hEzero
  have hHeq := setIntegral_eq_of_zero_off hUmeas hKmeas hKsubU hHzero
  have hCarlemanK : (∫ z in K, E z) ≤ c₀ * (∫ z in K, H z) := by
    calc
      _ = ∫ z in U, E z := hEeq.symm
      _ ≤ c₀ * (∫ z in U, H z) := hCarleman
      _ = c₀ * (∫ z in K, H z) := by rw [hHeq]
  exact ⟨carleman_energy_controls_average_box hQmeas hQsubK hVint
    hEint hEnonneg hdensity, hCarlemanK⟩

private theorem gaussian_average_error_regions_measurable
    (ρ σ ε : ℝ) :
    MeasurableSet {z : ParabolicPoint |
      13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
        vec3EuclideanNorm z.1 ≤ 3 * ρ / 4} ∧
    Continuous (fun z : ParabolicPoint =>
      ((buGaussianTimeShiftPoint σ).symm z).2) ∧
    MeasurableSet {z : ParabolicPoint |
      3 / 2 ≤ ((buGaussianTimeShiftPoint σ).symm z).2 ∧
        ((buGaussianTimeShiftPoint σ).symm z).2 ≤ 7 / 4} ∧
    MeasurableSet {z : ParabolicPoint |
      ε ≤ ((buGaussianTimeShiftPoint σ).symm z).2 ∧
        ((buGaussianTimeShiftPoint σ).symm z).2 ≤ 2 * ε} := by
  have hShellMeas : MeasurableSet {z : ParabolicPoint |
      13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
        vec3EuclideanNorm z.1 ≤ 3 * ρ / 4} := by
    exact (measurableSet_le continuous_const.measurable
      (continuous_vec3EuclideanNorm.measurable.comp measurable_fst)).inter
      (measurableSet_le (continuous_vec3EuclideanNorm.measurable.comp measurable_fst)
        continuous_const.measurable)
  have hrawTimeContinuous : Continuous (fun z : ParabolicPoint =>
      ((buGaussianTimeShiftPoint σ).symm z).2) := by
    exact (continuous_snd.comp parabolicHomeomorph.continuous).comp
      (buGaussianTimeShiftPoint σ).symm.continuous
  have hLateMeas : MeasurableSet {z : ParabolicPoint |
      3 / 2 ≤ ((buGaussianTimeShiftPoint σ).symm z).2 ∧
        ((buGaussianTimeShiftPoint σ).symm z).2 ≤ 7 / 4} := by
    simpa only [Set.preimage, Set.mem_Icc] using
      measurableSet_Icc.preimage hrawTimeContinuous.measurable
  have hInitialMeas : MeasurableSet {z : ParabolicPoint |
      ε ≤ ((buGaussianTimeShiftPoint σ).symm z).2 ∧
        ((buGaussianTimeShiftPoint σ).symm z).2 ≤ 2 * ε} := by
    simpa only [Set.preimage, Set.mem_Icc] using
      measurableSet_Icc.preimage hrawTimeContinuous.measurable
  exact ⟨hShellMeas, hrawTimeContinuous, hLateMeas, hInitialMeas⟩

private theorem gaussian_average_shell_gradient_tail_bound
    {ρ a : ℝ} (hρlarge : 4 < ρ) (ha : 1 < a)
    {K : Set ParabolicPoint}
    (v : ParabolicPoint → Vec3)
    (hKsub : K ⊆ spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2))
    (hKlate : ∀ z ∈ K, z.2 ≤ 23 / 12)
    (v : ParabolicPoint → Vec3) (Dv : ParabolicPoint → Fin 3 → Vec3)
    (hSourceInt : Integrable
      (fun z => ucGaussianWeight a z * spatialGradientSq v Dv z)
      (volume.restrict (spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2))))
    (bound : ℝ)
    (hShellGrad :
      (∫ z in spaceTimeSet
        {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
          vec3EuclideanNorm y ≤ 3 * ρ / 4} (Ioo (1 / 6) (23 / 12)),
        ucGaussianWeight a z * spatialGradientSq v Dv z) ≤ bound) :
    (∫ z in K, ({z | 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
      vec3EuclideanNorm z.1 ≤ 3 * ρ / 4}.indicator
        (fun z => ucGaussianWeight a z * spatialGradientSq v Dv z))) ≤ bound := by
  let Shell : Set ParabolicPoint := {z | 13 * ρ / 20 ≤
    vec3EuclideanNorm z.1 ∧ vec3EuclideanNorm z.1 ≤ 3 * ρ / 4}
  let S₁ : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
  let Sshell : Set ParabolicPoint :=
    spaceTimeSet {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
      vec3EuclideanNorm y ≤ 3 * ρ / 4} (Ioo (1 / 6) (23 / 12))
  have hSshellSub : Sshell ⊆ S₁ := by
    intro z hz
    change (13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
      vec3EuclideanNorm z.1 ≤ 3 * ρ / 4) ∧
      z.2 ∈ Ioo (1 / 6 : ℝ) (23 / 12) at hz
    have hρpos : 0 < ρ := by linarith only [hρlarge]
    have hnorm : vec3EuclideanNorm z.1 < ρ := by
      nlinarith only [hz.1.2, hρpos]
    change z.1 ∈ vec3Ball 0 ρ ∧ z.2 ∈ Ioo (1 / 6) 2
    constructor
    · simpa only [mem_vec3Ball, sub_zero] using hnorm
    · exact ⟨hz.2.1, lt_trans hz.2.2 (by norm_num)⟩
  have hShellMeas : MeasurableSet Shell := by
    dsimp [Shell]
    exact (measurableSet_le continuous_const.measurable
      (continuous_vec3EuclideanNorm.measurable.comp measurable_fst)).inter
      (measurableSet_le (continuous_vec3EuclideanNorm.measurable.comp measurable_fst)
        continuous_const.measurable)
  have hSshellMeas : MeasurableSet Sshell := by
    have hspatial : MeasurableSet
        {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
          vec3EuclideanNorm y ≤ 3 * ρ / 4} :=
      (measurableSet_le continuous_const.measurable
        continuous_vec3EuclideanNorm.measurable).inter
      (measurableSet_le continuous_vec3EuclideanNorm.measurable
        continuous_const.measurable)
    exact hspatial.prod measurableSet_Ioo
  have hShellSourceInt : Integrable
      (fun z => ucGaussianWeight a z * spatialGradientSq v Dv z)
      (volume.restrict Sshell) :=
    hSourceInt.mono_measure (Measure.restrict_mono hSshellSub le_rfl)
  have hShellSourceNonneg : 0 ≤ᵐ[volume.restrict Sshell]
      (fun z => ucGaussianWeight a z * spatialGradientSq v Dv z) := by
    filter_upwards [ae_restrict_mem hSshellMeas] with z hz
    have hzS := hSshellSub hz
    have hspos : 0 < z.2 := by
      have hs := hzS.2.1
      norm_num at hs ⊢
      linarith only [hs]
    have hG : 0 ≤ spatialGradientSq v Dv z := by
      dsimp [spatialGradientSq]
      positivity
    exact mul_nonneg (ucGaussianWeight_nonneg a hspos) hG
  have hShellAE : ∀ᵐ z : ParabolicPoint ∂volume,
      z ∈ K ∩ Shell → z ∈ Sshell := by
    filter_upwards [buGaussian_ae_time_ne (23 / 12 : ℝ)] with z hne hz
    have hzS := hKsub hz.1
    have htop : z.2 ≤ 23 / 12 := hKlate z hz.1
    have htop' : z.2 < 23 / 12 := lt_of_le_of_ne htop hne
    exact ⟨hz.2, ⟨hzS.2.1, htop'⟩⟩
  have hShellIntegral :
      (∫ z in K, Shell.indicator
        (fun z => ucGaussianWeight a z * spatialGradientSq v Dv z)) ≤
      ∫ z in Sshell, ucGaussianWeight a z * spatialGradientSq v Dv z := by
    have hEq : (∫ z in K, Shell.indicator
        (fun z => ucGaussianWeight a z * spatialGradientSq v Dv z)) =
        ∫ z in K ∩ Shell, ucGaussianWeight a z * spatialGradientSq v Dv z := by
      rw [setIntegral_indicator hShellMeas]
    rw [hEq]
    exact setIntegral_mono_set hShellSourceInt hShellSourceNonneg hShellAE
  have hShellBound :
      (∫ z in Sshell, ucGaussianWeight a z * spatialGradientSq v Dv z) ≤ bound := by
    simpa [Sshell] using hShellGrad
  simpa [Shell] using hShellIntegral.trans hShellBound

private theorem gaussian_average_radial_shell_mass_data
    {ρ a : ℝ} (hρlarge : 4 < ρ) (ha : 1 < a)
    {K : Set ParabolicPoint}
    (hKsub : K ⊆ spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2))
    (hS₁meas : MeasurableSet
      (spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2)))
    (hMassIntS₁ : Integrable (fun z => ucGaussianWeight a z *
      vec3EuclideanNorm (v z) ^ 2)
      (volume.restrict (spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2))) :
    Integrable (buGaussianRadialWeightedMass ρ a v)
        (volume.restrict (spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2))) ∧
    0 ≤ᵐ[volume.restrict (spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2))]
      buGaussianRadialWeightedMass ρ a v ∧
    Integrable (buGaussianRadialWeightedMass ρ a v) (volume.restrict K) ∧
    ∀ z ∈ K, ({z | 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
      vec3EuclideanNorm z.1 ≤ 3 * ρ / 4}.indicator
        (fun z => ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2)) z ≤
      buGaussianRadialWeightedMass ρ a v z := by
  let S₁ : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
  let Shell : Set ParabolicPoint := {z | 13 * ρ / 20 ≤
    vec3EuclideanNorm z.1 ∧ vec3EuclideanNorm z.1 ≤ 3 * ρ / 4}
  have hRadMeas : MeasurableSet {z : ParabolicPoint |
      ρ / 2 ≤ vec3EuclideanNorm z.1} :=
    measurableSet_le continuous_const.measurable
      (continuous_vec3EuclideanNorm.measurable.comp measurable_fst)
  have hRadialInt : Integrable (buGaussianRadialWeightedMass ρ a v)
      (volume.restrict S₁) := by
    have h := hMassIntS₁.indicator hRadMeas
    convert h using 1
    ext z
    by_cases hz : ρ / 2 ≤ vec3EuclideanNorm z.1 <;>
      simp [Set.indicator, buGaussianRadialWeightedMass, hz]
  have hRadialNonneg : 0 ≤ᵐ[volume.restrict S₁]
      buGaussianRadialWeightedMass ρ a v := by
    filter_upwards [ae_restrict_mem hS₁meas] with z hzS
    by_cases hr : ρ / 2 ≤ vec3EuclideanNorm z.1
    · have hspos : 0 < z.2 := by
        have hs := hzS.2.1
        norm_num at hs ⊢
        linarith only [hs]
      simp [buGaussianRadialWeightedMass, hr]
      exact mul_nonneg (ucGaussianWeight_nonneg a hspos) (sq_nonneg _)
    · simp [buGaussianRadialWeightedMass, hr]
  have hRadialIntK : Integrable (buGaussianRadialWeightedMass ρ a v)
      (volume.restrict K) :=
    hRadialInt.mono_measure (Measure.restrict_mono hKsub le_rfl)
  have hShellMassPoint : ∀ z ∈ K,
      Shell.indicator (fun z => ucGaussianWeight a z *
        vec3EuclideanNorm (v z) ^ 2) z ≤
      buGaussianRadialWeightedMass ρ a v z := by
    intro z hzK
    by_cases hzShell : z ∈ Shell
    · have hr : ρ / 2 ≤ vec3EuclideanNorm z.1 := by
        have hlow := hzShell.1
        have hρpos : 0 < ρ := by linarith only [hρlarge]
        nlinarith only [hlow, hρpos]
      simp [Shell, buGaussianRadialWeightedMass, hzShell, hr]
    · have hzS := hKsub hzK
      have hspos : 0 < z.2 := by
        have hs := hzS.2.1
        norm_num at hs ⊢
        linarith only [hs]
      by_cases hr : ρ / 2 ≤ vec3EuclideanNorm z.1
      · simp [Shell, buGaussianRadialWeightedMass, hzShell, hr]
        exact mul_nonneg (ucGaussianWeight_nonneg a hspos) (sq_nonneg _)
      · simp [Shell, buGaussianRadialWeightedMass, hzShell, hr]
  exact ⟨by simpa [S₁] using hRadialInt,
    by simpa [S₁] using hRadialNonneg,
    hRadialIntK, by simpa [Shell] using hShellMassPoint⟩

private theorem gaussian_initial_trace_strip_error
    {ρ a ε δ : ℝ} (ha : 1 < a) (hε : 0 < ε)
    (hεle : ε ≤ 1 / 12) (v : ParabolicPoint → Vec3)
    {K : Set ParabolicPoint} (hKmeas : MeasurableSet K)
    (hKsub : K ⊆ spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2))
    (hBmeas : MeasurableSet (vec3Ball 0 ρ))
    (hSourceMassIntS₁ : Integrable (fun z => vec3EuclideanNorm (v z) ^ 2)
      (volume.restrict (spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2)))
    (hWeightedMassIntK : Integrable (fun z => ucGaussianWeight a z *
      vec3EuclideanNorm (v z) ^ 2) (volume.restrict K))
    (htrace : (∫ z in spaceTimeSet (vec3Ball 0 ρ)
      (Ioc (1 / 6 + ε) (1 / 6 + 2 * ε)), vec3EuclideanNorm (v z) ^ 2) /
        ε ^ 2 < δ) :
    let Wmax : ℝ := ((1 / 6 : ℝ) * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a)
    let Initial : Set ParabolicPoint := {z |
      ε ≤ ((buGaussianTimeShiftPoint (1 / 6 : ℝ)).symm z).2 ∧
        ((buGaussianTimeShiftPoint (1 / 6 : ℝ)).symm z).2 ≤ 2 * ε}
    let Vsrc : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (v z) ^ 2
    let initialMass : ParabolicPoint → ℝ :=
      Initial.indicator (fun z => ucGaussianWeight a z * Vsrc z)
    Integrable initialMass (volume.restrict K) ∧
      (∫ z in K, initialMass z) ≤
        Wmax * (∫ z in spaceTimeSet (vec3Ball 0 ρ)
          (Icc (1 / 6 + ε) (1 / 6 + 2 * ε)), Vsrc z) ∧
      (∫ z in spaceTimeSet (vec3Ball 0 ρ)
        (Icc (1 / 6 + ε) (1 / 6 + 2 * ε)), Vsrc z) / ε ^ 2 < δ := by
  let Wmax : ℝ := ((1 / 6 : ℝ) * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a)
  let B : Set Vec3 := vec3Ball 0 ρ
  let S₁ : Set ParabolicPoint := spaceTimeSet B (Ioo (1 / 6) 2)
  let Sinit : Set ParabolicPoint :=
    spaceTimeSet B (Icc (1 / 6 + ε) (1 / 6 + 2 * ε))
  let SinitOpen : Set ParabolicPoint :=
    spaceTimeSet B (Ioc (1 / 6 + ε) (1 / 6 + 2 * ε))
  let Vsrc : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (v z) ^ 2
  let rawTime : ParabolicPoint → ℝ := fun z =>
    ((buGaussianTimeShiftPoint (1 / 6 : ℝ)).symm z).2
  let Initial : Set ParabolicPoint := {z | ε ≤ rawTime z ∧ rawTime z ≤ 2 * ε}
  let initialMass : ParabolicPoint → ℝ :=
    Initial.indicator (fun z => ucGaussianWeight a z * Vsrc z)
  have hWmax : 0 < Wmax := by dsimp [Wmax]; positivity
  have hSinitMeas : MeasurableSet Sinit := hBmeas.prod measurableSet_Icc
  have hSinitSub : Sinit ⊆ S₁ := by
    intro z hz
    change z.1 ∈ B ∧ z.2 ∈ Icc (1 / 6 + ε) (1 / 6 + 2 * ε) at hz
    change z.1 ∈ B ∧ z.2 ∈ Ioo (1 / 6) 2
    refine ⟨hz.1, ?_⟩
    constructor
    · linarith only [hz.2.1, hε]
    · linarith only [hz.2.2, hεle]
  have hSinitInt : Integrable Vsrc (volume.restrict Sinit) :=
    hSourceMassIntS₁.mono_measure (Measure.restrict_mono hSinitSub le_rfl)
  have hInitialMeas : MeasurableSet Initial := by
    have hrawTimeContinuous : Continuous rawTime := by
      dsimp [rawTime]
      exact (continuous_snd.comp parabolicHomeomorph.continuous).comp
        (buGaussianTimeShiftPoint (1 / 6 : ℝ)).symm.continuous
    dsimp [Initial, rawTime]
    simpa only [Set.preimage, Set.mem_Icc] using
      measurableSet_Icc.preimage hrawTimeContinuous.measurable
  have hInitialMassInt : Integrable initialMass (volume.restrict K) := by
    simpa [initialMass] using hWeightedMassIntK.indicator hInitialMeas
  have hInitialPoint (z : ParabolicPoint) (hzK : z ∈ K) :
      initialMass z ≤ Wmax * Sinit.indicator Vsrc z := by
    by_cases hzInit : z ∈ Initial
    · have hzS := hKsub hzK
      have hzStrip : z ∈ Sinit := by
        have hraw := hzInit
        dsimp [Initial, rawTime] at hraw
        rw [buGaussian_timeShift_point_symm_apply] at hraw
        change z.1 ∈ B ∧ z.2 ∈ Icc (1 / 6 + ε) (1 / 6 + 2 * ε)
        refine ⟨hzS.1, ?_⟩
        change 1 / 6 + ε ≤ z.2 ∧ z.2 ≤ 1 / 6 + 2 * ε
        constructor <;> linarith only [hraw.1, hraw.2]
      have hspos : 0 < z.2 := by
        have hs := hzS.2.1
        norm_num at hs ⊢
        linarith only [hs]
      have hweight : ucGaussianWeight a z ≤ Wmax := by
        exact ucGaussianWeight_le_after (by norm_num)
          (by linarith only [ha]) hzS.2.1.le hzS.2.2.le
      have hmul := mul_le_mul_of_nonneg_right hweight
        (sq_nonneg (vec3EuclideanNorm (v z)))
      simpa [initialMass, hzInit, hzStrip, Vsrc, Set.indicator, Wmax] using hmul
    · have hnonneg : 0 ≤ Sinit.indicator Vsrc z := by
        by_cases hz : z ∈ Sinit <;> simp [Set.indicator, hz, Vsrc, sq_nonneg]
      have hnonneg' := mul_nonneg hWmax.le hnonneg
      simpa [initialMass, hzInit] using hnonneg'
  have hInitialIntegral : (∫ z in K, initialMass z) ≤
      Wmax * (∫ z in Sinit, Vsrc z) :=
    bu_short_early_integral_le_trace hKmeas hSinitMeas
      hSinitInt hInitialMassInt (fun z => sq_nonneg _)
      Wmax hWmax.le hInitialPoint
  have hInitAE : Sinit =ᵐ[volume] SinitOpen := by
    filter_upwards [buGaussian_ae_time_ne (1 / 6 + ε)] with z hne
    apply propext
    change (z.1 ∈ B ∧ z.2 ∈ Icc (1 / 6 + ε) (1 / 6 + 2 * ε)) ↔
      (z.1 ∈ B ∧ z.2 ∈ Ioc (1 / 6 + ε) (1 / 6 + 2 * ε))
    constructor
    · rintro ⟨hzB, hzT⟩
      exact ⟨hzB, ⟨lt_of_le_of_ne hzT.1 (Ne.symm hne), hzT.2⟩⟩
    · rintro ⟨hzB, hzT⟩
      exact ⟨hzB, ⟨hzT.1.le, hzT.2⟩⟩
  have hInitialTraceIntegral : (∫ z in Sinit, Vsrc z) / ε ^ 2 < δ := by
    have hEq : (∫ z in Sinit, Vsrc z) =
        ∫ z in SinitOpen, Vsrc z := setIntegral_congr_set hInitAE
    rw [hEq]
    exact htrace
  exact ⟨hInitialMassInt, hInitialIntegral, hInitialTraceIntegral⟩

private theorem gaussian_average_absorb_car_energy
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {heat major : α → ℝ} (c₀ C_G c₁ scale t γ Icar Eerr : ℝ)
    (hc₀ : 0 ≤ c₀) (hCG : C_G = 72 * c₀)
    (hCarleman : Icar ≤ c₀ * (∫ z, heat z))
    (hMajorIntegral : (∫ z, heat z) ≤ ∫ z, major z)
    (hMajorEq : (∫ z, major z) =
      72 * (c₁ * scale) ^ 2 * Icar + Eerr)
    (hscaleSq : scale ^ 2 = 3 * t) (htγ : t < γ)
    (hγabsorb : 3 * C_G * c₁ ^ 2 * γ ≤ 1 / 2)
    (hIcarNonneg : 0 ≤ Icar) : Icar ≤ 2 * c₀ * Eerr := by
  have hCarUpper : Icar ≤
      c₀ * (72 * (c₁ * scale) ^ 2 * Icar + Eerr) := by
    have hbound := hCarleman.trans
      (mul_le_mul_of_nonneg_left hMajorIntegral hc₀)
    simpa only [hMajorEq] using hbound
  have hAbsorbCoeff : c₀ * 72 * (c₁ * scale) ^ 2 ≤ 1 / 2 := by
    calc
      c₀ * 72 * (c₁ * scale) ^ 2 = (3 * C_G * c₁ ^ 2) * t := by
        rw [mul_pow, hscaleSq]
        rw [hCG]
        ring
      _ ≤ (3 * C_G * c₁ ^ 2) * γ :=
        mul_le_mul_of_nonneg_left htγ.le (by positivity)
      _ ≤ 1 / 2 := by simpa only [mul_assoc] using hγabsorb
  have hhalf := mul_le_mul_of_nonneg_right hAbsorbCoeff hIcarNonneg
  nlinarith only [hCarUpper, hhalf]

private theorem gaussian_average_cutoff_volume_bound
    {ρ : ℝ} {K : Set ParabolicPoint} (hρlarge : 4 < ρ)
    (hKsub : K ⊆ spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2))
    (hBfinite : volume (vec3Ball 0 ρ) < ⊤) :
    volume K < ⊤ ∧ (volume K).toReal ≤ 12 * ρ ^ 3 := by
  let S₁ : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
  have hS₁finite : volume S₁ < ⊤ := by
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
      (vec3Ball 0 ρ ×ˢ Ioo (1 / 6) 2) < ⊤
    rw [Measure.prod_prod]
    have hI : volume (Ioo (1 / 6 : ℝ) 2) < ⊤ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    exact ENNReal.mul_lt_top hBfinite hI
  have hKfinite : volume K < ⊤ :=
    (measure_mono hKsub).trans_lt hS₁finite
  have hKvolume : (volume K).toReal ≤ 12 * ρ ^ 3 := by
    calc
      (volume K).toReal ≤ (volume S₁).toReal :=
        ENNReal.toReal_mono hS₁finite.ne (measure_mono hKsub)
      _ ≤ 12 * ρ ^ 3 := by
        simpa only [S₁] using
          buGaussian_local_cylinder_volume_bound
            (by linarith only [hρlarge] : 0 < ρ)
  exact ⟨hKfinite, hKvolume⟩

private theorem gaussian_average_late_initial_shell_tail_stage
    {K S₁ Sinit Late : Set ParabolicPoint}
    {lateMass initialMass shellMass radialMass Vsrc : ParabolicPoint → ℝ}
    (A barA β ρ a scale Tbound ε δ Wmax : ℝ) (x : Vec3)
    (v : ParabolicPoint → Vec3)
    (hKmeas : MeasurableSet K) (hKsubS₁ : K ⊆ S₁)
    (hBfinite : volume (vec3Ball 0 ρ) < ⊤) (hρlarge : 4 < ρ)
    (hTboundEq : Tbound = Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
      Real.exp (-2 * β * ρ ^ 2)) (hTboundNonneg : 0 ≤ Tbound)
    (hA : 0 ≤ A) (hAmax : A ≤ 1 / (10 : ℝ) ^ 12)
    (hAbar : A ≤ barA) (hscaleSqLe : scale ^ 2 ≤ 1 / 4)
    (haeq : a = β * ρ ^ 2 / buGaussianH)
    (hLateTime : ∀ z ∈ K, z ∈ Late → 3 / 2 ≤ z.2)
    (hgrowth : ∀ z ∈ S₁,
      vec3EuclideanNorm (v z) ≤
        Real.exp (2 * A * vec3EuclideanNorm x ^ 2 +
          2 * A * scale ^ 2 * vec3EuclideanNorm z.1 ^ 2))
    (hLateMassEq : ∀ z, lateMass z =
      if z ∈ Late then ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2
      else 0)
    (hLateMassInt : Integrable lateMass (volume.restrict K))
    (hInitialMassInt : Integrable initialMass (volume.restrict K))
    (hInitialIntegral : (∫ z in K, initialMass z) ≤
      Wmax * (∫ z in Sinit, Vsrc z))
    (hInitialTrace : (∫ z in Sinit, Vsrc z) / ε ^ 2 < δ)
    (hε : 0 < ε) (hWmax : 0 < Wmax)
    (hShellMassInt : Integrable shellMass (volume.restrict K))
    (hRadialIntK : Integrable radialMass (volume.restrict K))
    (hShellPoint : ∀ z ∈ K, shellMass z ≤ radialMass z)
    (hRadialInt : Integrable radialMass (volume.restrict S₁))
    (hRadialNonneg : 0 ≤ᵐ[volume.restrict S₁] radialMass)
    (hRadialTail : (∫ z in S₁, radialMass z) ≤ 24 * ρ ^ 3 * Tbound) :
    (∫ z in K, lateMass z) ≤ 12 * ρ ^ 3 * Tbound ∧
    (256 / ε ^ 2) * (∫ z in K, initialMass z) ≤ Tbound ∧
    (∫ z in K, shellMass z) ≤ 24 * ρ ^ 3 * Tbound := by
  have hKvolumeData := gaussian_average_cutoff_volume_bound
    hρlarge hKsubS₁ hBfinite
  rcases hKvolumeData with ⟨hKfinite, hKvolume⟩
  have hLatePoint (z : ParabolicPoint) (hzK : z ∈ K) :
      lateMass z ≤ Tbound := by
    by_cases hzLate : z ∈ Late
    · have hzS := hKsubS₁ hzK
      have hslow := hLateTime z hzK hzLate
      have hpoint := gaussian_late_weighted_mass_point_bound
        A barA β ρ a scale Tbound x v hA hAmax hAbar hscaleSqLe haeq
        hTboundEq hTboundNonneg z hslow hzS.2.2.le (hgrowth z hzS)
      simpa [hLateMassEq, hzLate] using hpoint
    · simpa [hLateMassEq, hzLate] using hTboundNonneg
  have hspace : 1 ≤ Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hInitialBaseBound : Real.exp (-2 * β * ρ ^ 2) ≤ Tbound := by
    rw [hTboundEq]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hspace (Real.exp_nonneg _)
  exact gaussian_average_tail_error_integrals
    hKmeas (hKvolumeData.1) hKvolume hTboundNonneg hKsubS₁
    hLateMassInt hLatePoint ε δ Wmax (Real.exp (-2 * β * ρ ^ 2)) hε hWmax
    hInitialMassInt hInitialIntegral hInitialTrace
    (by simpa only [δ] using buGaussian_initial_error_cancel ε Wmax
      (Real.exp (-2 * β * ρ ^ 2)) (ne_of_gt hε) hWmax.ne')
    hInitialBaseBound hShellMassInt hRadialIntK hShellPoint
    hRadialInt hRadialNonneg hRadialTail

private theorem gaussian_average_core_error_stage
    (c₀ Cg Cs c₁ scale ρ a r R₀ k₀ k₁ Cacc Icar Eerr shell0 shell1
      SM SG LM IM R T : ℝ)
    (hc₀ : 0 ≤ c₀) (hCg : 0 ≤ Cg) (hCs : 0 ≤ Cs)
    (hc₁ : 0 < c₁) (hscale : 0 ≤ scale) (hscaleSq : scale ^ 2 ≤ 1 / 4)
    (hρlarge : 4 < ρ) (ha : 0 < a) (hr : r = 1 / (16 * Real.sqrt a))
    (hρr : ρ * r = R₀)
    (hk₀ : 0 ≤ k₀) (hk₁ : 0 ≤ k₁) (hCacc : 0 ≤ Cacc)
    (hT : 0 ≤ T) (hρ : 0 ≤ ρ) (haNonneg : 0 ≤ a)
    (hCarAbsorbed : Icar ≤ 2 * c₀ * Eerr)
    (hEerr : Eerr = 8 * shell0 ^ 2 * SM + 8 * shell1 ^ 2 * SG +
      4096 * LM + IM)
    (hSMnonneg : 0 ≤ SM) (hSGnonneg : 0 ≤ SG)
    (hSM : SM ≤ 24 * ρ ^ 3 * T)
    (hSG : SG ≤
      (Real.exp (2 * (56 * a * (2 * r) ^ 2 + 12 * ρ * (2 * r) +
        36 * ρ ^ 2 * (2 * r) ^ 2)) *
        (256 * (1 + (c₁ * scale) ^ 2 + 1 / ((2 * r) / 2) ^ 2))) *
        (8 * Besicovitch.multiplicity BUGaussianSpace ^ 2 : ℝ) * R)
    (hRadialNonneg : 0 ≤ R) (hRadialTail : R ≤ 24 * ρ ^ 3 * T)
    (hLM : LM ≤ 12 * ρ ^ 3 * T) (hIM : IM ≤ T) :
    Icar ≤ 2 * c₀ * (192 * (k₀ ^ 2 + k₁ ^ 2 * Cacc) + 49153) *
      ((1 + a) * (1 + ρ) ^ 3 * T) := by
  have hFactorBound := buGaussian_shell_coefficient_bound
    (a := a) (r := r) (ρ := ρ) (scale := scale) (c₁ := c₁)
    (R₀ := R₀) ha hr hρr hscaleSq
  have hAmp := buGaussian_shell_amplitude_bound
    hρlarge hscale hscaleSq hc₁.le hCg hCs
  exact buGaussian_error_assembly_bound
    hc₀ hk₀ hk₁ hCacc haNonneg hρ hT hCarAbsorbed hEerr
    hAmp.1 hAmp.2.1 hAmp.2.2.1 hAmp.2.2.2
    hSMnonneg hSGnonneg hSM hSG hFactorBound hRadialNonneg
    hRadialTail hLM hIM

private structure GaussianAverageCutoffSupport
    (ρ ε : ℝ) (hρ : 0 < ρ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtu : ParabolicPoint → Vec3) where
  κ : Vec3 × ℝ → ℝ
  K : Set ParabolicPoint
  hKdef : K = buCutSupportSet κ
  hcutScalarComp : (fun z : ParabolicPoint => κ (parabolicHomeomorph z)) =
    buGaussianShiftedCutoff ρ hρ ε
  hKeq : K = tsupport (buGaussianShiftedCutoff ρ hρ ε)
  hKsubS₁ : K ⊆ spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
  hKsubU₀ : K ⊆ spaceTimeSet univ (Ioo 0 2)
  hKmeas : MeasurableSet K
  hQsubK : spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2) 1) ⊆ K
  hQmeas : MeasurableSet
    (spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2) 1))
  hweakCut : HasSpaceTimeWeakDerivs univ (Ioo 0 2)
    (buGaussianShiftedCutoffField ρ hρ ε u)
    (buGaussianShiftedCutoffDw ρ hρ ε u Du)
    (buGaussianShiftedCutoffD2w ρ hρ ε u Du D2u)
    (buGaussianShiftedCutoffDtw ρ hρ ε u Dtu)
  hcompactCut : HasCompactSupport (buGaussianShiftedCutoffField ρ hρ ε u)
  htsCut : tsupport (buGaussianShiftedCutoffField ρ hρ ε u) ⊆
    spaceTimeSet univ (Ioo 0 2)
  hmemCut : MemLp (buGaussianShiftedCutoffField ρ hρ ε u) 2 volume
  hmemDwCut : MemLp (buGaussianShiftedCutoffDw ρ hρ ε u Du) 2 volume
  hmemD2Cut : MemLp (buGaussianShiftedCutoffD2w ρ hρ ε u Du D2u) 2 volume
  hmemDtCut : MemLp (buGaussianShiftedCutoffDtw ρ hρ ε u Dtu) 2 volume
  hcutZero : ∀ z, z ∉ K →
    buGaussianShiftedCutoffField ρ hρ ε u z = 0 ∧
    buGaussianShiftedCutoffDw ρ hρ ε u Du z = 0 ∧
    buGaussianShiftedCutoffD2w ρ hρ ε u Du D2u z = 0 ∧
    buGaussianShiftedCutoffDtw ρ hρ ε u Dtu z = 0
  hKlate : ∀ z ∈ K, z.2 ≤ 23 / 12

private theorem gaussian_average_cutoff_support_stage
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hεle : ε ≤ 1 / 12)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtu : ParabolicPoint → Vec3)
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ)
      (Ioo 0 (2 - 1 / 6)) u Du D2u Dtu)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2),
      ‖buGaussianShiftedField (1 / 6) u z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDw (1 / 6) Du z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedD2w (1 / 6) D2u z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDtw (1 / 6) Dtu z‖ₑ ^ (2 : ℝ)) < ⊤) :
    GaussianAverageCutoffSupport ρ ε hρ u Du D2u Dtu := by
  let κ : Vec3 × ℝ → ℝ := fun q =>
    ucCutoffScalar (ucSpatialCutoff ρ hρ)
      (fun s => ucFinalTimeCutoff (s - 1 / 6))
      (fun s => ucInitialTimeCutoff ε (s - 1 / 6)) q
  let K : Set ParabolicPoint := buCutSupportSet κ
  have hcutAdmissible := buGaussian_shifted_cutoff_admissible hρ hε hweak hL2
  rcases hcutAdmissible with
    ⟨hweakCut, hcompactCut, htsCut, hmemCut, hmemDwCut, hmemD2Cut, hmemDtCut⟩
  have hzeroLate := buGaussian_shifted_cutoff_data_zero_late hρ u Du D2u Dtu
  rcases hzeroLate with ⟨hcutZero, hKlate⟩
  have hcutScalarComp :
      (fun z : ParabolicPoint => κ (parabolicHomeomorph z)) =
        buGaussianShiftedCutoff ρ hρ ε := by
    funext z
    change ucCutoffScalar (ucSpatialCutoff ρ hρ)
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6)) (parabolicHomeomorph z) =
      ucGaussianCutoff ρ hρ ε ((buGaussianTimeShiftPoint (1 / 6)).symm z)
    rw [parabolicHomeomorph_apply, buGaussian_timeShift_point_symm_apply]
    rfl
  have hKeq : K = tsupport (buGaussianShiftedCutoff ρ hρ ε) := by
    dsimp [K, buCutSupportSet]
    rw [← hcutScalarComp]
    exact (tsupport_comp_eq_preimage κ parabolicHomeomorph).symm
  have hKsubS₁ : K ⊆ spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2) := by
    rw [hKeq]
    exact buGaussian_shiftedCutoff_tsupport_subset hρ hε
  have hKsubU₀ : K ⊆ spaceTimeSet univ (Ioo 0 2) := by
    intro z hz
    have hz' := hKsubS₁ hz
    exact ⟨Set.mem_univ _, ⟨by linarith only [hz'.2.1], hz'.2.2⟩⟩
  have hKmeas : MeasurableSet K := by
    dsimp [K, buCutSupportSet]
    have hclosed : IsClosed (tsupport κ) := isClosed_tsupport κ
    exact (hclosed.preimage parabolicHomeomorph.continuous).measurableSet
  have hQsubK : spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2) 1) ⊆ K := by
    rw [hKeq]
    intro z hz
    apply subset_tsupport
    have hscalar := (buGaussian_cutoff_field_eq_on_average_box
      (ρ := ρ) (ε := ε) hρ hε hεle u z hz).1
    have hcomp := congrFun hcutScalarComp z
    have hval : buGaussianShiftedCutoff ρ hρ ε z = 1 := by
      change ucCutoffScalar (ucSpatialCutoff ρ hρ)
          (fun s => ucFinalTimeCutoff (s - 1 / 6))
          (fun s => ucInitialTimeCutoff ε (s - 1 / 6)) z = 1 at hscalar
      have hκ : κ (parabolicHomeomorph z) = 1 := by
        change ucCutoffScalar (ucSpatialCutoff ρ hρ)
            (fun s => ucFinalTimeCutoff (s - 1 / 6))
            (fun s => ucInitialTimeCutoff ε (s - 1 / 6))
            (parabolicHomeomorph z) = 1
        rw [parabolicHomeomorph_apply]
        change ucCutoffScalar (ucSpatialCutoff ρ hρ)
            (fun s => ucFinalTimeCutoff (s - 1 / 6))
            (fun s => ucInitialTimeCutoff ε (s - 1 / 6))
            (z.1, z.2) = 1 at hscalar
        exact hscalar
      exact hcomp.symm.trans hκ
    change buGaussianShiftedCutoff ρ hρ ε z ≠ 0
    rw [hval]
    norm_num
  have hQmeas : MeasurableSet
      (spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2) 1)) :=
    (isOpen_spaceTimeSet _ _ Metric.isOpen_ball isOpen_Ioo).measurableSet
  exact ⟨κ, K, rfl, hcutScalarComp, hKeq, hKsubS₁, hKsubU₀,
    hKmeas, hQsubK, hQmeas, hweakCut, hcompactCut, htsCut,
    hmemCut, hmemDwCut, hmemD2Cut, hmemDtCut, hcutZero, hKlate⟩

private theorem gaussian_average_choose_cutoff_stage
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtu : ParabolicPoint → Vec3)
    (htraceShift : Tendsto (fun ε : ℝ =>
      (∫ z in spaceTimeSet (vec3Ball 0 ρ) (Ioc (1 / 6 + ε) (1 / 6 + 2 * ε)),
        vec3EuclideanNorm (u ((buGaussianTimeShiftPoint (1 / 6)).symm z)) ^ 2) /
          ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ)
      (Ioo 0 (2 - 1 / 6)) u Du D2u Dtu)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2),
      ‖buGaussianShiftedField (1 / 6) u z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDw (1 / 6) Du z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedD2w (1 / 6) D2u z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDtw (1 / 6) Dtu z‖ₑ ^ (2 : ℝ)) < ⊤) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 12 ∧
      (∫ z in spaceTimeSet (vec3Ball 0 ρ)
          (Ioc (1 / 6 + ε) (1 / 6 + 2 * ε)),
        vec3EuclideanNorm (u ((buGaussianTimeShiftPoint (1 / 6)).symm z)) ^ 2) /
          ε ^ 2 < δ ∧
      GaussianAverageCutoffSupport ρ ε hρ u Du D2u Dtu := by
  have htraceSmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      (∫ z in spaceTimeSet (vec3Ball 0 ρ)
          (Ioc (1 / 6 + ε) (1 / 6 + 2 * ε)),
        vec3EuclideanNorm (u ((buGaussianTimeShiftPoint (1 / 6)).symm z)) ^ 2) /
          ε ^ 2 < δ := by
    filter_upwards [htraceShift.eventually (Metric.ball_mem_nhds 0 hδ)] with ε hε
    have hmassNonneg : 0 ≤
        ∫ z in spaceTimeSet (vec3Ball 0 ρ) (Ioc (1 / 6 + ε) (1 / 6 + 2 * ε)),
          vec3EuclideanNorm (u ((buGaussianTimeShiftPoint (1 / 6)).symm z)) ^ 2 :=
      setIntegral_nonneg_of_ae
        (Filter.Eventually.of_forall (fun z => sq_nonneg _))
    have hratioNonneg : 0 ≤
        (∫ z in spaceTimeSet (vec3Ball 0 ρ)
          (Ioc (1 / 6 + ε) (1 / 6 + 2 * ε)),
          vec3EuclideanNorm (u ((buGaussianTimeShiftPoint (1 / 6)).symm z)) ^ 2) /
            ε ^ 2 := div_nonneg hmassNonneg (sq_nonneg ε)
    have hdist : dist
        ((∫ z in spaceTimeSet (vec3Ball 0 ρ)
          (Ioc (1 / 6 + ε) (1 / 6 + 2 * ε)),
          vec3EuclideanNorm (u ((buGaussianTimeShiftPoint (1 / 6)).symm z)) ^ 2) /
            ε ^ 2) 0 < δ := by simpa only [Metric.mem_ball] using hε
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hratioNonneg] using hdist
  have hεsmallEvent : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 / 12 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 12))
  have hεposEvent : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  rcases (htraceSmall.and hεsmallEvent |>.and hεposEvent).exists with
    ⟨ε, hεdata⟩
  rcases hεdata with ⟨⟨htraceε, hεsmall⟩, hε⟩
  have hεle : ε ≤ 1 / 12 := hεsmall.le
  exact ⟨ε, hε, hεle, htraceε,
    gaussian_average_cutoff_support_stage hρ hε hεle u Du D2u Dtu hweak hL2⟩

private theorem gaussian_average_initial_cutoff_setup
    {ρ δ scale : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (c₁ : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtu : ParabolicPoint → Vec3)
    (hcontRaw : ContinuousOn u (vec3Ball 0 ρ ×ˢ Ioo 0 2))
    (hzeroRaw : ∀ y : Vec3, y ∈ vec3Ball 0 ρ → u (y, 0) = 0)
    (hweakRaw : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      u Du D2u Dtu)
    (hL2Raw : (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo 0 2),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) +
        ‖D2u z‖ₑ ^ (2 : ℝ) + ‖Dtu z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineqRaw : ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
      vec3EuclideanNorm (ucWeakHeatVector D2u Dtu z) ≤
        c₁ * scale * (vec3EuclideanNorm (u z) +
          Real.sqrt (spatialGradientSq u Du z)))
    (hweakShift : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
      (buGaussianShiftedField (1 / 6) u)
      (buGaussianShiftedDw (1 / 6) Du)
      (buGaussianShiftedD2w (1 / 6) D2u)
      (buGaussianShiftedDtw (1 / 6) Dtu))
    (hL2Shift : (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2),
      ‖buGaussianShiftedField (1 / 6) u z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDw (1 / 6) Du z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedD2w (1 / 6) D2u z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDtw (1 / 6) Dtu z‖ₑ ^ (2 : ℝ)) < ⊤) :
    HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 (2 - 1 / 6)) u Du D2u Dtu ∧
    volume (vec3Ball 0 ρ) < ⊤ ∧
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 12 ∧
      (∫ z in spaceTimeSet (vec3Ball 0 ρ)
          (Ioc (1 / 6 + ε) (1 / 6 + 2 * ε)),
        vec3EuclideanNorm (u ((buGaussianTimeShiftPoint (1 / 6)).symm z)) ^ 2) /
          ε ^ 2 < δ ∧
      GaussianAverageCutoffSupport ρ ε hρ u Du D2u Dtu := by
  let B : Set Vec3 := vec3Ball 0 ρ
  let I₀ : Set ℝ := Ioo 0 (2 - 1 / 6)
  have hI₀sub : I₀ ⊆ Ioo 0 2 := by
    intro s hs
    exact ⟨hs.1, lt_of_lt_of_le hs.2 (by norm_num [I₀])⟩
  have hcontRaw' : ContinuousOn u (B ×ˢ Ioo 0 2) := hcontRaw
  have hrestricted := uc_restrict_data (c₁ * scale) B B I₀ (Ioo 0 2)
    u Du D2u Dtu (isOpen_vec3Ball 0 ρ) isOpen_Ioo subset_rfl hI₀sub
    hcontRaw' hweakRaw hL2Raw hineqRaw
  have hweak₀ : HasSpaceTimeWeakDerivs B I₀ u Du D2u Dtu := hrestricted.2.1
  have hL2₀ : (∫⁻ z in S₀,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) +
        ‖D2u z‖ₑ ^ (2 : ℝ) + ‖Dtu z‖ₑ ^ (2 : ℝ)) < ⊤ := hrestricted.2.2.1
  have hBopen : IsOpen B := by dsimp [B]; exact isOpen_vec3Ball 0 ρ
  have hBfinite : volume B < ⊤ := by
    dsimp [B]
    exact CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top
  have hcontTrace : ContinuousOn u (spaceTimeSet B (Ico 0 (2 - 1 / 6))) := by
    apply hcontRaw.mono
    intro z hz
    change z.1 ∈ B ∧ z.2 ∈ Ico 0 (2 - 1 / 6) at hz
    exact ⟨hz.1, ⟨hz.2.1, lt_of_lt_of_le hz.2.2 (by norm_num)⟩⟩
  have htraceRaw := buGaussian_initial_trace_strip_tendsto_zero
    hBopen hBfinite (by norm_num : (0 : ℝ) < 2 - 1 / 6)
    hcontTrace hzeroRaw hweak₀ hL2₀
  have htraceShift := buGaussian_shifted_trace_strip_tendsto
    (σ := (1 / 6 : ℝ)) hBopen.measurableSet u htraceRaw
  exact ⟨hweak₀, hBfinite,
    gaussian_average_choose_cutoff_stage hρ hδ u Du D2u Dtu
      htraceShift hweak₀ hL2Shift⟩

private theorem gaussian_average_cutoff_carleman_stage
    {ρ ε a c₀ : ℝ} (hρlarge : 4 < ρ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hεle : ε ≤ 1 / 12) (ha : 1 < a)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtu : ParabolicPoint → Vec3)
    (hweak₀ : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ)
      (Ioo 0 (2 - 1 / 6)) u Du D2u Dtu)
    (hweakShift : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
      (buGaussianShiftedField (1 / 6) u)
      (buGaussianShiftedDw (1 / 6) Du)
      (buGaussianShiftedD2w (1 / 6) Du D2u)
      (buGaussianShiftedDtw (1 / 6) Dtu))
    (hL2Shift : (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2),
      ‖buGaussianShiftedField (1 / 6) u z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDw (1 / 6) Du z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedD2w (1 / 6) D2u z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDtw (1 / 6) Dtu z‖ₑ ^ (2 : ℝ)) < ⊤)
    (support : GaussianAverageCutoffSupport ρ ε hρ u Du D2u Dtu) :
    (Integrable (fun z => vec3EuclideanNorm
        (buGaussianShiftedField (1 / 6) u z) ^ 2)
      (volume.restrict (spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2))) ∧
      Integrable (fun z => spatialGradientSq
        (buGaussianShiftedField (1 / 6) u)
        (buGaussianShiftedDw (1 / 6) Du) z)
        (volume.restrict (spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2)))) ∧
    Integrable (fun z => vec3EuclideanNorm
      (buGaussianShiftedField (1 / 6) u z) ^ 2)
      (volume.restrict support.K) ∧
    Integrable (fun z => spatialGradientSq
      (buGaussianShiftedField (1 / 6) u)
      (buGaussianShiftedDw (1 / 6) Du) z) (volume.restrict support.K) ∧
    AEStronglyMeasurable (ucGaussianWeight a) (volume.restrict support.K) ∧
    (∀ᵐ z ∂(volume.restrict support.K),
      ‖ucGaussianWeight a z‖ ≤
        ((1 / 6 : ℝ) * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a)) ∧
    Integrable (fun z => ucGaussianWeight a z *
      (a / z.2 * vec3EuclideanNorm
        (buGaussianShiftedCutoffField ρ hρ ε u z) ^ 2 +
        spatialGradientSq (buGaussianShiftedCutoffField ρ hρ ε u)
          (buGaussianShiftedCutoffDw ρ hρ ε u Du) z))
      (volume.restrict support.K) ∧
    Integrable (fun z => ucGaussianWeight a z *
      vec3EuclideanNorm (ucWeakHeatVector
        (buGaussianShiftedCutoffD2w ρ hρ ε u Du D2u)
        (buGaussianShiftedCutoffDtw ρ hρ ε u Dtu) z) ^ 2)
      (volume.restrict support.K) ∧
    Real.exp (-(3 / 2 : ℝ)) *
      (∫ z in spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2) 1),
        vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) ^ 2) ≤
      ∫ z in support.K, ucGaussianWeight a z *
        (a / z.2 * vec3EuclideanNorm
          (buGaussianShiftedCutoffField ρ hρ ε u z) ^ 2 +
          spatialGradientSq (buGaussianShiftedCutoffField ρ hρ ε u)
            (buGaussianShiftedCutoffDw ρ hρ ε u Du) z) ∧
    (∫ z in support.K, ucGaussianWeight a z *
        (a / z.2 * vec3EuclideanNorm
          (buGaussianShiftedCutoffField ρ hρ ε u z) ^ 2 +
          spatialGradientSq (buGaussianShiftedCutoffField ρ hρ ε u)
            (buGaussianShiftedCutoffDw ρ hρ ε u Du) z)) ≤
      c₀ * (∫ z in support.K, ucGaussianWeight a z *
        vec3EuclideanNorm (ucWeakHeatVector
          (buGaussianShiftedCutoffD2w ρ hρ ε u Du D2u)
          (buGaussianShiftedCutoffDtw ρ hρ ε u Dtu) z) ^ 2) ∧
    0 ≤ᵐ[volume.restrict support.K] (fun z => ucGaussianWeight a z *
      (a / z.2 * vec3EuclideanNorm
        (buGaussianShiftedCutoffField ρ hρ ε u z) ^ 2 +
        spatialGradientSq (buGaussianShiftedCutoffField ρ hρ ε u)
          (buGaussianShiftedCutoffDw ρ hρ ε u Du) z)) := by
  let S₁ : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
  let Q₀ : Set ParabolicPoint :=
    spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2) 1)
  let v := buGaussianShiftedField (1 / 6) u
  let Dv := buGaussianShiftedDw (1 / 6) Du
  let cut := buGaussianShiftedCutoffField ρ hρ ε u
  let cutDw := buGaussianShiftedCutoffDw ρ hρ ε u Du
  let cutD2 := buGaussianShiftedCutoffD2w ρ hρ ε u Du D2u
  let cutDt := buGaussianShiftedCutoffDtw ρ hρ ε u Dtu
  let Vsrc : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (v z) ^ 2
  let W : ParabolicPoint → ℝ := ucGaussianWeight a
  let carMass : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (cut z) ^ 2
  let carEnergy : ParabolicPoint → ℝ := fun z =>
    W z * (a / z.2 * carMass z + spatialGradientSq cut cutDw z)
  let heatEnergy : ParabolicPoint → ℝ := fun z =>
    W z * vec3EuclideanNorm (ucWeakHeatVector cutD2 cutDt z) ^ 2
  let Wmax : ℝ := ((1 / 6 : ℝ) * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a)
  have hQsubS₁ : Q₀ ⊆ S₁ := support.hQsubK.trans support.hKsubS₁
  have hsrcEnergy := buGaussian_local_energy_integrable hweakShift hL2Shift
  have hsrcMassQ : Integrable Vsrc (volume.restrict Q₀) :=
    hsrcEnergy.1.mono_measure (Measure.restrict_mono hQsubS₁ le_rfl)
  have hsrcMassK : Integrable Vsrc (volume.restrict support.K) :=
    hsrcEnergy.1.mono_measure (Measure.restrict_mono support.hKsubS₁ le_rfl)
  have hsrcGradK : Integrable (spatialGradientSq v Dv)
      (volume.restrict support.K) :=
    hsrcEnergy.2.mono_measure (Measure.restrict_mono support.hKsubS₁ le_rfl)
  have hWmeas : AEStronglyMeasurable W (volume.restrict support.K) :=
    (ucGaussianWeight_measurable a).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have hWbound : ∀ᵐ z ∂(volume.restrict support.K), ‖W z‖ ≤ Wmax := by
    filter_upwards [ae_restrict_mem support.hKmeas] with z hz
    have hzS := support.hKsubS₁ hz
    have hslo : (1 / 6 : ℝ) ≤ z.2 := hzS.2.1.le
    have hshi : z.2 ≤ 2 := hzS.2.2.le
    have hspos : 0 < z.2 := by linarith only [hslo]
    rw [Real.norm_eq_abs, abs_of_nonneg (ucGaussianWeight_nonneg a hspos)]
    exact ucGaussianWeight_le_after (by norm_num) (by linarith only [ha])
      hslo hshi
  have hcutEnergy := bu_memLp_quadratic_energy_integrable support.K cut cutDw
    (support.hmemCut.mono_measure Measure.restrict_le_self)
    (support.hmemDwCut.mono_measure Measure.restrict_le_self)
  have hcutHeat := bu_memLp_heat_sq_integrable support.K cutD2 cutDt
    (support.hmemD2Cut.mono_measure Measure.restrict_le_self)
    (support.hmemDtCut.mono_measure Measure.restrict_le_self)
  have hWcarMass : Integrable (fun z => W z * carMass z)
      (volume.restrict support.K) := hcutEnergy.1.bdd_mul hWmeas hWbound
  have hWcarGrad : Integrable (fun z => W z * spatialGradientSq cut cutDw z)
      (volume.restrict support.K) := hcutEnergy.2.bdd_mul hWmeas hWbound
  have hWheat : Integrable (fun z => W z *
      vec3EuclideanNorm (ucWeakHeatVector cutD2 cutDt z) ^ 2)
      (volume.restrict support.K) := hcutHeat.bdd_mul hWmeas hWbound
  have hcoefMeas : AEStronglyMeasurable (fun z : ParabolicPoint => a / z.2)
      (volume.restrict support.K) :=
    (measurable_const.div measurable_snd).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have hcoefBound : ∀ᵐ z ∂(volume.restrict support.K),
      ‖a / z.2‖ ≤ 6 * a := by
    filter_upwards [ae_restrict_mem support.hKmeas] with z hz
    have hzS := support.hKsubS₁ hz
    have hslo : (1 / 6 : ℝ) ≤ z.2 := hzS.2.1.le
    have hspos : 0 < z.2 := by linarith only [hslo]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith only [ha]) hspos.le)]
    apply (div_le_iff₀ hspos).2
    nlinarith only [ha, hslo]
  have hcoefCarMass : Integrable (fun z => W z * (a / z.2 * carMass z))
      (volume.restrict support.K) := by
    have h := hWcarMass.bdd_mul hcoefMeas hcoefBound
    convert h using 1
    ext z
    ring
  have hcarEnergyInt : Integrable carEnergy (volume.restrict support.K) := by
    have h := hcoefCarMass.add hWcarGrad
    convert h using 1
    ext z
    simp [carEnergy]
    ring
  have hcarHeatInt : Integrable heatEnergy (volume.restrict support.K) := by
    simpa [heatEnergy] using hWheat
  have hcarleman0 := buGaussian_shifted_cutoff_carleman hρ hε hweak₀ hL2Shift a ha.le
  have hcarleman : (∫ z in U₀, carEnergy z) ≤
      c₀ * ∫ z in U₀, heatEnergy z := hcarleman0
  have hU₀meas : MeasurableSet U₀ := by
    exact (isOpen_spaceTimeSet _ _ isOpen_univ isOpen_Ioo).measurableSet
  have hcarMassZero : ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      z ∈ U₀ → z ∉ support.K → carEnergy z = 0 := by
    filter_upwards [] with z
    intro _ hzK
    have hz := support.hcutZero z hzK
    simp [carEnergy, carMass, cut, cutDw, spatialGradientSq,
      hz.1, hz.2.1, vec3EuclideanNorm_zero]
  have hcarHeatZero : ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      z ∈ U₀ → z ∉ support.K → heatEnergy z = 0 := by
    filter_upwards [] with z
    intro _ hzK
    have hz := support.hcutZero z hzK
    have hheat : ucWeakHeatVector cutD2 cutDt z = 0 := by
      change (fun i => cutDt z i + ∑ j : Fin 3, cutD2 z i j j) = 0
      rw [show cutDt z = 0 from hz.2.2.2,
        show cutD2 z = 0 from hz.2.2.1]
      funext i
      simp
    simp [heatEnergy, hheat, vec3EuclideanNorm_zero]
  have hcarDensityPoint : ∀ z ∈ Q₀,
      Real.exp (-(3 / 2 : ℝ)) * Vsrc z ≤ carEnergy z := by
    intro z hz
    have hdensity := buGaussian_carleman_mass_density_lower
      hρlarge ha.le hε hεle u z hz
    have hgrad : 0 ≤ spatialGradientSq cut cutDw z := by
      dsimp [spatialGradientSq]
      positivity
    have hWnonneg : 0 ≤ W z := by
      have htime : 0 < z.2 := by linarith only [hz.2.1]
      exact ucGaussianWeight_nonneg a htime
    have hbase : Real.exp (-(3 / 2 : ℝ)) * Vsrc z ≤
        W z * (a / z.2 * carMass z) := by
      simpa [Vsrc, v, W, a, carMass, cut, cutDw, σ, mul_assoc] using hdensity
    calc
      _ ≤ W z * (a / z.2 * carMass z) := hbase
      _ ≤ carEnergy z := by
        dsimp [carEnergy]
        apply mul_le_mul_of_nonneg_left _ hWnonneg
        exact le_add_of_nonneg_right hgrad
  have hcarEnergyNonneg : 0 ≤ᵐ[volume.restrict support.K] carEnergy := by
    filter_upwards [ae_restrict_mem support.hKmeas] with z hz
    have hzS := support.hKsubS₁ hz
    have htimepos : 0 < z.2 := by
      have hs : (1 / 6 : ℝ) < z.2 := hzS.2.1
      norm_num at hs ⊢
      linarith only [hs]
    have hgrad : 0 ≤ spatialGradientSq cut cutDw z := by
      dsimp [spatialGradientSq]
      positivity
    exact mul_nonneg (ucGaussianWeight_nonneg a htimepos)
      (add_nonneg (mul_nonneg (div_nonneg (by linarith only [ha]) htimepos.le)
        (sq_nonneg _)) hgrad)
  have hcarlemanBounds := gaussian_carleman_cutoff_mass_lower
    hU₀meas support.hKmeas support.hQmeas support.hKsubU₀
    support.hQsubK c₀ hsrcMassQ hcarEnergyInt hcarEnergyNonneg
    hcarleman hcarMassZero hcarHeatZero hcarDensityPoint
  exact ⟨hsrcEnergy, hsrcMassK, hsrcGradK, hWmeas, hWbound,
    hcarEnergyInt, hcarHeatInt, hcarlemanBounds.1, hcarlemanBounds.2,
    hcarEnergyNonneg⟩

private theorem gaussian_average_integrate_cutoff_errors
    {μ : Measure ParabolicPoint} {K Shell Late Initial : Set ParabolicPoint}
    (W Vsrc Gsrc carEnergy heatEnergy shell late initial : ParabolicPoint → ℝ)
    (c₁ scale shell0 shell1 ε : ℝ) (hε : ε ≠ 0)
    (hShellMeas : MeasurableSet Shell) (hLateMeas : MeasurableSet Late)
    (hInitialMeas : MeasurableSet Initial)
    (hWsrcMass : Integrable (fun z => W z * Vsrc z) (μ.restrict K))
    (hWsrcGrad : Integrable (fun z => W z * Gsrc z) (μ.restrict K))
    (hWsrcMassNonneg : 0 ≤ᵐ[μ.restrict K] (fun z => W z * Vsrc z))
    (hWsrcGradNonneg : 0 ≤ᵐ[μ.restrict K] (fun z => W z * Gsrc z))
    (hcarEnergyInt : Integrable carEnergy (μ.restrict K))
    (hcarHeatInt : Integrable heatEnergy (μ.restrict K))
    (hErrorPoint : ∀ᵐ z ∂(μ.restrict K),
      heatEnergy z ≤
        72 * (c₁ * scale) ^ 2 * carEnergy z +
          4 * W z * (shell z ^ 2 + late z ^ 2 + initial z ^ 2))
    (hWnonneg : ∀ᵐ z ∂(μ.restrict K), 0 ≤ W z)
    (hShellFormula : ∀ z, shell z =
      if z ∈ Shell then shell0 * Real.sqrt (Vsrc z) +
        shell1 * Real.sqrt (Gsrc z) else 0)
    (hLateFormula : ∀ z, late z =
      if z ∈ Late then 32 * Real.sqrt (Vsrc z) else 0)
    (hInitialFormula : ∀ z, initial z =
      if z ∈ Initial then (8 / ε) * Real.sqrt (Vsrc z) else 0) :
    Integrable
        (fun z => 72 * (c₁ * scale) ^ 2 * carEnergy z +
          8 * shell0 ^ 2 * Shell.indicator (fun z => W z * Vsrc z) z +
          8 * shell1 ^ 2 * Shell.indicator (fun z => W z * Gsrc z) z +
          4096 * Late.indicator (fun z => W z * Vsrc z) z +
          (256 / ε ^ 2) * Initial.indicator (fun z => W z * Vsrc z) z)
        (μ.restrict K) ∧
      (∫ z in K, heatEnergy z) ≤
        ∫ z in K, (72 * (c₁ * scale) ^ 2 * carEnergy z +
          8 * shell0 ^ 2 * Shell.indicator (fun z => W z * Vsrc z) z +
          8 * shell1 ^ 2 * Shell.indicator (fun z => W z * Gsrc z) z +
          4096 * Late.indicator (fun z => W z * Vsrc z) z +
          (256 / ε ^ 2) * Initial.indicator (fun z => W z * Vsrc z) z) := by
  let shellMass : ParabolicPoint → ℝ :=
    Shell.indicator (fun z => W z * Vsrc z)
  let shellGrad : ParabolicPoint → ℝ :=
    Shell.indicator (fun z => W z * Gsrc z)
  let lateMass : ParabolicPoint → ℝ :=
    Late.indicator (fun z => W z * Vsrc z)
  let initialMass : ParabolicPoint → ℝ :=
    Initial.indicator (fun z => W z * Vsrc z)
  let major : ParabolicPoint → ℝ := fun z =>
    72 * (c₁ * scale) ^ 2 * carEnergy z +
      8 * shell0 ^ 2 * shellMass z +
      8 * shell1 ^ 2 * shellGrad z + 4096 * lateMass z +
      (256 / ε ^ 2) * initialMass z
  have hShellMassInt : Integrable shellMass (μ.restrict K) := by
    rw [hShellMassEq]
    exact hWsrcMass.indicator hShellMeas
  have hShellGradInt : Integrable shellGrad (μ.restrict K) := by
    rw [hShellGradEq]
    exact hWsrcGrad.indicator hShellMeas
  have hLateMassInt : Integrable lateMass (μ.restrict K) := by
    simpa [lateMass] using hWsrcMass.indicator hLateMeas
  have hInitialMassInt : Integrable initialMass (μ.restrict K) := by
    rw [hInitialMassEq]
    exact hWsrcMass.indicator hInitialMeas
  have hMajorInt : Integrable major (μ.restrict K) := by
    dsimp [major]
    exact (((hcarEnergyInt.const_mul _).add
      (hShellMassInt.const_mul _)).add
      (hShellGradInt.const_mul _)).add
      (hLateMassInt.const_mul _) |>.add (hInitialMassInt.const_mul _)
  have hMajorPoint : ∀ᵐ z ∂(μ.restrict K), heatEnergy z ≤ major z := by
    have hMajorPoint' := gaussian_average_cutoff_error_major
      (μ := μ.restrict K) c₁ scale shell0 shell1 ε hε
      hErrorPoint hWnonneg (fun z => sq_nonneg _) (fun z => by
        dsimp [spatialGradientSq]
        positivity) hShellFormula hLateFormula hInitialFormula
    simpa [major, shellMass, shellGrad, lateMass, initialMass] using hMajorPoint'
  have hMajorIntegral := integral_mono_ae hcarHeatInt hMajorInt hMajorPoint
  exact ⟨by simpa [major, shellMass, shellGrad, lateMass, initialMass] using hMajorInt,
    by simpa [major, shellMass, shellGrad, lateMass, initialMass] using hMajorIntegral⟩

private theorem gaussian_average_absorb_integrated_cutoff_errors
    {K Shell Late Initial : Set ParabolicPoint}
    (W Vsrc Gsrc carEnergy heatEnergy shell late initial : ParabolicPoint → ℝ)
    (c₀ C_G c₁ scale t γ shell0 shell1 ε : ℝ)
    (hC₀ : 0 ≤ c₀) (hCG : C_G = 72 * c₀)
    (hc₁ : 0 < c₁) (hscaleSq : scale ^ 2 = 3 * t)
    (htγ : t < γ) (hγabsorb : 3 * C_G * c₁ ^ 2 * γ ≤ 1 / 2)
    (hε : ε ≠ 0)
    (hShellMeas : MeasurableSet Shell) (hLateMeas : MeasurableSet Late)
    (hInitialMeas : MeasurableSet Initial)
    (hWsrcMass : Integrable (fun z => W z * Vsrc z) (volume.restrict K))
    (hWsrcGrad : Integrable (fun z => W z * Gsrc z) (volume.restrict K))
    (hWsrcMassNonneg : 0 ≤ᵐ[volume.restrict K] (fun z => W z * Vsrc z))
    (hWsrcGradNonneg : 0 ≤ᵐ[volume.restrict K] (fun z => W z * Gsrc z))
    (hcarEnergyInt : Integrable carEnergy (volume.restrict K))
    (hcarHeatInt : Integrable heatEnergy (volume.restrict K))
    (hcarEnergyNonneg : 0 ≤ᵐ[volume.restrict K] carEnergy)
    (hErrorPoint : ∀ᵐ z ∂(volume.restrict K),
      heatEnergy z ≤ 72 * (c₁ * scale) ^ 2 * carEnergy z +
        4 * W z * (shell z ^ 2 + late z ^ 2 + initial z ^ 2))
    (hWnonneg : ∀ᵐ z ∂(volume.restrict K), 0 ≤ W z)
    (hShellFormula : ∀ z, shell z =
      if z ∈ Shell then shell0 * Real.sqrt (Vsrc z) +
        shell1 * Real.sqrt (Gsrc z) else 0)
    (hLateFormula : ∀ z, late z =
      if z ∈ Late then 32 * Real.sqrt (Vsrc z) else 0)
    (hInitialFormula : ∀ z, initial z =
      if z ∈ Initial then (8 / ε) * Real.sqrt (Vsrc z) else 0)
    (hcarlemanK : (∫ z in K, carEnergy z) ≤
      c₀ * (∫ z in K, heatEnergy z)) :
    ∃ Icar Eerr : ℝ, Icar = (∫ z in K, carEnergy z) ∧
      Eerr = 8 * shell0 ^ 2 * (∫ z in K,
        Shell.indicator (fun z => W z * Vsrc z) z) +
        8 * shell1 ^ 2 * (∫ z in K,
          Shell.indicator (fun z => W z * Gsrc z) z) +
        4096 * (∫ z in K, Late.indicator (fun z => W z * Vsrc z) z) +
        (256 / ε ^ 2) * (∫ z in K, Initial.indicator (fun z => W z * Vsrc z) z) ∧
      Icar ≤ 2 * c₀ * Eerr := by
  let shellMass : ParabolicPoint → ℝ :=
    Shell.indicator (fun z => W z * Vsrc z)
  let shellGrad : ParabolicPoint → ℝ :=
    Shell.indicator (fun z => W z * Gsrc z)
  let lateMass : ParabolicPoint → ℝ :=
    Late.indicator (fun z => W z * Vsrc z)
  let initialMass : ParabolicPoint → ℝ :=
    Initial.indicator (fun z => W z * Vsrc z)
  let major : ParabolicPoint → ℝ := fun z =>
    72 * (c₁ * scale) ^ 2 * carEnergy z +
      8 * shell0 ^ 2 * shellMass z + 8 * shell1 ^ 2 * shellGrad z +
      4096 * lateMass z + (256 / ε ^ 2) * initialMass z
  have hShellMassInt : Integrable shellMass (volume.restrict K) := by
    simpa [shellMass] using hWsrcMass.indicator hShellMeas
  have hShellGradInt : Integrable shellGrad (volume.restrict K) := by
    simpa [shellGrad] using hWsrcGrad.indicator hShellMeas
  have hLateMassInt : Integrable lateMass (volume.restrict K) := by
    rw [hLateMassDefEq]
    exact hWsrcMass.indicator hLateMeas
  have hInitialMassInt : Integrable initialMass (volume.restrict K) := by
    simpa [initialMass] using hWsrcMass.indicator hInitialMeas
  have hShellMassNonneg : 0 ≤ ∫ z in K, shellMass z := by
    rw [hShellMassEq]
    exact buGaussian_indicator_integral_nonneg K Shell
      (fun z => W z * Vsrc z) hWsrcMassNonneg
  have hShellGradNonneg : 0 ≤ ∫ z in K, shellGrad z := by
    rw [hShellGradEq]
    exact buGaussian_indicator_integral_nonneg K Shell
      (fun z => W z * Gsrc z) hWsrcGradNonneg
  have hIntegratedErrors := gaussian_average_integrate_cutoff_errors
    (μ := volume) W Vsrc Gsrc carEnergy heatEnergy shell late initial
    c₁ scale shell0 shell1 ε hε hShellMeas hLateMeas hInitialMeas
    hWsrcMass hWsrcGrad hWsrcMassNonneg hWsrcGradNonneg
    hcarEnergyInt hcarHeatInt hErrorPoint hWnonneg
    hShellFormula hLateFormula hInitialFormula
  have hMajorInt : Integrable major (volume.restrict K) := by
    simpa [major, shellMass, shellGrad, lateMass, initialMass] using
      hIntegratedErrors.1
  have hMajorIntegral : (∫ z in K, heatEnergy z) ≤
      ∫ z in K, major z := by
    simpa [major, shellMass, shellGrad, lateMass, initialMass] using
      hIntegratedErrors.2
  let Icar : ℝ := ∫ z in K, carEnergy z
  let Eerr : ℝ :=
    8 * shell0 ^ 2 * (∫ z in K, shellMass z) +
      8 * shell1 ^ 2 * (∫ z in K, shellGrad z) +
      4096 * (∫ z in K, lateMass z) +
      (256 / ε ^ 2) * (∫ z in K, initialMass z)
  have hMajorEq : (∫ z in K, major z) =
      72 * (c₁ * scale) ^ 2 * Icar + Eerr := by
    dsimp [major, Icar, Eerr]
    rw [integral_add, integral_add, integral_add, integral_add]
    · simp only [integral_const_mul]
      ring
    all_goals first
      | exact hcarEnergyInt.const_mul _
      | exact hShellMassInt.const_mul _
      | exact hShellGradInt.const_mul _
      | exact hLateMassInt.const_mul _
      | exact hInitialMassInt.const_mul _
      | exact (hcarEnergyInt.const_mul _).add (hShellMassInt.const_mul _)
      | exact ((hcarEnergyInt.const_mul _).add
          (hShellMassInt.const_mul _)).add (hShellGradInt.const_mul _)
      | exact (((hcarEnergyInt.const_mul _).add
          (hShellMassInt.const_mul _)).add
          (hShellGradInt.const_mul _)).add (hLateMassInt.const_mul _)
  have hIcarNonneg : 0 ≤ Icar := by
    dsimp [Icar]
    exact integral_nonneg_of_ae hcarEnergyNonneg
  have hAbsorbed := gaussian_average_absorb_car_energy
    c₀ C_G c₁ scale t γ Icar Eerr hC₀ hCG hcarlemanK
    hMajorIntegral hMajorEq hscaleSq htγ hγabsorb hIcarNonneg
  exact ⟨Icar, Eerr, rfl, by
    dsimp [Eerr, shellMass, shellGrad, lateMass, initialMass]
    ring, hAbsorbed⟩

private theorem gaussian_average_weighted_operator_error_point
    {ρ ε a c₁ scale : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hεsmall : 2 * ε ≤ 1 / 2) (hc₁ : 0 ≤ c₁) (hscale : 0 ≤ scale)
    (ha : 1 < a) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtu : ParabolicPoint → Vec3)
    (hineq : ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
      vec3EuclideanNorm (ucWeakHeatVector D2u Dtu z) ≤
        c₁ * scale * (vec3EuclideanNorm (u z) +
          Real.sqrt (spatialGradientSq u Du z)))
    {K : Set ParabolicPoint}
    (hKsub : K ⊆ spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2))
    (hKmeas : MeasurableSet K) :
    ∀ᵐ z ∂(volume.restrict K),
      ucGaussianWeight a z * vec3EuclideanNorm
        (ucWeakHeatVector (buGaussianShiftedCutoffD2w ρ hρ ε u Du D2u)
          (buGaussianShiftedCutoffDtw ρ hρ ε u Dtu) z) ^ 2 ≤
      72 * (c₁ * scale) ^ 2 * (ucGaussianWeight a z *
        (a / z.2 * vec3EuclideanNorm
          (buGaussianShiftedCutoffField ρ hρ ε u z) ^ 2 +
          spatialGradientSq (buGaussianShiftedCutoffField ρ hρ ε u)
            (buGaussianShiftedCutoffDw ρ hρ ε u Du) z)) +
      4 * ucGaussianWeight a z *
        ((if 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
            vec3EuclideanNorm z.1 ≤ 3 * ρ / 4 then
          (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
            3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
              vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) +
          18 * (cutoffGradientConstant / ρ) *
            Real.sqrt (spatialGradientSq (buGaussianShiftedField (1 / 6) u)
              (buGaussianShiftedDw (1 / 6) Du) z) else 0) ^ 2 +
        (if 3 / 2 ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
            ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 7 / 4 then
          32 * vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) else 0) ^ 2 +
        (if ε ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
            ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 2 * ε then
          (8 / ε) * vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) else 0) ^ 2) ∧
    (∀ᵐ z ∂(volume.restrict K), 0 ≤ ucGaussianWeight a z) ∧
    (∀ z, (if 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
        vec3EuclideanNorm z.1 ≤ 3 * ρ / 4 then
      (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
        3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
          vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) +
      18 * (cutoffGradientConstant / ρ) * Real.sqrt (spatialGradientSq
        (buGaussianShiftedField (1 / 6) u)
        (buGaussianShiftedDw (1 / 6) Du) z) else 0) =
      if 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
        vec3EuclideanNorm z.1 ≤ 3 * ρ / 4 then
      (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
        3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
          Real.sqrt (vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) ^ 2) +
      18 * (cutoffGradientConstant / ρ) * Real.sqrt (spatialGradientSq
        (buGaussianShiftedField (1 / 6) u)
        (buGaussianShiftedDw (1 / 6) Du) z) else 0) ∧
    (∀ z, (if 3 / 2 ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
        ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 7 / 4 then
      32 * vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) else 0) =
      if 3 / 2 ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
        ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 7 / 4 then
      32 * Real.sqrt (vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) ^ 2) else 0) ∧
    (∀ z, (if ε ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
        ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 2 * ε then
      (8 / ε) * vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) else 0) =
      if ε ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
        ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 2 * ε then
      (8 / ε) * Real.sqrt (vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) ^ 2) else 0) := by
  have hOp₀ := buGaussian_shifted_operator_localized_ae_bound
    hρ hε hεsmall hc₁ hscale u Du D2u Dtu hineq
  have hOpRestrict := ae_mono (Measure.restrict_mono hKsub le_rfl) hOp₀
  have hOpBound : ∀ᵐ z ∂(volume.restrict K),
      vec3EuclideanNorm (ucWeakHeatVector
        (buGaussianShiftedCutoffD2w ρ hρ ε u Du D2u)
        (buGaussianShiftedCutoffDtw ρ hρ ε u Dtu) z) ≤
      c₁ * scale * (vec3EuclideanNorm
          (buGaussianShiftedCutoffField ρ hρ ε u z) +
        3 * Real.sqrt (spatialGradientSq
          (buGaussianShiftedCutoffField ρ hρ ε u)
          (buGaussianShiftedCutoffDw ρ hρ ε u Du) z)) +
      (if 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
          vec3EuclideanNorm z.1 ≤ 3 * ρ / 4 then
        (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
          3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
            vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) +
        18 * (cutoffGradientConstant / ρ) *
          Real.sqrt (spatialGradientSq (buGaussianShiftedField (1 / 6) u)
            (buGaussianShiftedDw (1 / 6) Du) z) else 0) +
      (if 3 / 2 ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
          ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 7 / 4 then
        32 * vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) else 0) +
      (if ε ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
          ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 2 * ε then
        (8 / ε) * vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) else 0) := by
    simpa only using hOpRestrict
  have hErrorPoint := by
    filter_upwards [hOpBound, ae_restrict_mem hKmeas] with z hOp hzK
    have hzS := hKsub hzK
    have hspos : 0 < z.2 := by
      have hs := hzS.2.1
      norm_num at hs ⊢
      linarith only [hs]
    have hq : (1 / 2 : ℝ) ≤ a / z.2 := by
      apply (le_div_iff₀ hspos).2
      nlinarith only [ha, hzS.2.2]
    have hm : 0 ≤ vec3EuclideanNorm
        (buGaussianShiftedCutoffField ρ hρ ε u z) ^ 2 := sq_nonneg _
    have hg : 0 ≤ spatialGradientSq
        (buGaussianShiftedCutoffField ρ hρ ε u)
        (buGaussianShiftedCutoffDw ρ hρ ε u Du) z := by
      dsimp [spatialGradientSq]
      positivity
    have hW : 0 ≤ ucGaussianWeight a z := ucGaussianWeight_nonneg a hspos
    have hh : 0 ≤ vec3EuclideanNorm (ucWeakHeatVector
        (buGaussianShiftedCutoffD2w ρ hρ ε u Du D2u)
        (buGaussianShiftedCutoffDtw ρ hρ ε u Dtu) z) := vec3EuclideanNorm_nonneg _
    have hpoint := buGaussian_weighted_four_error_bound
      (W := ucGaussianWeight a z) (q := a / z.2)
      (m := vec3EuclideanNorm
        (buGaussianShiftedCutoffField ρ hρ ε u z) ^ 2)
      (g := spatialGradientSq (buGaussianShiftedCutoffField ρ hρ ε u)
        (buGaussianShiftedCutoffDw ρ hρ ε u Du) z) (c := c₁ * scale)
      (b := if 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
          vec3EuclideanNorm z.1 ≤ 3 * ρ / 4 then
        (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
          3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
            vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) +
        18 * (cutoffGradientConstant / ρ) * Real.sqrt (spatialGradientSq
          (buGaussianShiftedField (1 / 6) u)
          (buGaussianShiftedDw (1 / 6) Du) z) else 0)
      (d := if 3 / 2 ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
          ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 7 / 4 then
        32 * vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) else 0)
      (e := if ε ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
          ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 2 * ε then
        (8 / ε) * vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) else 0)
      (h := vec3EuclideanNorm (ucWeakHeatVector
        (buGaussianShiftedCutoffD2w ρ hρ ε u Du D2u)
        (buGaussianShiftedCutoffDtw ρ hρ ε u Dtu) z))
      hW hq hm hg hh hOp
    simpa [mul_assoc] using hpoint
  have hWeightNonneg : ∀ᵐ z ∂(volume.restrict K), 0 ≤ ucGaussianWeight a z := by
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    have hzS := hKsub hz
    have hs : (1 / 6 : ℝ) < z.2 := hzS.2.1
    have hspos : 0 < z.2 := by linarith only [hs]
    exact ucGaussianWeight_nonneg a hspos
  have hShellFormula (z : ParabolicPoint) :
      (if 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
          vec3EuclideanNorm z.1 ≤ 3 * ρ / 4 then
        (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
          3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
            vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) +
        18 * (cutoffGradientConstant / ρ) * Real.sqrt (spatialGradientSq
          (buGaussianShiftedField (1 / 6) u)
          (buGaussianShiftedDw (1 / 6) Du) z) else 0) =
      if 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
          vec3EuclideanNorm z.1 ≤ 3 * ρ / 4 then
        (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
          3 * c₁ * scale * (cutoffGradientConstant / ρ)) *
            Real.sqrt (vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) ^ 2) +
        18 * (cutoffGradientConstant / ρ) * Real.sqrt (spatialGradientSq
          (buGaussianShiftedField (1 / 6) u)
          (buGaussianShiftedDw (1 / 6) Du) z) else 0 := by
    by_cases hz : 13 * ρ / 20 ≤ vec3EuclideanNorm z.1 ∧
        vec3EuclideanNorm z.1 ≤ 3 * ρ / 4
    · simp [hz, Real.sqrt_sq (vec3EuclideanNorm_nonneg _)]
    · simp [hz]
  have hLateFormula (z : ParabolicPoint) :
      (if 3 / 2 ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
          ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 7 / 4 then
        32 * vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) else 0) =
      if 3 / 2 ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
          ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 7 / 4 then
        32 * Real.sqrt (vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) ^ 2) else 0 := by
    by_cases hz : 3 / 2 ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
        ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 7 / 4
    · simp [hz, Real.sqrt_sq (vec3EuclideanNorm_nonneg _)]
    · simp [hz]
  have hInitialFormula (z : ParabolicPoint) :
      (if ε ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
          ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 2 * ε then
        (8 / ε) * vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) else 0) =
      if ε ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
          ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 2 * ε then
        (8 / ε) * Real.sqrt (vec3EuclideanNorm (buGaussianShiftedField (1 / 6) u z) ^ 2) else 0 := by
    by_cases hz : ε ≤ ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ∧
        ((buGaussianTimeShiftPoint (1 / 6)).symm z).2 ≤ 2 * ε
    · simp [hz, Real.sqrt_sq (vec3EuclideanNorm_nonneg _)]
    · simp [hz]
  exact ⟨hErrorPoint, hWeightNonneg, hShellFormula, hLateFormula,
    hInitialFormula⟩

private theorem gaussian_average_prepare_cutoff_carleman
    {ρ δ scale : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hρlarge : 4 < ρ)
    (c₁ a c₀ : ℝ) (ha : 1 < a)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtu : ParabolicPoint → Vec3)
    (hcontRaw : ContinuousOn u (vec3Ball 0 ρ ×ˢ Ioo 0 2))
    (hzeroRaw : ∀ y : Vec3, y ∈ vec3Ball 0 ρ → u (y, 0) = 0)
    (hweakRaw : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      u Du D2u Dtu)
    (hL2Raw : (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo 0 2),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) +
        ‖D2u z‖ₑ ^ (2 : ℝ) + ‖Dtu z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineqRaw : ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
      vec3EuclideanNorm (ucWeakHeatVector D2u Dtu z) ≤
        c₁ * scale * (vec3EuclideanNorm (u z) +
          Real.sqrt (spatialGradientSq u Du z)))
    (hweakShift : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
      (buGaussianShiftedField (1 / 6) u)
      (buGaussianShiftedDw (1 / 6) Du)
      (buGaussianShiftedD2w (1 / 6) D2u)
      (buGaussianShiftedDtw (1 / 6) Dtu))
    (hL2Shift : (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2),
      ‖buGaussianShiftedField (1 / 6) u z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDw (1 / 6) Du z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedD2w (1 / 6) D2u z‖ₑ ^ (2 : ℝ) +
        ‖buGaussianShiftedDtw (1 / 6) Dtu z‖ₑ ^ (2 : ℝ)) < ⊤) :
    ∃ hweak₀ : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ)
        (Ioo 0 (2 - 1 / 6)) u Du D2u Dtu,
      ∃ hBfinite : volume (vec3Ball 0 ρ) < ⊤,
        ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 12 ∧
          (∫ z in spaceTimeSet (vec3Ball 0 ρ)
            (Ioc (1 / 6 + ε) (1 / 6 + 2 * ε)),
            vec3EuclideanNorm (u ((buGaussianTimeShiftPoint (1 / 6)).symm z)) ^ 2) /
              ε ^ 2 < δ ∧
          ∃ support : GaussianAverageCutoffSupport ρ ε hρ u Du D2u Dtu,
            (∀ (hε : 0 < ε) (hεle : ε ≤ 1 / 12),
              gaussian_average_cutoff_carleman_stage hρlarge hρ hε hεle ha
                u Du D2u Dtu hweak₀ hweakShift hL2Shift support) := by
  rcases gaussian_average_initial_cutoff_setup hρ hδ c₁ u Du D2u Dtu
      hcontRaw hzeroRaw hweakRaw hL2Raw hineqRaw hweakShift hL2Shift with
    ⟨hweak₀, hBfinite, ⟨ε, hε, hεle, htraceε, support⟩⟩
  refine ⟨hweak₀, hBfinite, ε, hε, hεle, htraceε, support, ?_⟩
  intro hε' hεle'
  exact gaussian_average_cutoff_carleman_stage hρlarge hρ hε' hεle' ha
    u Du D2u Dtu hweak₀ hweakShift hL2Shift support

private theorem gaussian_average_weighted_source_error_data
    {K S₁ Shell Initial : Set ParabolicPoint} {B : Set Vec3}
    (ρ ε δ a : ℝ) (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (W Vsrc Gsrc shellMass : ParabolicPoint → ℝ)
    (hρlarge : 4 < ρ) (ha : 1 < a) (hε : 0 < ε) (hεle : ε ≤ 1 / 12)
    (hKmeas : MeasurableSet K) (hKsubS₁ : K ⊆ S₁)
    (hBmeas : MeasurableSet B)
    (htraceε : (∫ z in spaceTimeSet B (Ioc (1 / 6 + ε) (1 / 6 + 2 * ε)),
      vec3EuclideanNorm (v z) ^ 2) /
        ε ^ 2 < δ)
    (hsrcMassK : Integrable (fun z => vec3EuclideanNorm (v z) ^ 2)
      (volume.restrict K))
    (hsrcGradK : Integrable (spatialGradientSq v Dv) (volume.restrict K))
    (hsrcMassS₁ : Integrable (fun z => vec3EuclideanNorm (v z) ^ 2)
      (volume.restrict S₁))
    (hWmeasK : AEStronglyMeasurable W (volume.restrict K))
    (hWboundK : ∀ᵐ z ∂(volume.restrict K), ‖W z‖ ≤
      ((1 / 6 : ℝ) * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a))
    (hShellMassEq : shellMass = Shell.indicator (fun z => W z * Vsrc z)) :
    Integrable (fun z => W z * Vsrc z) (volume.restrict K) ∧
    Integrable (fun z => W z * Gsrc z) (volume.restrict K) ∧
    0 ≤ᵐ[volume.restrict K] (fun z => W z * Vsrc z) ∧
    0 ≤ᵐ[volume.restrict K] (fun z => W z * Gsrc z) ∧
    MeasurableSet S₁ ∧
    AEStronglyMeasurable W (volume.restrict S₁) ∧
    (∀ᵐ z ∂(volume.restrict S₁), ‖W z‖ ≤
      ((1 / 6 : ℝ) * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a)) ∧
    Integrable (fun z => W z * Vsrc z) (volume.restrict S₁) ∧
    Integrable (Initial.indicator (fun z => W z * Vsrc z)) (volume.restrict K) ∧
    (∫ z in K, Initial.indicator (fun z => W z * Vsrc z) z) ≤
      ((1 / 6 : ℝ) * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a) *
        (∫ z in spaceTimeSet B (Icc (1 / 6 + ε) (1 / 6 + 2 * ε)), Vsrc z) ∧
    (∫ z in spaceTimeSet B (Icc (1 / 6 + ε) (1 / 6 + 2 * ε)), Vsrc z) /
        ε ^ 2 < δ ∧
    Integrable (buGaussianRadialWeightedMass ρ a v) (volume.restrict S₁) ∧
    0 ≤ᵐ[volume.restrict S₁] (buGaussianRadialWeightedMass ρ a v) ∧
    Integrable (buGaussianRadialWeightedMass ρ a v) (volume.restrict K) ∧
    (∀ z ∈ K, shellMass z ≤ buGaussianRadialWeightedMass ρ a v z) := by
  have hWsrcMass : Integrable (fun z => W z * Vsrc z)
      (volume.restrict K) := hsrcMassK.bdd_mul hWmeasK hWboundK
  have hWsrcGrad : Integrable (fun z => W z * Gsrc z)
      (volume.restrict K) := hsrcGradK.bdd_mul hWmeasK hWboundK
  have hWsrcMassNonneg : 0 ≤ᵐ[volume.restrict K]
      (fun z => W z * Vsrc z) := by
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    have hzS := hKsubS₁ hz
    have hspos : 0 < z.2 := by
      have hs := hzS.2.1
      norm_num at hs ⊢
      linarith only [hs]
    exact mul_nonneg (ucGaussianWeight_nonneg a hspos) (sq_nonneg _)
  have hWsrcGradNonneg : 0 ≤ᵐ[volume.restrict K]
      (fun z => W z * Gsrc z) := by
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    have hzS := hKsubS₁ hz
    have hspos : 0 < z.2 := by
      have hs := hzS.2.1
      norm_num at hs ⊢
      linarith only [hs]
    have hg : 0 ≤ Gsrc z := by dsimp [Gsrc, spatialGradientSq]; positivity
    exact mul_nonneg (ucGaussianWeight_nonneg a hspos) hg
  have hS₁meas : MeasurableSet S₁ :=
    (vec3Ball_measurable 0 ρ).prod measurableSet_Ioo
  have hWmeasS₁ : AEStronglyMeasurable W (volume.restrict S₁) :=
    (ucGaussianWeight_measurable a).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have hWboundS₁ : ∀ᵐ z ∂(volume.restrict S₁), ‖W z‖ ≤
      ((1 / 6 : ℝ) * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a) := by
    filter_upwards [ae_restrict_mem hS₁meas] with z hz
    have hslo : (1 / 6 : ℝ) ≤ z.2 := hz.2.1.le
    have hspos : 0 < z.2 := by linarith only [hslo]
    rw [Real.norm_eq_abs, abs_of_nonneg (ucGaussianWeight_nonneg a hspos)]
    exact ucGaussianWeight_le_after (by norm_num) (by linarith only [ha])
      hslo hz.2.2.le
  have hWsrcMassS₁ : Integrable (fun z => W z * Vsrc z)
      (volume.restrict S₁) := hsrcMassS₁.bdd_mul hWmeasS₁ hWboundS₁
  have hInitialData := gaussian_initial_trace_strip_error
    ha hε hεle v hKmeas hKsubS₁ hBmeas hsrcMassK hWsrcMass htraceε
  rcases hInitialData with ⟨hInitialMassInt, hInitialIntegral, hInitialTrace⟩
  have hRadialData := gaussian_average_radial_shell_mass_data
    hρlarge ha v hKsubS₁ hS₁meas hWsrcMassS₁
  rcases hRadialData with
    ⟨hRadialInt, hRadialNonneg, hRadialIntK, hShellMassPoint⟩
  have hShellMassPoint' : ∀ z ∈ K,
      shellMass z ≤ buGaussianRadialWeightedMass ρ a v z := by
    simpa [hShellMassEq, Shell, W, Vsrc] using hShellMassPoint
  exact ⟨hWsrcMass, hWsrcGrad, hWsrcMassNonneg, hWsrcGradNonneg,
    hS₁meas, hWmeasS₁, hWboundS₁, hWsrcMassS₁, hInitialMassInt,
    hInitialIntegral, hInitialTrace, hRadialInt, hRadialNonneg,
    hRadialIntK, hShellMassPoint'⟩

private structure GaussianAverageConstants (c₁ : ℝ) where
  c₀ C_G γ k₀ k₁ R₀ Cacc Ctail Ccore C : ℝ
  hc₀ : 0 < c₀
  hCG : 0 < C_G
  hγpos : 0 < γ
  hγlt : γ < 1 / 12
  hγ24 : 24 * γ ≤ 1 / 2
  hγβ : γ ≤ buGaussianBeta / (3 * buGaussianH)
  hγabsorb : 3 * C_G * c₁ ^ 2 * γ ≤ 1 / 2
  hcutG : 0 ≤ cutoffGradientConstant
  hcutS : 0 ≤ cutoffSecondDerivativeConstant
  hk₀ : 0 ≤ k₀
  hk₁ : 0 ≤ k₁
  hCacc : 0 ≤ Cacc
  hCtail : 0 < Ctail
  hCcore : 0 < Ccore
  hC : 0 < C

private theorem gaussian_average_constants (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hβ : 0 < buGaussianBeta) (hH : 0 < buGaussianH) :
    GaussianAverageConstants c₁ := by
  let c₀ : ℝ := Real.exp (4 / 3) * (9 + 2 * Real.sqrt 6)
  let C_G : ℝ := 72 * c₀
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hCG : 0 < C_G := by dsimp [C_G]; positivity
  obtain ⟨γ, hγpos, hγlt, hγ24, hγβ, hγabsorb⟩ :=
    buGaussian_parameter_choice c₁ C_G buGaussianBeta buGaussianH
      hc₁ hCG hβ hH
  let k₀ : ℝ := 32 + 3 * cutoffSecondDerivativeConstant +
    3 * c₁ * cutoffGradientConstant
  let k₁ : ℝ := 18 * cutoffGradientConstant
  let R₀ : ℝ := Real.sqrt (buGaussianH / buGaussianBeta) / 16
  let Cacc : ℝ := Real.exp (2 * (56 / 64 + 24 * R₀ + 144 * R₀ ^ 2)) *
    (256 * 256 * (1 + c₁ ^ 2)) *
      (8 * (Besicovitch.multiplicity BUGaussianSpace : ℝ) ^ 2)
  let Ctail : ℝ :=
    64 * (1 + buGaussianBeta / (2 * buGaussianH)) /
      (buGaussianBeta / 2) ^ 2 / Real.sqrt buGaussianBeta
  let Ccore : ℝ := 2 * Real.exp (3 / 2) * c₀ *
    (192 * (k₀ ^ 2 + k₁ ^ 2 * Cacc) + 49153) * Ctail
  let C : ℝ := Real.rpow 3 (5 / 2 : ℝ) * Ccore
  have hcutG : 0 ≤ cutoffGradientConstant :=
    CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
  have hcutS : 0 ≤ cutoffSecondDerivativeConstant :=
    CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
  have hk₀ : 0 ≤ k₀ := by dsimp [k₀]; positivity
  have hk₁ : 0 ≤ k₁ := by dsimp [k₁]; positivity
  have hCacc : 0 ≤ Cacc := by dsimp [Cacc]; positivity
  have hCtail : 0 < Ctail := by dsimp [Ctail]; positivity
  have hCcore : 0 < Ccore := by dsimp [Ccore]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  exact ⟨c₀, C_G, γ, k₀, k₁, R₀, Cacc, Ctail, Ccore, C,
    hc₀, hCG, hγpos, hγlt, hγ24, hγβ,
    (by simpa only [mul_assoc] using hγabsorb), hcutG, hcutS, hk₀, hk₁,
    hCacc, hCtail, hCcore, hC⟩

private theorem gaussian_average_parameter_geometry
    (β H γ x₂ t scale ρ a r : ℝ)
    (hβ : 0 < β) (hH : 0 < H) (hβH16 : β / H < 1 / 16)
    (hγβ : γ ≤ β / (3 * H)) (hγ24 : γ ≤ 1 / 24)
    (hx₂ : 2 < x₂) (ht : 0 < t) (htγ : t < γ)
    (hscale : scale = Real.sqrt (3 * t))
    (hρ : ρ = (x₂ - 1) / scale)
    (ha : a = β * ρ ^ 2 / H)
    (hr : r = 1 / (16 * Real.sqrt a)) :
    4 < ρ ∧ 1 < a ∧ 0 ≤ ρ ∧ 0 ≤ a ∧ 0 < r ∧ r ≤ 1 / 16 ∧
      ρ * r = Real.sqrt (H / β) / 16 ∧ 0 < scale ∧
      scale ^ 2 = 3 * t ∧ scale ^ 2 ≤ 1 / 4 ∧ a = β * ρ ^ 2 / H := by
  have hβlt : β < (1 / 16 : ℝ) * H := (div_lt_iff₀ hH).mp hβH16
  have h16βH : 16 * β < H := by nlinarith only [hβlt]
  have hgeometry := buGaussian_parameter_geometry β H γ x₂ t hβ hH
    h16βH hγβ hx₂ ht htγ
  have hρlarge : 4 < ρ := by simpa [hρ, hscale, ha, hr] using hgeometry.1
  have haLarge : 1 < a := by simpa [hρ, hscale, ha, hr] using hgeometry.2.1
  have hρnonneg : 0 ≤ ρ := (by norm_num : (0 : ℝ) ≤ 4).trans hρlarge.le
  have hanonneg : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 1).trans haLarge.le
  have hrpos : 0 < r := by simpa [hρ, hscale, ha, hr] using hgeometry.2.2.1
  have hrsmall : r ≤ 1 / 16 := by
    have h := hgeometry.2.2.2.1
    rw [hr]
    exact h.le
  have hrhoR : ρ * r = Real.sqrt (H / β) / 16 := by
    simpa [hρ, hscale, ha, hr] using hgeometry.2.2.2.2
  have hscalePos : 0 < scale := by rw [hscale]; positivity
  have hscaleSq : scale ^ 2 = 3 * t := by rw [hscale]; exact Real.sq_sqrt (by positivity)
  have hscaleSqLe : scale ^ 2 ≤ 1 / 4 := by
    rw [hscaleSq]
    have htγ' := mul_le_mul_of_nonneg_left (le_of_lt htγ) (by norm_num : (0 : ℝ) ≤ 3)
    have hγ' : 3 * γ ≤ 1 / 8 := by nlinarith only [hγ24]
    linarith only [htγ', hγ']
  exact ⟨hρlarge, haLarge, hρnonneg, hanonneg, hrpos, hrsmall,
    hrhoR, hscalePos, hscaleSq, hscaleSqLe, ha⟩

private theorem gaussian_average_integrated_tail_core_stage
    {K S₁ Sinit Shell Late Initial : Set ParabolicPoint}
    (A barA β ρ a scale Tbound ε δ Wmax c₀ C_G c₁ t γ cutG cutS r R₀
      k₀ k₁ Cacc shell0 shell1 : ℝ) (x : Vec3)
    (v : ParabolicPoint → Vec3) (Dv : ParabolicPoint → Fin 3 → Vec3)
    (W Vsrc Gsrc carEnergy heatEnergy shell late initial shellMass shellGrad
      lateMass initialMass radialMass : ParabolicPoint → ℝ)
    (hWEq : W = ucGaussianWeight a)
    (hVsrcEq : Vsrc = fun z => vec3EuclideanNorm (v z) ^ 2)
    (hGsrcEq : Gsrc = fun z => spatialGradientSq v Dv z)
    (hShellMassEq : shellMass = Shell.indicator (fun z => W z * Vsrc z))
    (hShellGradEq : shellGrad = Shell.indicator (fun z => W z * Gsrc z))
    (hLateMassDefEq : lateMass = Late.indicator (fun z => W z * Vsrc z))
    (hInitialMassEq : initialMass = Initial.indicator (fun z => W z * Vsrc z))
    (hA : 0 ≤ A) (hAmax : A ≤ 1 / (10 : ℝ) ^ 12)
    (hAbar : A ≤ barA) (hρlarge : 4 < ρ) (ha : 1 < a)
    (hscale : 0 ≤ scale) (hscaleSq : scale ^ 2 = 3 * t)
    (hscaleSqLe : scale ^ 2 ≤ 1 / 4)
    (haeq : a = β * ρ ^ 2 / buGaussianH) (hr : r = 1 / (16 * Real.sqrt a))
    (hρr : ρ * r = R₀) (hc₀ : 0 ≤ c₀) (hCG : C_G = 72 * c₀)
    (hc₁ : 0 < c₁) (htγ : t < γ) (hγabsorb : 3 * C_G * c₁ ^ 2 * γ ≤ 1 / 2)
    (hcutG : 0 ≤ cutG) (hcutS : 0 ≤ cutS)
    (hk₀ : 0 ≤ k₀) (hk₁ : 0 ≤ k₁) (hCacc : 0 ≤ Cacc)
    (hρnonneg : 0 ≤ ρ) (hanonneg : 0 ≤ a)
    (hShellMeas : MeasurableSet Shell) (hLateMeas : MeasurableSet Late)
    (hInitialMeas : MeasurableSet Initial)
    (hWsrcMass : Integrable (fun z => W z * Vsrc z) (volume.restrict K))
    (hWsrcGrad : Integrable (fun z => W z * Gsrc z) (volume.restrict K))
    (hWsrcMassNonneg : 0 ≤ᵐ[volume.restrict K] (fun z => W z * Vsrc z))
    (hWsrcGradNonneg : 0 ≤ᵐ[volume.restrict K] (fun z => W z * Gsrc z))
    (hcarEnergyInt : Integrable carEnergy (volume.restrict K))
    (hcarHeatInt : Integrable heatEnergy (volume.restrict K))
    (hcarEnergyNonneg : 0 ≤ᵐ[volume.restrict K] carEnergy)
    (hErrorPoint : ∀ᵐ z ∂(volume.restrict K),
      heatEnergy z ≤ 72 * (c₁ * scale) ^ 2 * carEnergy z +
        4 * W z * (shell z ^ 2 + late z ^ 2 + initial z ^ 2))
    (hWnonneg : ∀ᵐ z ∂(volume.restrict K), 0 ≤ W z)
    (hShellFormula : ∀ z, shell z =
      if z ∈ Shell then shell0 * Real.sqrt (Vsrc z) +
        shell1 * Real.sqrt (Gsrc z) else 0)
    (hLateFormula : ∀ z, late z =
      if z ∈ Late then 32 * Real.sqrt (Vsrc z) else 0)
    (hInitialFormula : ∀ z, initial z =
      if z ∈ Initial then (8 / ε) * Real.sqrt (Vsrc z) else 0)
    (hcarlemanK : (∫ z in K, carEnergy z) ≤ c₀ * (∫ z in K, heatEnergy z))
    (hBfinite : volume (vec3Ball 0 ρ) < ⊤) (hKmeas : MeasurableSet K)
    (hKsubS₁ : K ⊆ S₁) (hKlate : ∀ z ∈ K, z.2 ≤ 23 / 12)
    (hWsrcGradS₁ : Integrable (fun z => W z * Gsrc z) (volume.restrict S₁))
    (hWmeasS₁ : AEStronglyMeasurable W (volume.restrict S₁))
    (hWboundS₁ : ∀ᵐ z ∂(volume.restrict S₁), ‖W z‖ ≤ Wmax)
    (hShellGrad :
      (∫ z in spaceTimeSet
        {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
          vec3EuclideanNorm y ≤ 3 * ρ / 4} (Ioo (1 / 6) (23 / 12)),
        W z * Gsrc z) ≤
        (Real.exp (2 * (56 * a * (2 * r) ^ 2 + 12 * ρ * (2 * r) +
          36 * ρ ^ 2 * (2 * r) ^ 2)) *
          (256 * (1 + (c₁ * scale) ^ 2 + 1 / ((2 * r) / 2) ^ 2))) *
        (8 * Besicovitch.multiplicity BUGaussianSpace ^ 2 : ℝ) *
        (∫ z in S₁, radialMass z))
    (hTboundEq : Tbound = Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
      Real.exp (-2 * β * ρ ^ 2)) (hTboundNonneg : 0 ≤ Tbound)
    (hLateTime : ∀ z ∈ K, z ∈ Late → 3 / 2 ≤ z.2)
    (hgrowth : ∀ z ∈ S₁,
      vec3EuclideanNorm (v z) ≤
        Real.exp (2 * A * vec3EuclideanNorm x ^ 2 +
          2 * A * scale ^ 2 * vec3EuclideanNorm z.1 ^ 2))
    (hInitialIntegral : (∫ z in K, initialMass z) ≤
      Wmax * (∫ z in Sinit, Vsrc z))
    (hInitialTrace : (∫ z in Sinit, Vsrc z) / ε ^ 2 < δ)
    (hε : 0 < ε) (hWmax : 0 < Wmax)
    (hShellPoint : ∀ z ∈ K, shellMass z ≤ radialMass z)
    (hRadialIntK : Integrable radialMass (volume.restrict K))
    (hRadialInt : Integrable radialMass (volume.restrict S₁))
    (hRadialNonneg : 0 ≤ᵐ[volume.restrict S₁] radialMass)
    (hRadialTail : (∫ z in S₁, radialMass z) ≤ 24 * ρ ^ 3 * Tbound) :
    ∃ Icar : ℝ, Icar = (∫ z in K, carEnergy z) ∧
      Icar ≤ 2 * c₀ * (192 * (k₀ ^ 2 + k₁ ^ 2 * Cacc) + 49153) *
        ((1 + a) * (1 + ρ) ^ 3 * Tbound) := by
  have hLateMassInt : Integrable lateMass (volume.restrict K) := by
    simpa [lateMass] using hWsrcMass.indicator hLateMeas
  have hInitialMassInt : Integrable initialMass (volume.restrict K) := by
    simpa [initialMass] using hWsrcMass.indicator hInitialMeas
  have hShellMassInt : Integrable shellMass (volume.restrict K) := by
    simpa [shellMass] using hWsrcMass.indicator hShellMeas
  have hShellGradInt : Integrable shellGrad (volume.restrict K) := by
    simpa [shellGrad] using hWsrcGrad.indicator hShellMeas
  have hAbsorption := gaussian_average_absorb_integrated_cutoff_errors
    (K := K) (Shell := Shell) (Late := Late) (Initial := Initial)
    W Vsrc Gsrc carEnergy heatEnergy shell late initial
    c₀ C_G c₁ scale t γ shell0 shell1 ε hc₀ hCG hc₁ hscaleSq htγ hγabsorb
    (ne_of_gt hε) hShellMeas hLateMeas hInitialMeas hWsrcMass hWsrcGrad
    hWsrcMassNonneg hWsrcGradNonneg hcarEnergyInt hcarHeatInt
    hcarEnergyNonneg hErrorPoint hWnonneg hShellFormula hLateFormula
    hInitialFormula hcarlemanK
  obtain ⟨Icar, Eerr, hIcarEq, hEerrEq, hCarAbsorbed⟩ := hAbsorption
  have hEerr : Eerr = 8 * shell0 ^ 2 * (∫ z in K, shellMass z) +
      8 * shell1 ^ 2 * (∫ z in K, shellGrad z) +
      4096 * (∫ z in K, lateMass z) +
      (256 / ε ^ 2) * (∫ z in K, initialMass z) := by
    rw [hShellMassEq, hShellGradEq, hLateMassDefEq, hInitialMassEq] at hEerrEq
    exact hEerrEq
  have hShellMassNonneg : 0 ≤ ∫ z in K, shellMass z := by
    simpa only [shellMass] using
      buGaussian_indicator_integral_nonneg K Shell
        (fun z => W z * Vsrc z) hWsrcMassNonneg
  have hShellGradNonneg : 0 ≤ ∫ z in K, shellGrad z := by
    simpa only [shellGrad] using
      buGaussian_indicator_integral_nonneg K Shell
        (fun z => W z * Gsrc z) hWsrcGradNonneg
  have hWsrcGradS₁' := hWsrcGradS₁
  have hShellGradUpper : (∫ z in K, shellGrad z) ≤
      (Real.exp (2 * (56 * a * (2 * r) ^ 2 + 12 * ρ * (2 * r) +
        36 * ρ ^ 2 * (2 * r) ^ 2)) *
        (256 * (1 + (c₁ * scale) ^ 2 + 1 / ((2 * r) / 2) ^ 2))) *
        (8 * Besicovitch.multiplicity BUGaussianSpace ^ 2 : ℝ) *
        (∫ z in S₁, radialMass z) := by
    have hShellGrad' := gaussian_average_shell_gradient_tail_bound
      hρlarge ha hKsubS₁ hKlate v Dv hWsrcGradS₁' hShellGrad
    simpa [hShellGradEq, S₁, hWEq, hGsrcEq] using hShellGrad'
  have hLateMassEq (z : ParabolicPoint) : lateMass z =
      if z ∈ Late then W z * vec3EuclideanNorm (v z) ^ 2 else 0 := by
    by_cases hz : z ∈ Late <;> simp [hLateMassDefEq, hWEq, hVsrcEq, hz]
  have hTailErrors := gaussian_average_late_initial_shell_tail_stage
    (K := K) (S₁ := S₁) (Sinit := Sinit) (Late := Late)
    (lateMass := lateMass) (initialMass := initialMass)
    (shellMass := shellMass) (radialMass := radialMass) (Vsrc := Vsrc)
    A barA β ρ a scale Tbound ε δ Wmax x v hKmeas hKsubS₁ hBfinite
    hρlarge hTboundEq hTboundNonneg hA hAmax hAbar hscaleSqLe haeq
    hLateTime hgrowth hLateMassEq hLateMassInt hInitialMassInt
    hInitialIntegral hInitialTrace hε hWmax hShellMassInt hRadialIntK
    hShellPoint hRadialInt hRadialNonneg hRadialTail
  exact gaussian_average_core_error_stage
    c₀ cutG cutS c₁ scale ρ a r R₀ k₀ k₁ Cacc Icar Eerr shell0 shell1
    (∫ z in K, shellMass z) (∫ z in K, shellGrad z)
    (∫ z in K, lateMass z) ((256 / ε ^ 2) * (∫ z in K, initialMass z))
    (∫ z in S₁, radialMass z) Tbound
    hc₀ hcutG hcutS hc₁ hscale hscaleSqLe hρlarge ha hr hρr
    hk₀ hk₁ hCacc hTboundNonneg hρnonneg hanonneg hCarAbsorbed hEerr
    hShellMassNonneg hShellGradNonneg hTailErrors.2.2 hShellGradUpper
    (integral_nonneg_of_ae hRadialNonneg) hRadialTail
    hTailErrors.1 hTailErrors.2.1
  |> fun hBound => ⟨Icar, hIcarEq, hBound⟩

/-- Gaussian decay of the normalized space-time averages in `lem:bu-gaussian`. -/
theorem bu_gaussian_average_uniform (c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 / 12 ∧
      ∀ A : ℝ, 0 ≤ A → A ≤ 1 / (10 : ℝ) ^ 12 →
      ∃ C : ℝ, 0 < C ∧
        ∀ (w : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
          (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (Dtw : ParabolicPoint → Vec3),
          ContinuousOn w (buHalfSpace ×ˢ Ico 0 1) →
          (∀ x : Vec3, 0 < x 2 → w (x, 0) = 0) →
          HasSpaceTimeWeakDerivs buHalfSpace (Ioo 0 1) w Dw D2w Dtw →
          (∀ S : Set ParabolicPoint, S ⊆ buHalfCylinder → Bornology.IsBounded S →
            (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) +
              ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) →
          (∀ᵐ z ∂(volume.restrict buHalfCylinder),
            vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
              c₁ * (Real.sqrt (spatialGradientSq w Dw z) + vec3EuclideanNorm (w z))) →
          (∀ z ∈ buHalfCylinder,
            vec3EuclideanNorm (w z) ≤ Real.exp (A * vec3EuclideanNorm z.1 ^ 2)) →
          ∀ x : Vec3, 2 < x 2 → ∀ t : ℝ, 0 < t → t < γ →
            t ^ (-(5 / 2 : ℝ)) *
                ∫ z in spaceTimeSet (Metric.ball x (Real.sqrt (3 * t)))
                  (Ioo t (5 * t / 2)), vec3EuclideanNorm (w z) ^ 2 ≤
              C * Real.exp (8 * max A (1 / (10 : ℝ) ^ 12 / 2) *
                vec3EuclideanNorm x ^ 2) *
                Real.exp (-((1 / (10 : ℝ) ^ 6) * x 2 ^ 2) / (12 * t)) := by
  obtain ⟨hβ, hβsmall, hH, hβH⟩ := buGaussian_source_weight_parameters
  let parameters := gaussian_average_constants c₁ hc₁ hβ hH
  let c₀ := parameters.c₀
  let C_G := parameters.C_G
  let γ := parameters.γ
  let k₀ := parameters.k₀
  let k₁ := parameters.k₁
  let R₀ := parameters.R₀
  let Cacc := parameters.Cacc
  let Ctail := parameters.Ctail
  let Ccore := parameters.Ccore
  let C := parameters.C
  have hc₀ := parameters.hc₀
  have hγpos := parameters.hγpos
  have hγlt := parameters.hγlt
  have hγ24 := parameters.hγ24
  have hγβ := parameters.hγβ
  have hγabsorb := parameters.hγabsorb
  have hcutG := parameters.hcutG
  have hcutS := parameters.hcutS
  have hk₀ := parameters.hk₀
  have hk₁ := parameters.hk₁
  have hCacc := parameters.hCacc
  have hCtail := parameters.hCtail
  have hCcore := parameters.hCcore
  have hC := parameters.hC
  refine ⟨γ, hγpos, hγlt, ?_⟩
  intro A hA hAmax
  let barA : ℝ := max A (1 / (10 : ℝ) ^ 12 / 2)
  have hAbar : A ≤ barA := le_max_left _ _
  refine ⟨C, hC, ?_⟩
  intro w Dw D2w Dtw hcont hzero hderiv hL2 hineq hgrowth x hx₂ t ht htγ
  let scale : ℝ := Real.sqrt (3 * t)
  let ρ : ℝ := (x 2 - 1) / scale
  let a : ℝ := buGaussianBeta * ρ ^ 2 / buGaussianH
  let r : ℝ := 1 / (16 * Real.sqrt a)
  let σ : ℝ := (1 / 6 : ℝ)
  have hγ12 : γ ≤ 1 / 12 := by linarith only [hγ24]
  have hβH16 : buGaussianBeta / buGaussianH < 1 / 16 :=
    lt_trans hβH (by norm_num)
  rcases gaussian_average_parameter_geometry
      buGaussianBeta buGaussianH γ (x 2) t scale ρ a r hβ hH hβH16 hγβ hγ24
      hx₂ ht htγ rfl rfl rfl rfl with
    ⟨hρlarge, ha, hρnonneg, hanonneg, hrpos, hrsmall, hrhoR, hscalePos,
      hscaleSq, hscaleSqLe, haeq⟩
  have hdataRaw := buGaussian_rescaled_data c₁ A hc₁ w Dw D2w Dtw
    hcont hzero hderiv hL2 hineq hgrowth x t γ hx₂ ht hγ12 htγ
  have hdataShift := buGaussian_shifted_rescaled_data c₁ A hc₁ hA
    w Dw D2w Dtw hcont hzero hderiv hL2 hineq hgrowth
    x t γ hx₂ ht hγ12 htγ
  dsimp [scale, ρ, σ] at hdataRaw hdataShift
  rcases hdataRaw with ⟨hweakRaw, hL2Raw, hcontRaw, hzeroRaw, hineqRaw⟩
  rcases hdataShift with
    ⟨hweakShift, hL2Shift, hineqShift, hcontShift, hzeroShift, hgrowthShift⟩
  let B : Set Vec3 := vec3Ball 0 ρ
  let S₁ : Set ParabolicPoint := spaceTimeSet B (Ioo σ 2)
  let u := ucScaledField x scale w
  let Du := ucScaledDw x scale Dw
  let D2u := ucScaledD2w x scale D2w
  let Dtu := ucScaledDtw x scale Dtw
  let v := buGaussianShiftedField σ u
  let Dv := buGaussianShiftedDw σ Du
  let Wmax : ℝ := ((1 / 6 : ℝ) * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a)
  let δinit : ℝ := Real.exp (-2 * buGaussianBeta * ρ ^ 2) /
    (256 * Wmax)
  have hWmax : 0 < Wmax := by dsimp [Wmax]; positivity
  have hδinit : 0 < δinit := by dsimp [δinit]; positivity
  rcases gaussian_average_prepare_cutoff_carleman
      (ρ := ρ) (δ := δinit) (scale := scale)
      (by linarith only [hρlarge]) hδinit hρlarge c₁ a c₀ ha u Du D2u Dtu
      hcontRaw hzeroRaw hweakRaw hL2Raw hineqRaw hweakShift hL2Shift with
    ⟨hweak₀, hBfinite, ε, hε, hεle, htraceε, cutoffSupport, hcarStageFn⟩
  have hcarStage := hcarStageFn hε hεle
  let κ := cutoffSupport.κ
  let K := cutoffSupport.K
  have hKsubS₁ := cutoffSupport.hKsubS₁
  have hKmeas := cutoffSupport.hKmeas
  have hKlate := cutoffSupport.hKlate

  let cut : ParabolicPoint → Vec3 :=
    buGaussianShiftedCutoffField ρ (by linarith only [hρlarge]) ε u
  let cutDw : ParabolicPoint → Fin 3 → Vec3 :=
    buGaussianShiftedCutoffDw ρ (by linarith only [hρlarge]) ε u Du
  let cutD2 : ParabolicPoint → Fin 3 → Fin 3 → Vec3 :=
    buGaussianShiftedCutoffD2w ρ (by linarith only [hρlarge]) ε u Du D2u
  let cutDt : ParabolicPoint → Vec3 :=
    buGaussianShiftedCutoffDtw ρ (by linarith only [hρlarge]) ε u Dtu
  let Vsrc : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (v z) ^ 2
  let Gsrc : ParabolicPoint → ℝ := fun z => spatialGradientSq v Dv z
  let W : ParabolicPoint → ℝ := ucGaussianWeight a
  let carMass : ParabolicPoint → ℝ := fun z =>
    vec3EuclideanNorm (cut z) ^ 2
  let carEnergy : ParabolicPoint → ℝ := fun z =>
    W z * (a / z.2 * carMass z + spatialGradientSq cut cutDw z)
  let heatEnergy : ParabolicPoint → ℝ := fun z =>
    W z * vec3EuclideanNorm (ucWeakHeatVector cutD2 cutDt z) ^ 2
  rcases hcarStage with
    ⟨⟨hsrcMassS₁, hsrcGradS₁⟩, hsrcMassK, hsrcGradK, hWmeas, hWbound,
      hcarEnergyInt, hcarHeatInt, hcarMassLower, hcarlemanK,
      hcarEnergyNonneg⟩
  have hsrcEnergy := (hsrcMassS₁, hsrcGradS₁)

  let Shell : Set ParabolicPoint := {z | 13 * ρ / 20 ≤
    vec3EuclideanNorm z.1 ∧ vec3EuclideanNorm z.1 ≤ 3 * ρ / 4}
  let rawTime : ParabolicPoint → ℝ := fun z =>
    ((buGaussianTimeShiftPoint σ).symm z).2
  let Late : Set ParabolicPoint := {z | 3 / 2 ≤ rawTime z ∧ rawTime z ≤ 7 / 4}
  let Initial : Set ParabolicPoint := {z | ε ≤ rawTime z ∧ rawTime z ≤ 2 * ε}
  let shell0 : ℝ := 32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) +
    3 * c₁ * scale * (cutoffGradientConstant / ρ)
  let shell1 : ℝ := 18 * (cutoffGradientConstant / ρ)
  let shell : ParabolicPoint → ℝ := fun z =>
    if z ∈ Shell then shell0 * vec3EuclideanNorm (v z) +
      shell1 * Real.sqrt (Gsrc z) else 0
  let late : ParabolicPoint → ℝ := fun z =>
    if z ∈ Late then 32 * vec3EuclideanNorm (v z) else 0
  let initial : ParabolicPoint → ℝ := fun z =>
    if z ∈ Initial then (8 / ε) * vec3EuclideanNorm (v z) else 0
  let shellMass : ParabolicPoint → ℝ :=
    Shell.indicator (fun z => W z * Vsrc z)
  let shellGrad : ParabolicPoint → ℝ :=
    Shell.indicator (fun z => W z * Gsrc z)
  let lateMass : ParabolicPoint → ℝ :=
    Late.indicator (fun z => W z * Vsrc z)
  let initialMass : ParabolicPoint → ℝ :=
    Initial.indicator (fun z => W z * Vsrc z)
  have hErrorRegions := gaussian_average_error_regions_measurable ρ σ ε
  have hShellMeas : MeasurableSet Shell := hErrorRegions.1
  have hLateMeas : MeasurableSet Late := hErrorRegions.2.2.1
  have hInitialMeas : MeasurableSet Initial := hErrorRegions.2.2.2
  have hWeightedSourceData := gaussian_average_weighted_source_error_data
    (ρ := ρ) (ε := ε) (δ := δinit) (a := a) (v := v) (Dv := Dv)
    (W := W) (Vsrc := Vsrc) (Gsrc := Gsrc) (shellMass := shellMass)
    (K := K) (S₁ := S₁) (Shell := Shell) (Initial := Initial)
    (B := B) hρlarge ha hε hεle hKmeas hKsubS₁
    (vec3Ball_measurable 0 ρ)
    (by simpa [v, buGaussianShiftedField, σ] using htraceε)
    hsrcMassK hsrcGradK hsrcMassS₁ hWmeas hWbound rfl
  rcases hWeightedSourceData with
    ⟨hWsrcMass, hWsrcGrad, hWsrcMassNonneg, hWsrcGradNonneg,
      hS₁meas, hWmeasS₁, hWboundS₁, hWsrcMassS₁, hInitialMassInt,
      hInitialIntegral, hInitialTraceIntegral, hRadialInt, hRadialNonneg,
      hRadialIntK, hShellMassPoint⟩
  have hRadialTail := buGaussian_radial_mass_tail_bound
    hρlarge haeq hA hAmax hAbar hscaleSqLe hweakShift hL2Shift hgrowthShift
  have hShellGrad := buGaussian_transition_shell_gradient_caccioppoli
    hρlarge (by linarith only [ha] : 0 < a) hrpos hrsmall
    (mul_nonneg hc₁.le hscalePos.le)
    hweakShift hcontShift hL2Shift hineqShift
  rcases gaussian_average_weighted_operator_error_point
      (by linarith only [hρlarge]) hε
      (by nlinarith only [hεle]) hc₁.le hscalePos.le ha
      u Du D2u Dtu hineqRaw hKsubS₁ hKmeas with
    ⟨hErrorPoint, hWnonneg, hShellFormula, hLateFormula, hInitialFormula⟩

  let Tbound : ℝ := Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
    Real.exp (-2 * buGaussianBeta * ρ ^ 2)
  have hTboundNonneg : 0 ≤ Tbound := by dsimp [Tbound]; positivity
  have hLateTime : ∀ z ∈ K, z ∈ Late → 3 / 2 ≤ z.2 := by
    intro z hzK hzLate
    have hraw := hzLate.1
    rw [show rawTime z = z.2 - σ by
      dsimp [rawTime]
      rw [buGaussian_timeShift_point_symm_apply]] at hraw
    dsimp [σ] at hraw
    linarith only [hraw]
  obtain ⟨Icar, hIcarEq, hCoreBound⟩ :=
    gaussian_average_integrated_tail_core_stage
      A barA buGaussianBeta ρ a scale Tbound ε δinit Wmax c₀ C_G c₁ t γ
      cutoffGradientConstant cutoffSecondDerivativeConstant r R₀ k₀ k₁ Cacc
      x v Dv W Vsrc Gsrc carEnergy heatEnergy shell late initial shellMass
      shellGrad lateMass initialMass (buGaussianRadialWeightedMass ρ a v)
      rfl rfl rfl rfl rfl rfl rfl
      hA hAmax hAbar hρlarge ha hscalePos.le hscaleSq hscaleSqLe haeq rfl
      hrhoR hc₀.le (by dsimp [C_G]; ring) hc₁ htγ hγabsorb
      hcutG hcutS hk₀ hk₁ hCacc hρnonneg hanonneg
      hShellMeas hLateMeas hInitialMeas hWsrcMass hWsrcGrad
      hWsrcMassNonneg hWsrcGradNonneg hcarEnergyInt hcarHeatInt
      hcarEnergyNonneg hErrorPoint hWnonneg hShellFormula hLateFormula
      hInitialFormula hcarlemanK hBfinite hKmeas hKsubS₁ hKlate
      (hsrcEnergy.2.bdd_mul hWmeasS₁ hWboundS₁)
      hWmeasS₁ hWboundS₁ hShellGrad (by rfl) hTboundNonneg
      hLateTime hgrowthShift hInitialIntegral hInitialTraceIntegral hε hWmax
      hShellMassPoint hRadialIntK hRadialInt hRadialNonneg hRadialTail


  have hFinal := buGaussian_physical_average_of_core
    buGaussianBeta buGaussianH c₀
    (192 * (k₀ ^ 2 + k₁ ^ 2 * Cacc) + 49153)
    Ctail Ccore k₀ k₁ Cacc x t ρ a barA Icar w
    hβ hH ht hx₂ hρlarge rfl haeq rfl rfl hc₀.le rfl hCacc
    (buGaussian_metric_average_integrable_at_small_time
      A w Dw D2w Dtw hderiv hL2 hgrowth x t hx₂ ht
      (le_of_lt htγ |>.trans hγ24))
    hcarMassLower
    hCoreBound
  simpa only [Real.rpow_eq_pow, C, barA, buGaussianBeta] using hFinal

end ESS
