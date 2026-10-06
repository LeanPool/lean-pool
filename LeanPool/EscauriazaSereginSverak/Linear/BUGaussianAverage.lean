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
  have hCtail : 0 < Ctail := by
    dsimp [Ctail]
    positivity
  have hCcore : 0 < Ccore := by
    dsimp [Ccore]
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨γ, hγpos, hγlt, ?_⟩
  intro A hA hAmax
  let barA : ℝ := max A (1 / (10 : ℝ) ^ 12 / 2)
  have hAbar : A ≤ barA := le_max_left _ _
  have hbarAnonneg : 0 ≤ barA := by
    dsimp [barA]
    positivity
  have hAbarSmall : barA ≤ 1 / (10 : ℝ) ^ 12 := by
    dsimp [barA]
    exact max_le hAmax (by norm_num)
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
  have hβlt : buGaussianBeta < (1 / 16 : ℝ) * buGaussianH :=
    (div_lt_iff₀ hH).mp hβH16
  have h16βH : 16 * buGaussianBeta < buGaussianH := by nlinarith only [hβlt]
  have hgeometry := buGaussian_parameter_geometry
    buGaussianBeta buGaussianH γ (x 2) t hβ hH
    h16βH
    hγβ hx₂ ht htγ
  have hρlarge : 4 < ρ := by simpa [ρ, scale, a, r] using hgeometry.1
  have ha : 1 < a := by simpa [ρ, scale, a, r] using hgeometry.2.1
  have hρnonneg : 0 ≤ ρ := (by norm_num : (0 : ℝ) ≤ 4).trans hρlarge.le
  have hanonneg : 0 ≤ a := (by norm_num : (0 : ℝ) ≤ 1).trans ha.le
  have hrpos : 0 < r := by simpa [ρ, scale, a, r] using hgeometry.2.2.1
  have hrsmall : r ≤ 1 / 16 := by
    have h := hgeometry.2.2.2.1
    dsimp [r]
    exact h.le
  have hrhoR : ρ * r = Real.sqrt (buGaussianH / buGaussianBeta) / 16 := by
    simpa [ρ, scale, a, r] using hgeometry.2.2.2.2
  have hscalePos : 0 < scale := by dsimp [scale]; positivity
  have hscaleSq : scale ^ 2 = 3 * t := by
    dsimp [scale]
    exact Real.sq_sqrt (by positivity)
  have hscaleSqLe : scale ^ 2 ≤ 1 / 4 := by
    rw [hscaleSq]
    have htγ' := mul_le_mul_of_nonneg_left (le_of_lt htγ) (by norm_num : (0 : ℝ) ≤ 3)
    have hγ' : 3 * γ ≤ 1 / 8 := by nlinarith only [hγ24]
    linarith only [htγ', hγ']
  have haeq : a = buGaussianBeta * ρ ^ 2 / buGaussianH := by rfl
  have hscaleNonneg : 0 ≤ scale := hscalePos.le
  have hγβPositive : γ ≤ buGaussianBeta / (3 * buGaussianH) := hγβ
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
  let I₀ : Set ℝ := Ioo 0 (2 - σ)
  let S₀ : Set ParabolicPoint := spaceTimeSet B I₀
  let S₁ : Set ParabolicPoint := spaceTimeSet B (Ioo σ 2)
  let Q₀ : Set ParabolicPoint :=
    spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2 : ℝ) 1)
  let U₀ : Set ParabolicPoint := spaceTimeSet univ (Ioo 0 2)
  let u := ucScaledField x scale w
  let Du := ucScaledDw x scale Dw
  let D2u := ucScaledD2w x scale D2w
  let Dtu := ucScaledDtw x scale Dtw
  let v := buGaussianShiftedField σ u
  let Dv := buGaussianShiftedDw σ Du
  let D2v := buGaussianShiftedD2w σ D2u
  let Dtv := buGaussianShiftedDtw σ Dtu
  have hI₀sub : I₀ ⊆ Ioo 0 2 := by
    intro s hs
    exact ⟨hs.1, lt_of_lt_of_le hs.2 (by norm_num [I₀, σ])⟩
  have hcontRaw' : ContinuousOn u (B ×ˢ Ioo 0 2) := by
    apply hcontRaw.mono
    intro z hz
    exact ⟨hz.1, ⟨hz.2.1.le, hz.2.2⟩⟩
  have hrestricted := uc_restrict_data (c₁ * scale) B B I₀ (Ioo 0 2)
    u Du D2u Dtu (isOpen_vec3Ball 0 ρ) isOpen_Ioo subset_rfl hI₀sub
    hcontRaw' hweakRaw hL2Raw hineqRaw
  have hweak₀ : HasSpaceTimeWeakDerivs B I₀ u Du D2u Dtu := hrestricted.2.1
  have hL2₀ : (∫⁻ z in S₀,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) +
        ‖D2u z‖ₑ ^ (2 : ℝ) + ‖Dtu z‖ₑ ^ (2 : ℝ)) < ⊤ := hrestricted.2.2.1
  have hBopen : IsOpen B := by dsimp [B]; exact isOpen_vec3Ball 0 ρ
  have hBmeas : MeasurableSet B := hBopen.measurableSet
  have hBfinite : volume B < ⊤ := by
    dsimp [B]
    exact CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top
  have hcontTrace : ContinuousOn u (spaceTimeSet B (Ico 0 (2 - σ))) := by
    apply hcontRaw.mono
    intro z hz
    change z.1 ∈ B ∧ z.2 ∈ Ico 0 (2 - σ) at hz
    change z.1 ∈ vec3Ball 0 ((x 2 - 1) / scale) ∧ z.2 ∈ Ico 0 2
    exact ⟨hz.1, ⟨hz.2.1, lt_of_lt_of_le hz.2.2 (by norm_num [σ])⟩⟩
  have htraceRaw := buGaussian_initial_trace_strip_tendsto_zero
    hBopen hBfinite (by norm_num [σ] : (0 : ℝ) < 2 - σ)
    hcontTrace hzeroRaw hweak₀ hL2₀
  have htraceShift := buGaussian_shifted_trace_strip_tendsto
    (σ := σ) hBmeas u htraceRaw
  let Wmax : ℝ := ((1 / 6 : ℝ) * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a)
  let δinit : ℝ := Real.exp (-2 * buGaussianBeta * ρ ^ 2) /
    (256 * Wmax)
  have hWmax : 0 < Wmax := by dsimp [Wmax]; positivity
  have hδinit : 0 < δinit := by dsimp [δinit]; positivity
  have htraceSmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      (∫ z in spaceTimeSet B (Ioc (σ + ε) (σ + 2 * ε)),
        vec3EuclideanNorm (u ((buGaussianTimeShiftPoint σ).symm z)) ^ 2) /
          ε ^ 2 < δinit := by
    filter_upwards [htraceShift.eventually
      (Metric.ball_mem_nhds 0 hδinit)] with ε hε
    have hmassNonneg : 0 ≤
        ∫ z in spaceTimeSet B (Ioc (σ + ε) (σ + 2 * ε)),
          vec3EuclideanNorm (u ((buGaussianTimeShiftPoint σ).symm z)) ^ 2 :=
      setIntegral_nonneg_of_ae
        (Filter.Eventually.of_forall (fun z => sq_nonneg _))
    have hratioNonneg : 0 ≤
        (∫ z in spaceTimeSet B (Ioc (σ + ε) (σ + 2 * ε)),
          vec3EuclideanNorm (u ((buGaussianTimeShiftPoint σ).symm z)) ^ 2) /
            ε ^ 2 := div_nonneg hmassNonneg (sq_nonneg ε)
    have hdist : dist
        ((∫ z in spaceTimeSet B (Ioc (σ + ε) (σ + 2 * ε)),
          vec3EuclideanNorm (u ((buGaussianTimeShiftPoint σ).symm z)) ^ 2) /
            ε ^ 2) 0 < δinit := by simpa only [Metric.mem_ball] using hε
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hratioNonneg] using hdist
  have hεsmallEvent : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 / 12 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 12))
  have hεposEvent : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  rcases (htraceSmall.and hεsmallEvent |>.and hεposEvent).exists with
    ⟨ε, hεdata⟩
  rcases hεdata with ⟨⟨htraceε, hεsmall⟩, hε⟩
  have hεle : ε ≤ 1 / 12 := hεsmall.le
  let κ : Vec3 × ℝ → ℝ := fun q =>
    ucCutoffScalar (ucSpatialCutoff ρ (by linarith only [hρlarge]))
      (fun s => ucFinalTimeCutoff (s - 1 / 6))
      (fun s => ucInitialTimeCutoff ε (s - 1 / 6)) q
  let K : Set ParabolicPoint := buCutSupportSet κ
  have hcutAdmissible := buGaussian_shifted_cutoff_admissible
    (by linarith only [hρlarge] : 0 < ρ) hε hweak₀ hL2Shift
  rcases hcutAdmissible with
    ⟨hweakCut, hcompactCut, htsCut, hmemCut, hmemDwCut, hmemD2Cut, hmemDtCut⟩
  have hzeroLate := buGaussian_shifted_cutoff_data_zero_late (ε := ε)
    (by linarith only [hρlarge] : 0 < ρ) u Du D2u Dtu
  rcases hzeroLate with ⟨hcutZero, hKlate⟩
  have hcutScalarComp :
      (fun z : ParabolicPoint => κ (parabolicHomeomorph z)) =
        buGaussianShiftedCutoff ρ (by linarith only [hρlarge]) ε := by
    funext z
    change ucCutoffScalar (ucSpatialCutoff ρ (by linarith only [hρlarge]))
        (fun s => ucFinalTimeCutoff (s - 1 / 6))
        (fun s => ucInitialTimeCutoff ε (s - 1 / 6)) (parabolicHomeomorph z) =
      ucGaussianCutoff ρ (by linarith only [hρlarge]) ε
        ((buGaussianTimeShiftPoint (1 / 6)).symm z)
    rw [parabolicHomeomorph_apply, buGaussian_timeShift_point_symm_apply]
    rfl
  have hKeq : K = tsupport (buGaussianShiftedCutoff ρ
      (by linarith only [hρlarge]) ε) := by
    dsimp [K, buCutSupportSet]
    rw [← hcutScalarComp]
    exact (tsupport_comp_eq_preimage κ parabolicHomeomorph).symm
  have hKsubS₁ : K ⊆ S₁ := by
    rw [hKeq]
    exact buGaussian_shiftedCutoff_tsupport_subset
      (by linarith only [hρlarge]) hε
  have hKsubU₀ : K ⊆ U₀ := by
    intro z hz
    have hz' := hKsubS₁ hz
    have hσpos : 0 < σ := by norm_num [σ]
    exact ⟨Set.mem_univ _, ⟨hσpos.trans hz'.2.1, hz'.2.2⟩⟩
  have hKmeas : MeasurableSet K := by
    dsimp [K, buCutSupportSet]
    have hclosed : IsClosed (tsupport κ) := isClosed_tsupport κ
    exact (hclosed.preimage parabolicHomeomorph.continuous).measurableSet

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
  have hQsubK : Q₀ ⊆ K := by
    rw [hKeq]
    intro z hz
    apply subset_tsupport
    have hscalar := (buGaussian_cutoff_field_eq_on_average_box
      hρlarge hε hεle u z hz).1
    have hcomp := congrFun hcutScalarComp z
    have hval : buGaussianShiftedCutoff ρ
        (by linarith only [hρlarge]) ε z = 1 := by
      change ucCutoffScalar (ucSpatialCutoff ρ (by linarith only [hρlarge]))
          (fun s => ucFinalTimeCutoff (s - 1 / 6))
          (fun s => ucInitialTimeCutoff ε (s - 1 / 6)) z = 1 at hscalar
      have hκ : κ (parabolicHomeomorph z) = 1 := by
        change ucCutoffScalar (ucSpatialCutoff ρ
            (by linarith only [hρlarge]))
          (fun s => ucFinalTimeCutoff (s - 1 / 6))
          (fun s => ucInitialTimeCutoff ε (s - 1 / 6))
          (parabolicHomeomorph z) = 1
        rw [parabolicHomeomorph_apply]
        change ucCutoffScalar (ucSpatialCutoff ρ
            (by linarith only [hρlarge]))
          (fun s => ucFinalTimeCutoff (s - 1 / 6))
          (fun s => ucInitialTimeCutoff ε (s - 1 / 6))
          (z.1, z.2) = 1 at hscalar
        exact hscalar
      exact hcomp.symm.trans hκ
    change buGaussianShiftedCutoff ρ
        (by linarith only [hρlarge]) ε z ≠ 0
    rw [hval]
    norm_num
  have hQmeas : MeasurableSet Q₀ := by
    dsimp [Q₀]
    exact (isOpen_spaceTimeSet _ _ Metric.isOpen_ball isOpen_Ioo).measurableSet
  have hQsubS₁ : Q₀ ⊆ S₁ := hQsubK.trans hKsubS₁
  have hsrcEnergy := buGaussian_local_energy_integrable hweakShift hL2Shift
  have hsrcMassQ : Integrable Vsrc (volume.restrict Q₀) := by
    exact hsrcEnergy.1.mono_measure (Measure.restrict_mono hQsubS₁ le_rfl)
  have hsrcMassK : Integrable Vsrc (volume.restrict K) := by
    exact hsrcEnergy.1.mono_measure (Measure.restrict_mono hKsubS₁ le_rfl)
  have hsrcGradK : Integrable Gsrc (volume.restrict K) := by
    exact hsrcEnergy.2.mono_measure (Measure.restrict_mono hKsubS₁ le_rfl)
  have hWmeas : AEStronglyMeasurable W (volume.restrict K) :=
    (ucGaussianWeight_measurable a).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have hWbound : ∀ᵐ z ∂(volume.restrict K),
      ‖W z‖ ≤ Wmax := by
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    have hzS := hKsubS₁ hz
    have hslo : (1 / 6 : ℝ) ≤ z.2 := hzS.2.1.le
    have hshi : z.2 ≤ 2 := hzS.2.2.le
    have hspos : 0 < z.2 := by linarith only [hslo]
    rw [Real.norm_eq_abs, abs_of_nonneg (ucGaussianWeight_nonneg a hspos)]
    exact ucGaussianWeight_le_after (by norm_num) (by linarith only [ha])
      hslo hshi
  have hcutEnergy := bu_memLp_quadratic_energy_integrable K cut cutDw
    (hmemCut.mono_measure Measure.restrict_le_self)
    (hmemDwCut.mono_measure Measure.restrict_le_self)
  have hcutHeat := bu_memLp_heat_sq_integrable K cutD2 cutDt
    (hmemD2Cut.mono_measure Measure.restrict_le_self)
    (hmemDtCut.mono_measure Measure.restrict_le_self)
  have hWcarMass : Integrable (fun z => W z * carMass z)
      (volume.restrict K) := by
    exact hcutEnergy.1.bdd_mul hWmeas hWbound
  have hWcarGrad : Integrable (fun z => W z * spatialGradientSq cut cutDw z)
      (volume.restrict K) := by
    exact hcutEnergy.2.bdd_mul hWmeas hWbound
  have hWheat : Integrable (fun z => W z *
      vec3EuclideanNorm (ucWeakHeatVector cutD2 cutDt z) ^ 2)
      (volume.restrict K) := by
    exact hcutHeat.bdd_mul hWmeas hWbound
  have hcoefMeas : AEStronglyMeasurable (fun z : ParabolicPoint => a / z.2)
      (volume.restrict K) :=
    (measurable_const.div measurable_snd).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have hcoefBound : ∀ᵐ z ∂(volume.restrict K),
      ‖a / z.2‖ ≤ 6 * a := by
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    have hzS := hKsubS₁ hz
    have hslo : (1 / 6 : ℝ) ≤ z.2 := hzS.2.1.le
    have hspos : 0 < z.2 := by linarith only [hslo]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith only [ha]) hspos.le)]
    apply (div_le_iff₀ hspos).2
    nlinarith only [ha, hslo]
  have hcoefCarMass : Integrable (fun z => W z *
      (a / z.2 * carMass z)) (volume.restrict K) := by
    have h := hWcarMass.bdd_mul hcoefMeas hcoefBound
    convert h using 1
    ext z
    ring
  have hcarEnergyInt : Integrable carEnergy (volume.restrict K) := by
    have h := hcoefCarMass.add hWcarGrad
    convert h using 1
    ext z
    simp [carEnergy]
    ring
  have hcarHeatInt : Integrable heatEnergy (volume.restrict K) := by
    simpa [heatEnergy] using hWheat
  have hcarleman0 := buGaussian_shifted_cutoff_carleman
    (by linarith only [hρlarge] : 0 < ρ) hε hweak₀ hL2Shift a
    (by linarith only [ha])
  have hcarleman : (∫ z in U₀, carEnergy z) ≤
      c₀ * ∫ z in U₀, heatEnergy z := by
    exact hcarleman0
  have hU₀meas : MeasurableSet U₀ := by
    dsimp [U₀]
    exact (isOpen_spaceTimeSet _ _ isOpen_univ isOpen_Ioo).measurableSet
  have hcarMassZero : ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      z ∈ U₀ → z ∉ K → carEnergy z = 0 := by
    filter_upwards [] with z
    intro _ hzK
    have hz := (hcutZero z hzK)
    simp [carEnergy, carMass, cut, cutDw, spatialGradientSq,
      hz.1, hz.2.1, vec3EuclideanNorm_zero]
  have hcarHeatZero : ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      z ∈ U₀ → z ∉ K → heatEnergy z = 0 := by
    filter_upwards [] with z
    intro _ hzK
    have hz := (hcutZero z hzK)
    have hheat : ucWeakHeatVector cutD2 cutDt z = 0 := by
      change (fun i => cutDt z i + ∑ j : Fin 3, cutD2 z i j j) = 0
      rw [show cutDt z = 0 from hz.2.2.2,
        show cutD2 z = 0 from hz.2.2.1]
      funext i
      simp
    simp [heatEnergy, hheat, vec3EuclideanNorm_zero]
  have hcarMassSupport := setIntegral_eq_of_zero_off
    hU₀meas hKmeas hKsubU₀ hcarMassZero
  have hcarHeatSupport := setIntegral_eq_of_zero_off
    hU₀meas hKmeas hKsubU₀ hcarHeatZero
  have hcarlemanK : (∫ z in K, carEnergy z) ≤
      c₀ * ∫ z in K, heatEnergy z := by
    simpa only [← hcarMassSupport, ← hcarHeatSupport] using hcarleman
  have hcarDensityPoint : ∀ z ∈ Q₀,
      Real.exp (-(3 / 2 : ℝ)) * Vsrc z ≤ carEnergy z := by
    intro z hz
    have hdensity := buGaussian_carleman_mass_density_lower
      hρlarge (by linarith only [ha]) hε hεle u z hz
    have hgrad : 0 ≤ spatialGradientSq cut cutDw z := by
      dsimp [spatialGradientSq]
      positivity
    have hWnonneg : 0 ≤ W z := by
      have htime : 0 < z.2 := by
        have hztime : (1 / 2 : ℝ) < z.2 := hz.2.1
        linarith only [hztime]
      exact ucGaussianWeight_nonneg a htime
    have hbase : Real.exp (-(3 / 2 : ℝ)) * Vsrc z ≤
        W z * (a / z.2 * carMass z) := by
      simpa [Vsrc, v, σ, W, a, carMass, cut, mul_assoc] using hdensity
    calc
      _ ≤ W z * (a / z.2 * carMass z) := hbase
      _ ≤ carEnergy z := by
        dsimp [carEnergy]
        apply mul_le_mul_of_nonneg_left _ hWnonneg
        exact le_add_of_nonneg_right hgrad
  have hcarDensityInt : Integrable
      (fun z => Real.exp (-(3 / 2 : ℝ)) * Vsrc z)
      (volume.restrict Q₀) := hsrcMassQ.const_mul _
  have hcarEnergyQ : Integrable carEnergy (volume.restrict Q₀) :=
    hcarEnergyInt.mono_measure (Measure.restrict_mono hQsubK le_rfl)
  have hcarDensity := setIntegral_mono_on hcarDensityInt hcarEnergyQ
    hQmeas hcarDensityPoint
  have hcarEnergyNonneg : 0 ≤ᵐ[volume.restrict K] carEnergy := by
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    have hzS := hKsubS₁ hz
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
  have hcarQtoK := setIntegral_mono_set hcarEnergyInt
    hcarEnergyNonneg (ae_of_all _ hQsubK)
  have hcarMassLower : Real.exp (-(3 / 2 : ℝ)) *
      (∫ z in Q₀, Vsrc z) ≤ ∫ z in K, carEnergy z := by
    calc
      _ = ∫ z in Q₀, Real.exp (-(3 / 2 : ℝ)) * Vsrc z := by
        rw [integral_const_mul]
      _ ≤ ∫ z in Q₀, carEnergy z := hcarDensity
      _ ≤ ∫ z in K, carEnergy z := hcarQtoK

  let Shell : Set ParabolicPoint := {z | 13 * ρ / 20 ≤
    vec3EuclideanNorm z.1 ∧ vec3EuclideanNorm z.1 ≤ 3 * ρ / 4}
  let rawTime : ParabolicPoint → ℝ := fun z =>
    ((buGaussianTimeShiftPoint σ).symm z).2
  let Late : Set ParabolicPoint := {z | 3 / 2 ≤ rawTime z ∧ rawTime z ≤ 7 / 4}
  let Initial : Set ParabolicPoint := {z | ε ≤ rawTime z ∧ rawTime z ≤ 2 * ε}
  let main : ParabolicPoint → ℝ := fun z => c₁ * scale *
    (vec3EuclideanNorm (cut z) + 3 * Real.sqrt (spatialGradientSq cut cutDw z))
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
  have hOp₀ := buGaussian_shifted_operator_localized_ae_bound
    (ρ := ρ) (ε := ε) (c₁ := c₁) (scale := scale)
    (by linarith only [hρlarge] : 0 < ρ) hε
    (by nlinarith only [hεle]) hc₁.le hscaleNonneg u Du D2u Dtu hineqRaw
  have hOpRestrict := ae_mono
    (Measure.restrict_mono hKsubS₁ le_rfl) hOp₀
  have hOpBound : ∀ᵐ z ∂(volume.restrict K),
      vec3EuclideanNorm (ucWeakHeatVector cutD2 cutDt z) ≤
        main z + shell z + late z + initial z := by
    filter_upwards [hOpRestrict] with z hz
    simpa [main, shell, late, initial, Shell, Late, Initial, rawTime,
      shell0, shell1, cut, cutDw, cutD2, cutDt, Gsrc, v, Dv, σ,
      buGaussian_timeShift_point_symm_apply] using hz
  have hShellMeas : MeasurableSet Shell := by
    dsimp [Shell]
    exact (measurableSet_le continuous_const.measurable
      (continuous_vec3EuclideanNorm.measurable.comp measurable_fst)).inter
      (measurableSet_le (continuous_vec3EuclideanNorm.measurable.comp measurable_fst)
        continuous_const.measurable)
  have hrawTimeContinuous : Continuous rawTime := by
    dsimp [rawTime]
    exact (continuous_snd.comp parabolicHomeomorph.continuous).comp
      (buGaussianTimeShiftPoint σ).symm.continuous
  have hLateMeas : MeasurableSet Late := by
    dsimp [Late]
    simpa only [Set.preimage, Set.mem_Icc] using
      measurableSet_Icc.preimage hrawTimeContinuous.measurable
  have hInitialMeas : MeasurableSet Initial := by
    dsimp [Initial]
    simpa only [Set.preimage, Set.mem_Icc] using
      (measurableSet_Icc.preimage hrawTimeContinuous.measurable)
  have hWsrcMass : Integrable (fun z => W z * Vsrc z)
      (volume.restrict K) := hsrcMassK.bdd_mul hWmeas hWbound
  have hWsrcGrad : Integrable (fun z => W z * Gsrc z)
      (volume.restrict K) := hsrcGradK.bdd_mul hWmeas hWbound
  have hWsrcMassNonneg : 0 ≤ᵐ[volume.restrict K]
      (fun z => W z * Vsrc z) := by
    filter_upwards [ae_restrict_mem hKmeas] with z hzK
    have hzS := hKsubS₁ hzK
    have hspos : 0 < z.2 := by
      have hs := hzS.2.1
      norm_num at hs ⊢
      linarith only [hs]
    exact mul_nonneg (ucGaussianWeight_nonneg a hspos) (sq_nonneg _)
  have hWsrcGradNonneg : 0 ≤ᵐ[volume.restrict K]
      (fun z => W z * Gsrc z) := by
    filter_upwards [ae_restrict_mem hKmeas] with z hzK
    have hzS := hKsubS₁ hzK
    have hspos : 0 < z.2 := by
      have hs := hzS.2.1
      norm_num at hs ⊢
      linarith only [hs]
    have hg : 0 ≤ Gsrc z := by dsimp [Gsrc, spatialGradientSq]; positivity
    exact mul_nonneg (ucGaussianWeight_nonneg a hspos) hg
  have hS₁meas : MeasurableSet S₁ := by
    exact (vec3Ball_measurable 0 ρ).prod measurableSet_Ioo
  have hWmeasS₁ : AEStronglyMeasurable W (volume.restrict S₁) :=
    (ucGaussianWeight_measurable a).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have hWboundS₁ : ∀ᵐ z ∂(volume.restrict S₁), ‖W z‖ ≤ Wmax := by
    filter_upwards [ae_restrict_mem hS₁meas] with z hz
    have hslo : (1 / 6 : ℝ) ≤ z.2 := hz.2.1.le
    have hspos : 0 < z.2 := by linarith only [hslo]
    rw [Real.norm_eq_abs, abs_of_nonneg (ucGaussianWeight_nonneg a hspos)]
    exact ucGaussianWeight_le_after (by norm_num) (by linarith only [ha])
      hslo hz.2.2.le
  have hWsrcMassS₁ : Integrable (fun z => W z * Vsrc z)
      (volume.restrict S₁) := hsrcEnergy.1.bdd_mul hWmeasS₁ hWboundS₁
  have hRadMeas : MeasurableSet {z : ParabolicPoint |
      ρ / 2 ≤ vec3EuclideanNorm z.1} :=
    measurableSet_le continuous_const.measurable
      (continuous_vec3EuclideanNorm.measurable.comp measurable_fst)
  have hRadialInt : Integrable (buGaussianRadialWeightedMass ρ a v)
      (volume.restrict S₁) := by
    have h := hWsrcMassS₁.indicator hRadMeas
    convert h using 1
    ext z
    by_cases hz : ρ / 2 ≤ vec3EuclideanNorm z.1 <;>
      simp [Set.indicator, buGaussianRadialWeightedMass, W, Vsrc, hz]
  have hRadialTail := buGaussian_radial_mass_tail_bound
    hρlarge haeq hA hAmax hAbar hscaleSqLe hweakShift hL2Shift hgrowthShift
  have hShellGrad := buGaussian_transition_shell_gradient_caccioppoli
    hρlarge (by linarith only [ha] : 0 < a) hrpos hrsmall
    (mul_nonneg hc₁.le hscaleNonneg)
    hweakShift hcontShift hL2Shift hineqShift
  have hErrorPoint : ∀ᵐ z ∂(volume.restrict K),
      heatEnergy z ≤
        72 * (c₁ * scale) ^ 2 * carEnergy z +
          4 * W z * (shell z ^ 2 + late z ^ 2 + initial z ^ 2) := by
    filter_upwards [hOpBound, ae_restrict_mem hKmeas] with z hOp hzK
    have hzS := hKsubS₁ hzK
    have hspos : 0 < z.2 := by
      have hs := hzS.2.1
      norm_num at hs ⊢
      linarith only [hs]
    have hq : (1 / 2 : ℝ) ≤ a / z.2 := by
      apply (le_div_iff₀ hspos).2
      nlinarith only [ha, hzS.2.2]
    have hm : 0 ≤ carMass z := sq_nonneg _
    have hg : 0 ≤ spatialGradientSq cut cutDw z := by
      dsimp [spatialGradientSq]
      positivity
    have hW : 0 ≤ W z := ucGaussianWeight_nonneg a hspos
    have hh : 0 ≤ vec3EuclideanNorm (ucWeakHeatVector cutD2 cutDt z) :=
      vec3EuclideanNorm_nonneg _
    have hOp' : vec3EuclideanNorm (ucWeakHeatVector cutD2 cutDt z) ≤
        c₁ * scale * (Real.sqrt (carMass z) +
          3 * Real.sqrt (spatialGradientSq cut cutDw z)) +
          shell z + late z + initial z := by
      simpa [main, carMass, Real.sqrt_sq (vec3EuclideanNorm_nonneg _)]
        using hOp
    have hpoint := buGaussian_weighted_four_error_bound
      (W := W z) (q := a / z.2) (m := carMass z)
      (g := spatialGradientSq cut cutDw z) (c := c₁ * scale)
      (b := shell z) (d := late z) (e := initial z)
      (h := vec3EuclideanNorm (ucWeakHeatVector cutD2 cutDt z))
      hW hq hm hg hh hOp'
    simpa [heatEnergy, carEnergy, carMass, main, W, mul_assoc] using hpoint

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
      8 * shell1 ^ 2 * shellGrad z +
      4096 * lateMass z +
      (256 / ε ^ 2) * initialMass z
  have hShellMassInt : Integrable shellMass (volume.restrict K) := by
    simpa [shellMass] using hWsrcMass.indicator hShellMeas
  have hShellGradInt : Integrable shellGrad (volume.restrict K) := by
    simpa [shellGrad] using hWsrcGrad.indicator hShellMeas
  have hShellMassNonneg : 0 ≤ ∫ z in K, shellMass z := by
    simpa only [shellMass] using
      buGaussian_indicator_integral_nonneg K Shell
        (fun z => W z * Vsrc z) hWsrcMassNonneg
  have hShellGradNonneg : 0 ≤ ∫ z in K, shellGrad z := by
    simpa only [shellGrad] using
      buGaussian_indicator_integral_nonneg K Shell
        (fun z => W z * Gsrc z) hWsrcGradNonneg
  have hLateMassInt : Integrable lateMass (volume.restrict K) := by
    simpa [lateMass] using hWsrcMass.indicator hLateMeas
  have hInitialMassInt : Integrable initialMass (volume.restrict K) := by
    simpa [initialMass] using hWsrcMass.indicator hInitialMeas
  have hMajorInt : Integrable major (volume.restrict K) := by
    dsimp [major]
    exact (((hcarEnergyInt.const_mul _).add
      (hShellMassInt.const_mul _)).add
      (hShellGradInt.const_mul _)).add
      (hLateMassInt.const_mul _) |>.add (hInitialMassInt.const_mul _)
  have hMajorPoint : ∀ᵐ z ∂(volume.restrict K),
      heatEnergy z ≤ major z := by
    filter_upwards [hErrorPoint, ae_restrict_mem hKmeas] with z hError hzK
    have hzS := hKsubS₁ hzK
    have hspos : 0 < z.2 := by
      have hs := hzS.2.1
      norm_num at hs ⊢
      linarith only [hs]
    have hW : 0 ≤ W z := ucGaussianWeight_nonneg a hspos
    have hV : 0 ≤ Vsrc z := sq_nonneg _
    have hG : 0 ≤ Gsrc z := by
      dsimp [Gsrc, spatialGradientSq]
      positivity
    have hShellSq : 4 * W z * shell z ^ 2 ≤
        8 * shell0 ^ 2 * shellMass z +
          8 * shell1 ^ 2 * shellGrad z := by
      by_cases hz : z ∈ Shell
      · have htwo :
            (shell0 * vec3EuclideanNorm (v z) +
              shell1 * Real.sqrt (Gsrc z)) ^ 2 ≤
            2 * shell0 ^ 2 * Vsrc z + 2 * shell1 ^ 2 * Gsrc z := by
          have hdiff := sq_nonneg
            (shell0 * vec3EuclideanNorm (v z) -
              shell1 * Real.sqrt (Gsrc z))
          have hsqrt := Real.sq_sqrt hG
          dsimp [Vsrc]
          nlinarith only [hdiff, hsqrt]
        have hmul := mul_le_mul_of_nonneg_left htwo hW
        simp [shell, shellMass, shellGrad, hz] at ⊢
        nlinarith only [hmul]
      · simp [shell, shellMass, shellGrad, hz]
    have hLateSq : 4 * W z * late z ^ 2 = 4096 * lateMass z := by
      by_cases hz : z ∈ Late <;> simp [late, lateMass, hz]; ring
    have hInitialSq : 4 * W z * initial z ^ 2 =
        (256 / ε ^ 2) * initialMass z := by
      by_cases hz : z ∈ Initial <;> simp [initial, initialMass, hz]; ring
    dsimp [major]
    nlinarith only [hError, hShellSq, hLateSq, hInitialSq]
  have hMajorIntegral : (∫ z in K, heatEnergy z) ≤
      ∫ z in K, major z :=
    integral_mono_ae hcarHeatInt hMajorInt hMajorPoint
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
  have hCarUpper : Icar ≤ c₀ * (72 * (c₁ * scale) ^ 2 * Icar + Eerr) := by
    have hbound := hcarlemanK.trans
      (mul_le_mul_of_nonneg_left hMajorIntegral hc₀.le)
    simpa only [Icar, hMajorEq] using hbound
  have hAbsorbCoeff : c₀ * 72 * (c₁ * scale) ^ 2 ≤ 1 / 2 := by
    calc
      c₀ * 72 * (c₁ * scale) ^ 2 =
          (3 * C_G * c₁ ^ 2) * t := by
        rw [mul_pow, hscaleSq]
        dsimp [C_G]
        ring
      _ ≤ (3 * C_G * c₁ ^ 2) * γ :=
        mul_le_mul_of_nonneg_left htγ.le (by positivity)
      _ ≤ 1 / 2 := by simpa only [mul_assoc] using hγabsorb
  have hIcarNonneg : 0 ≤ Icar := by
    dsimp [Icar]
    exact integral_nonneg_of_ae hcarEnergyNonneg
  have hCarAbsorbed : Icar ≤ 2 * c₀ * Eerr := by
    have hhalf := mul_le_mul_of_nonneg_right hAbsorbCoeff hIcarNonneg
    nlinarith only [hCarUpper, hhalf]
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
    change z.1 ∈ vec3Ball 0 ρ ∧ z.2 ∈ Ioo σ 2
    constructor
    · simpa only [mem_vec3Ball, sub_zero] using hnorm
    · exact ⟨by simpa only [σ] using hz.2.1,
        lt_trans hz.2.2 (by norm_num)⟩
  have hWsrcGradS₁ : Integrable (fun z => W z * Gsrc z)
      (volume.restrict S₁) := hsrcEnergy.2.bdd_mul hWmeasS₁ hWboundS₁
  have hShellSourceInt : Integrable (fun z => W z * Gsrc z)
      (volume.restrict Sshell) :=
    hWsrcGradS₁.mono_measure (Measure.restrict_mono hSshellSub le_rfl)
  have hSshellMeas : MeasurableSet Sshell := by
    have hspatial : MeasurableSet
        {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
          vec3EuclideanNorm y ≤ 3 * ρ / 4} :=
      (measurableSet_le continuous_const.measurable
        continuous_vec3EuclideanNorm.measurable).inter
      (measurableSet_le continuous_vec3EuclideanNorm.measurable
        continuous_const.measurable)
    exact hspatial.prod measurableSet_Ioo
  have hShellSourceNonneg : 0 ≤ᵐ[volume.restrict Sshell]
      (fun z => W z * Gsrc z) := by
    filter_upwards [ae_restrict_mem hSshellMeas] with z hz
    have hzS := hSshellSub hz
    have hspos : 0 < z.2 := by
      have hs := hzS.2.1
      norm_num at hs ⊢
      linarith only [hs]
    have hG : 0 ≤ Gsrc z := by dsimp [Gsrc, spatialGradientSq]; positivity
    exact mul_nonneg (ucGaussianWeight_nonneg a hspos) hG
  have hShellAE : ∀ᵐ z : ParabolicPoint ∂volume,
      z ∈ K ∩ Shell → z ∈ Sshell := by
    filter_upwards [buGaussian_ae_time_ne (23 / 12 : ℝ)] with z hne hz
    have hzS := hKsubS₁ hz.1
    have htop := hKlate z hz.1
    have htop' : z.2 < 23 / 12 := lt_of_le_of_ne htop hne
    exact ⟨hz.2, ⟨hzS.2.1, htop'⟩⟩
  have hShellGradIntegral : (∫ z in K, shellGrad z) ≤
      ∫ z in Sshell, W z * Gsrc z := by
    have hEq : (∫ z in K, shellGrad z) =
        ∫ z in K ∩ Shell, W z * Gsrc z := by
      dsimp [shellGrad]
      rw [setIntegral_indicator hShellMeas]
    rw [hEq]
    exact setIntegral_mono_set hShellSourceInt hShellSourceNonneg hShellAE
  have hShellGradUpper : (∫ z in K, shellGrad z) ≤
      (Real.exp (2 * (56 * a * (2 * r) ^ 2 + 12 * ρ * (2 * r) +
        36 * ρ ^ 2 * (2 * r) ^ 2)) *
        (256 * (1 + (c₁ * scale) ^ 2 + 1 / ((2 * r) / 2) ^ 2))) *
        (8 * Besicovitch.multiplicity BUGaussianSpace ^ 2 : ℝ) *
        (∫ z in S₁, buGaussianRadialWeightedMass ρ a v z) := by
    exact hShellGradIntegral.trans hShellGrad
  let Tbound : ℝ := Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
    Real.exp (-2 * buGaussianBeta * ρ ^ 2)
  have hTboundNonneg : 0 ≤ Tbound := by dsimp [Tbound]; positivity
  have hRadialTail' :
      (∫ z in S₁, buGaussianRadialWeightedMass ρ a v z) ≤
        24 * ρ ^ 3 * Tbound := by
    simpa only [S₁, v, u, scale, Tbound, σ, B, mul_assoc]
      using hRadialTail
  have hLatePoint (z : ParabolicPoint) (hzK : z ∈ K) :
      lateMass z ≤ Tbound := by
    by_cases hzLate : z ∈ Late
    · have hzS := hKsubS₁ hzK
      have hslow : 3 / 2 ≤ z.2 := by
        have hraw := hzLate.1
        rw [show rawTime z = z.2 - σ by
          dsimp [rawTime]
          rw [buGaussian_timeShift_point_symm_apply]] at hraw
        dsimp [σ] at hraw
        linarith only [hraw]
      have hshi : z.2 ≤ 2 := hzS.2.2.le
      have hsmall := buGaussian_source_spatial_absorption
        hA hAmax hscaleSqLe hslow hshi
      have hendpoint := buGaussian_time_weight_endpoint haeq
      have hpoint := buGaussian_omega2_pointwise_bound
        (a := a) (β := buGaussianBeta) (ρ := ρ)
        (A := A) (barA := barA) (scale := scale)
        (s := z.2) (x := x) (y := z.1)
        (by linarith only [ha] : 0 ≤ a) hA hAbar hslow hshi
        hsmall hendpoint (v z) (hgrowthShift z hzS)
      have hpoint' : W z * Vsrc z ≤ Tbound *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (8 * z.2)) := by
        simpa [W, Vsrc, Tbound, ucGaussianWeight] using hpoint
      have hspos : 0 < z.2 := by linarith only [hslow]
      have hexp : Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (8 * z.2)) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by
          have hfrac : 0 ≤ vec3EuclideanNorm z.1 ^ 2 / (8 * z.2) := by
            positivity
          simpa only [neg_div] using neg_nonpos.mpr hfrac)
      have hmul := mul_le_mul_of_nonneg_left hexp hTboundNonneg
      simpa [lateMass, hzLate] using hpoint'.trans (by simpa using hmul)
    · simpa [lateMass, hzLate] using hTboundNonneg
  have hS₁finite : volume S₁ < ⊤ := by
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
      (vec3Ball 0 ρ ×ˢ Ioo σ 2) < ⊤
    rw [Measure.prod_prod]
    have hI : volume (Ioo σ 2) < ⊤ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    exact ENNReal.mul_lt_top hBfinite hI
  have hKfinite : volume K < ⊤ :=
    (measure_mono hKsubS₁).trans_lt hS₁finite
  have hKvolume : (volume K).toReal ≤ 12 * ρ ^ 3 := by
    calc
      (volume K).toReal ≤ (volume S₁).toReal :=
        ENNReal.toReal_mono hS₁finite.ne (measure_mono hKsubS₁)
      _ ≤ 12 * ρ ^ 3 := by
        simpa only [S₁, σ, B] using
          buGaussian_local_cylinder_volume_bound
            (by linarith only [hρlarge] : 0 < ρ)
  have hLateIntegral : (∫ z in K, lateMass z) ≤
      12 * ρ ^ 3 * Tbound := by
    have hconstInt : Integrable (fun _ : ParabolicPoint => Tbound)
        (volume.restrict K) := integrableOn_const hKfinite.ne
    have hbound := setIntegral_mono_on hLateMassInt hconstInt hKmeas
      hLatePoint
    rw [setIntegral_const] at hbound
    have hvol := mul_le_mul_of_nonneg_left hKvolume hTboundNonneg
    have hbound' : (∫ z in K, lateMass z) ≤
        Tbound * (volume K).toReal := by
      simpa [Measure.real, smul_eq_mul, mul_comm] using hbound
    simpa [mul_comm] using hbound'.trans hvol
  let Sinit : Set ParabolicPoint :=
    spaceTimeSet B (Icc (σ + ε) (σ + 2 * ε))
  let SinitOpen : Set ParabolicPoint :=
    spaceTimeSet B (Ioc (σ + ε) (σ + 2 * ε))
  have hSinitMeas : MeasurableSet Sinit := hBmeas.prod measurableSet_Icc
  have hSinitSub : Sinit ⊆ S₁ := by
    intro z hz
    change z.1 ∈ B ∧ z.2 ∈ Icc (σ + ε) (σ + 2 * ε) at hz
    change z.1 ∈ B ∧ z.2 ∈ Ioo σ 2
    refine ⟨hz.1, ?_⟩
    dsimp [σ] at hz ⊢
    constructor
    · linarith only [hz.2.1, hε]
    · linarith only [hz.2.2, hεsmall]
  have hSinitInt : Integrable Vsrc (volume.restrict Sinit) :=
    hsrcEnergy.1.mono_measure (Measure.restrict_mono hSinitSub le_rfl)
  have hInitialPoint (z : ParabolicPoint) (hzK : z ∈ K) :
      initialMass z ≤ Wmax * Sinit.indicator Vsrc z := by
    by_cases hzInit : z ∈ Initial
    · have hzS := hKsubS₁ hzK
      have hzStrip : z ∈ Sinit := by
        have hraw := hzInit
        dsimp [Initial, rawTime] at hraw
        rw [buGaussian_timeShift_point_symm_apply] at hraw
        change z.1 ∈ B ∧ z.2 ∈ Icc (σ + ε) (σ + 2 * ε)
        refine ⟨hzS.1, ?_⟩
        change σ + ε ≤ z.2 ∧ z.2 ≤ σ + 2 * ε
        constructor <;> linarith only [hraw.1, hraw.2]
      have hspos : 0 < z.2 := by
        have hs := hzS.2.1
        norm_num at hs ⊢
        linarith only [hs]
      have hweight : W z ≤ Wmax := by
        exact ucGaussianWeight_le_after (by norm_num)
          (by linarith only [ha]) hzS.2.1.le hzS.2.2.le
      have hmul := mul_le_mul_of_nonneg_right hweight
        (sq_nonneg (vec3EuclideanNorm (v z)))
      simpa [initialMass, hzInit, hzStrip, Vsrc, Set.indicator] using hmul
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
    filter_upwards [buGaussian_ae_time_ne (σ + ε)] with z hne
    apply propext
    change (z.1 ∈ B ∧ z.2 ∈ Icc (σ + ε) (σ + 2 * ε)) ↔
      (z.1 ∈ B ∧ z.2 ∈ Ioc (σ + ε) (σ + 2 * ε))
    constructor
    · rintro ⟨hzB, hzT⟩
      exact ⟨hzB, ⟨lt_of_le_of_ne hzT.1 (Ne.symm hne), hzT.2⟩⟩
    · rintro ⟨hzB, hzT⟩
      exact ⟨hzB, ⟨hzT.1.le, hzT.2⟩⟩
  have hInitialTraceIntegral : (∫ z in Sinit, Vsrc z) / ε ^ 2 < δinit := by
    have hEq : (∫ z in Sinit, Vsrc z) =
        ∫ z in SinitOpen, Vsrc z := setIntegral_congr_set hInitAE
    rw [hEq]
    simpa [SinitOpen, Vsrc, v, σ, buGaussianShiftedField] using htraceε
  have hInitialError : (256 / ε ^ 2) *
      (∫ z in K, initialMass z) ≤ Tbound := by
    have hεsq : 0 < ε ^ 2 := by positivity
    have hmass : (∫ z in Sinit, Vsrc z) ≤ δinit * ε ^ 2 :=
      (div_le_iff₀ hεsq).mp hInitialTraceIntegral.le
    have hcoeff : 0 ≤ 256 / ε ^ 2 := by positivity
    have hspace : 1 ≤ Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    have hInitialErrorStep1 :
        (256 / ε ^ 2) * (∫ z in K, initialMass z) ≤
          (256 / ε ^ 2) * (Wmax * (∫ z in Sinit, Vsrc z)) :=
      mul_le_mul_of_nonneg_left hInitialIntegral hcoeff
    have hInitialErrorStep2 :
        (256 / ε ^ 2) * (Wmax * (∫ z in Sinit, Vsrc z)) ≤
          (256 / ε ^ 2) * (Wmax * (δinit * ε ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hcoeff
      exact mul_le_mul_of_nonneg_left hmass hWmax.le
    have hInitialErrorStep3 :
        (256 / ε ^ 2) * (Wmax * (δinit * ε ^ 2)) =
          Real.exp (-2 * buGaussianBeta * ρ ^ 2) := by
      simpa only [δinit] using buGaussian_initial_error_cancel ε Wmax
        (Real.exp (-2 * buGaussianBeta * ρ ^ 2)) (ne_of_gt hε) hWmax.ne'
    have hInitialErrorStep4 :
        Real.exp (-2 * buGaussianBeta * ρ ^ 2) ≤ Tbound := by
      dsimp [Tbound]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hspace (Real.exp_nonneg _)
    exact le_trans hInitialErrorStep1
      (le_trans hInitialErrorStep2
        (le_trans (le_of_eq hInitialErrorStep3) hInitialErrorStep4))
  have hRadialIntK : Integrable (buGaussianRadialWeightedMass ρ a v)
      (volume.restrict K) :=
    hRadialInt.mono_measure (Measure.restrict_mono hKsubS₁ le_rfl)
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
  have hShellMassPoint (z : ParabolicPoint) (hzK : z ∈ K) :
      shellMass z ≤ buGaussianRadialWeightedMass ρ a v z := by
    by_cases hzShell : z ∈ Shell
    · have hr : ρ / 2 ≤ vec3EuclideanNorm z.1 := by
        have hlow := hzShell.1
        have hρpos : 0 < ρ := by linarith only [hρlarge]
        nlinarith only [hlow, hρpos]
      simp [shellMass, buGaussianRadialWeightedMass, hzShell, hr, W, Vsrc]
    · have hzS := hKsubS₁ hzK
      have hspos : 0 < z.2 := by
        have hs := hzS.2.1
        norm_num at hs ⊢
        linarith only [hs]
      by_cases hr : ρ / 2 ≤ vec3EuclideanNorm z.1
      · simp [shellMass, buGaussianRadialWeightedMass, hzShell, hr]
        exact mul_nonneg (ucGaussianWeight_nonneg a hspos) (sq_nonneg _)
      · simp [shellMass, buGaussianRadialWeightedMass, hzShell, hr]
  have hShellMassUpper : (∫ z in K, shellMass z) ≤
      24 * ρ ^ 3 * Tbound := by
    have hfirst := setIntegral_mono_on hShellMassInt hRadialIntK
      hKmeas hShellMassPoint
    have hsecond := setIntegral_mono_set hRadialInt hRadialNonneg
      (ae_of_all _ hKsubS₁)
    exact hfirst.trans (hsecond.trans hRadialTail')
  have hFactorBound :
      (Real.exp (2 * (56 * a * (2 * r) ^ 2 + 12 * ρ * (2 * r) +
        36 * ρ ^ 2 * (2 * r) ^ 2)) *
        (256 * (1 + (c₁ * scale) ^ 2 + 1 / ((2 * r) / 2) ^ 2))) *
        (8 * Besicovitch.multiplicity BUGaussianSpace ^ 2 : ℝ) ≤
      Cacc * (1 + a) := by
    exact buGaussian_shell_coefficient_bound
      (a := a) (r := r) (ρ := ρ) (scale := scale) (c₁ := c₁)
      (R₀ := R₀) (lt_trans (by norm_num : (0 : ℝ) < 1) ha)
      rfl hrhoR hscaleSqLe
  have hAmp := buGaussian_shell_amplitude_bound
    (ρ := ρ) (scale := scale) (c₁ := c₁)
    (Cg := cutoffGradientConstant) (Cs := cutoffSecondDerivativeConstant)
    hρlarge hscaleNonneg hscaleSqLe hc₁.le hcutG hcutS
  have hshell0nonneg : 0 ≤ shell0 := by simpa only [shell0] using hAmp.1
  have hshell0le : shell0 ≤ k₀ := by
    simpa only [shell0, k₀] using hAmp.2.1
  have hshell1nonneg : 0 ≤ shell1 := by
    simpa only [shell1] using hAmp.2.2.1
  have hshell1le : shell1 ≤ k₁ := by
    simpa only [shell1, k₁] using hAmp.2.2.2
  have hRadialNonnegIntegral :
      0 ≤ ∫ z in S₁, buGaussianRadialWeightedMass ρ a v z :=
    integral_nonneg_of_ae hRadialNonneg
  have hCoreBound : Icar ≤
      2 * c₀ * (192 * (k₀ ^ 2 + k₁ ^ 2 * Cacc) + 49153) *
        ((1 + a) * (1 + ρ) ^ 3 * Tbound) := by
    exact buGaussian_error_assembly_bound
      hc₀.le hk₀ hk₁ hCacc hanonneg hρnonneg hTboundNonneg
      hCarAbsorbed rfl hshell0nonneg hshell0le hshell1nonneg hshell1le
      hShellMassNonneg hShellGradNonneg hShellMassUpper
      hShellGradUpper hFactorBound hRadialNonnegIntegral hRadialTail'
      hLateIntegral hInitialError

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
