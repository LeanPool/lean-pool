/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianShellCaccioppoli
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianWeights
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays

/-!
# Gaussian mass outside the transition radius

The rescaled growth condition and Gaussian weight bound the radial mass that
appears on the transition shell in `lem:bu-gaussian`.
-/

public section


open MeasureTheory Set
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The radial weighted mass is bounded by its Gaussian tail times the
volume of the localization cylinder (`eq:bu-gaussian-collar`). -/
theorem buGaussian_radial_mass_tail_bound
    {ρ a A barA scale : ℝ} {x : Vec3}
    (hρ : 4 < ρ)
    (ha : a = buGaussianBeta * ρ ^ 2 / buGaussianH)
    (hA : 0 ≤ A) (hA0 : A ≤ 1 / (10 : ℝ) ^ 12)
    (hAbar : A ≤ barA) (hscale : scale ^ 2 ≤ 1 / 4)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2),
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hgrowth : ∀ z ∈ spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2),
      vec3EuclideanNorm (v z) ≤
        Real.exp (2 * A * vec3EuclideanNorm x ^ 2 +
          2 * A * scale ^ 2 * vec3EuclideanNorm z.1 ^ 2)) :
    (∫ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2),
      buGaussianRadialWeightedMass ρ a v z) ≤
      24 * ρ ^ 3 * Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
        Real.exp (-2 * buGaussianBeta * ρ ^ 2) := by
  let U : Set ParabolicPoint := spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
  let f : ParabolicPoint → ℝ := buGaussianRadialWeightedMass ρ a v
  let K : ℝ := Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
    Real.exp (-2 * buGaussianBeta * ρ ^ 2)
  have hρpos : 0 < ρ := by linarith only [hρ]
  have hρone : 1 ≤ ρ := by linarith only [hρ]
  have hmassInt₀ := buGaussian_local_energy_integrable hweak hL2
  have hsource := buGaussian_source_weight_parameters
  have hβ : 0 < buGaussianBeta := hsource.1
  have hH : 0 < buGaussianH := hsource.2.2.1
  have hβH : buGaussianBeta / buGaussianH < 1 / 96 := hsource.2.2.2
  have hUmeas : MeasurableSet U := by
    exact (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball 0 ρ) isOpen_Ioo).measurableSet
  have hRmeas : MeasurableSet
      {z : ParabolicPoint | ρ / 2 ≤ vec3EuclideanNorm z.1} := by
    exact measurableSet_le continuous_const.measurable
      (continuous_vec3EuclideanNorm.measurable.comp measurable_fst)
  have hWmeas : AEStronglyMeasurable (ucGaussianWeight a)
      (volume.restrict U) :=
    (ucGaussianWeight_measurable a).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have hWbound : ∀ᵐ z ∂(volume.restrict U),
      ‖ucGaussianWeight a z‖ ≤
        ((1 / 6 : ℝ) * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a) := by
    filter_upwards [ae_restrict_mem hUmeas] with z hz
    have hs : 1 / 6 ≤ z.2 := hz.2.1.le
    have hspos : 0 < z.2 := by norm_num at hs ⊢; linarith only [hs]
    rw [Real.norm_eq_abs, abs_of_nonneg (ucGaussianWeight_nonneg a hspos)]
    exact ucGaussianWeight_le_after (by norm_num) (by rw [ha]; positivity)
      hs hz.2.2.le
  have hbaseInt : Integrable
      (fun z => ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2)
      (volume.restrict U) := by
    exact hmassInt₀.1.bdd_mul hWmeas hWbound
  have hmassInt : Integrable f (volume.restrict U) := by
    have h := hbaseInt.indicator hRmeas
    convert h using 1
    ext z
    simp [f, buGaussianRadialWeightedMass, Set.indicator]
  have hβsmall : buGaussianBeta ≤ 1 / 128 := hsource.2.1
  have htailAtTwo : buGaussianLogTailExponent a ρ 2 ≤
      -2 * buGaussianBeta * ρ ^ 2 := by
    rw [buGaussianLogTailExponent, ha]
    have hlog := buGaussian_time_weight_log_two_nonneg
    have ha0 : 0 ≤ buGaussianBeta * ρ ^ 2 / buGaussianH := by positivity
    have htime : -2 * (buGaussianBeta * ρ ^ 2 / buGaussianH) *
        Real.log (gaussCarlemanTimeWeight (2 : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [ha0]) hlog
    have hρsq : 0 ≤ ρ ^ 2 := sq_nonneg ρ
    have htailCoeff : 2 * buGaussianBeta ≤ 1 / 64 := by
      dsimp [buGaussianBeta]
      norm_num
    have htail := mul_le_mul_of_nonneg_right htailCoeff hρsq
    have hdiv : ρ ^ 2 / (32 * 2) = ρ ^ 2 / 64 := by ring
    rw [hdiv]
    nlinarith only [htime, htail]
  have htail : ∀ s ∈ Ioo (1 / 6 : ℝ) 2,
      Real.exp (buGaussianLogTailExponent a ρ s) ≤
      Real.exp (-2 * buGaussianBeta * ρ ^ 2) := by
    intro s hs
    have hmono := buGaussian_log_tail_monotone hH hβ hβH ha
    have hsIcc : s ∈ Icc (1 / 6 : ℝ) 2 := ⟨hs.1.le, hs.2.le⟩
    have h₂ : (2 : ℝ) ∈ Icc (1 / 6) 2 := ⟨by norm_num, le_rfl⟩
    have hmono' := hmono hsIcc h₂ hs.2.le
    exact Real.exp_le_exp.mpr (hmono'.trans htailAtTwo)
  have hpoint : ∀ z ∈ U, 0 ≤ f z ∧ f z ≤ K := by
    intro z hz
    rcases z with ⟨y, s⟩
    change y ∈ vec3Ball 0 ρ ∧ s ∈ Ioo (1 / 6) 2 at hz
    have htime : 0 < s := by linarith only [hz.2.1]
    let z' : ParabolicPoint := (y, s)
    by_cases hr : ρ / 2 ≤ vec3EuclideanNorm y
    · have hg := hgrowth z' hz
      have hrad := buGaussian_radial_weighted_pointwise_bound (a := a)
        hA hA0 hAbar hρpos hscale htime hz.2.2.le hr (v z') hg
      have hrad' : ucGaussianWeight a z' *
          vec3EuclideanNorm (v z') ^ 2 ≤ K := by
        dsimp [K]
        exact hrad.trans (mul_le_mul_of_nonneg_left
          (htail s hz.2) (Real.exp_pos _).le)
      constructor
      · simp only [f, buGaussianRadialWeightedMass, ite_eq_left hr]
        exact mul_nonneg (ucGaussianWeight_nonneg a htime) (sq_nonneg _)
      · simpa [f, buGaussianRadialWeightedMass, hr] using hrad'
    · constructor
      · simp [f, buGaussianRadialWeightedMass, hr]
      · have hK : 0 ≤ K := by dsimp [K]; positivity
        simpa [f, buGaussianRadialWeightedMass, hr] using hK
  have hKnonneg : 0 ≤ K := by dsimp [K]; positivity
  have hUfinite : volume U < ⊤ := by
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
      (vec3Ball 0 ρ ×ˢ Ioo (1 / 6 : ℝ) 2) < ⊤
    rw [Measure.prod_prod]
    have hI : volume (Ioo (1 / 6 : ℝ) 2) < ⊤ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    exact ENNReal.mul_lt_top
      CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top hI
  have hconstInt : Integrable (fun _ : ParabolicPoint => K)
      (volume.restrict U) := integrableOn_const hUfinite.ne
  have hmassLe : (∫ z in U, f z) ≤ (∫ z in U, (fun _ : ParabolicPoint => K) z) :=
    setIntegral_mono_on hmassInt hconstInt hUmeas
      (fun z hz => (hpoint z hz).2)
  have hvol : (volume U).toReal ≤ 12 * ρ ^ 3 := by
    have hUvol : volume U = volume (vec3Ball 0 ρ) * volume (Ioo (1 / 6 : ℝ) 2) := by
      rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
      change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
        (vec3Ball 0 ρ ×ˢ Ioo (1 / 6 : ℝ) 2) = _
      rw [Measure.prod_prod]
    rw [hUvol, volume_vec3Ball_eq, Real.volume_Ioo,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hρpos.le,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi * 4 / 3),
      show (2 : ℝ) - 1 / 6 = 11 / 6 by norm_num,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 11 / 6)]
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have hρ3 : 0 ≤ ρ ^ 3 := by positivity
    nlinarith only [hpi, hρ3]
  have hconstIntegral : (∫ z in U, (fun _ : ParabolicPoint => K) z) =
      K * (volume U).toReal := by
    rw [setIntegral_const]
    simp [Measure.real, smul_eq_mul, mul_comm]
  have hfinal : (∫ z in U, f z) ≤ 24 * ρ ^ 3 * K := calc
    _ ≤ K * (volume U).toReal := by rw [← hconstIntegral]; exact hmassLe
    _ ≤ K * (12 * ρ ^ 3) := mul_le_mul_of_nonneg_left hvol hKnonneg
    _ ≤ 24 * ρ ^ 3 * K := by
      have hcoef : 12 * ρ ^ 3 ≤ 24 * ρ ^ 3 :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      calc
        K * (12 * ρ ^ 3) ≤ K * (24 * ρ ^ 3) :=
          mul_le_mul_of_nonneg_left hcoef hKnonneg
        _ = 24 * ρ ^ 3 * K := by ring
  simpa [U, f, K, mul_assoc, mul_left_comm, mul_comm] using hfinal

end ESS

end
