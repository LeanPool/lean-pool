/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureSolenoidalCutoff
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureVectorPotentialDecay
public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureMixedNorm
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureDualityPotentialEstimates
public import LeanPool.CaffarelliKohnNirenberg.Leray.TenThirdsConsumers
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Solenoidal cutoff spatial limits

Spatial profile estimates and convergence for the Helmholtz cutoff potentials.
-/

public section

open MeasureTheory Set Filter
open Filter
open scoped ENNReal
open scoped Convolution
open scoped Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat

noncomputable section

namespace CKN.Leray

/-- A time-compact spatial decay profile used to dominate the Helmholtz
cutoff derivatives. -/
@[expose]
def associatedPressureSpatialProfile
    (K : Set ℝ) (m : ℝ) (z : Vec3 × ℝ) : ℝ :=
  K.indicator (fun _ => (1 : ℝ)) z.2 * (1 + ‖z.1‖) ^ (-m)

/-- The spatial decay profile belongs to `L^r` whenever its decay exponent
beats the dimension. -/
theorem associatedPressureSpatialProfile_memLp
    {K : Set ℝ} (hK : IsCompact K) {m r : ℝ}
    (hr : 0 < r) (hmr : 3 < m * r) :
    MemLp (associatedPressureSpatialProfile K m) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)) := by
  have hrto : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr.le
  have htime : MemLp (K.indicator (fun _ : ℝ => (1 : ℝ)))
      (ENNReal.ofReal r) (volume : Measure ℝ) :=
    memLp_indicator_const (ENNReal.ofReal r) hK.measurableSet (1 : ℝ)
      (Or.inr hK.measure_lt_top.ne)
  let b : Vec3 → ℝ := fun x => (1 + ‖x‖) ^ (-m)
  have hspace : MemLp b (ENNReal.ofReal r) (volume : Measure Vec3) := by
    have hmeas : AEStronglyMeasurable b (volume : Measure Vec3) := by
      exact (by fun_prop : Measurable b).aestronglyMeasurable
    have hpower : Integrable (fun x : Vec3 => ‖b x‖ ^ r)
        (volume : Measure Vec3) := by
      have hbracket : Integrable (fun x : Vec3 =>
          (1 + ‖x‖) ^ (-(m * r))) (volume : Measure Vec3) := by
        apply integrable_one_add_norm
        rw [show (Module.finrank ℝ Vec3 : ℝ) = 3 by
          simp [Vec3]]
        linarith only [hmr]
      convert hbracket using 1
      ext x
      dsimp [b]
      rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      rw [← Real.rpow_mul (by positivity : 0 ≤ 1 + ‖x‖) (-m) r]
      congr 1
      ring
    have hp0 : ENNReal.ofReal r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hr)
    exact (integrable_norm_rpow_iff hmeas hp0 ENNReal.ofReal_ne_top).mp
      (by simpa only [hrto] using hpower)
  have hp0 : ENNReal.ofReal r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hr)
  have htimePower : Integrable
      (fun t : ℝ => ‖K.indicator (fun _ : ℝ => (1 : ℝ)) t‖ ^ r)
      (volume : Measure ℝ) := by
    simpa only [hrto] using htime.integrable_norm_rpow hp0 ENNReal.ofReal_ne_top
  have hspacePower : Integrable (fun x : Vec3 => ‖b x‖ ^ r)
      (volume : Measure Vec3) := by
    simpa only [hrto] using hspace.integrable_norm_rpow hp0 ENNReal.ofReal_ne_top
  have hprofilePower : Integrable
      (fun z : Vec3 × ℝ => ‖associatedPressureSpatialProfile K m z‖ ^ r)
      (volume : Measure (Vec3 × ℝ)) := by
    rw [Measure.volume_eq_prod]
    convert hspacePower.mul_prod htimePower using 1
    ext z
    by_cases hz : z.2 ∈ K
    · simp [associatedPressureSpatialProfile, b, hz]
    · simp [associatedPressureSpatialProfile, b, hz, Real.zero_rpow hr.ne']
  have hprofileMeas : Measurable (associatedPressureSpatialProfile K m) := by
    change Measurable (fun z : Vec3 × ℝ =>
      K.indicator (fun _ => (1 : ℝ)) z.2 * (1 + ‖z.1‖) ^ (-m))
    have hind : Measurable (K.indicator (fun _ : ℝ => (1 : ℝ))) :=
      Measurable.indicator measurable_const hK.measurableSet
    have hbracket : Measurable (fun z : Vec3 × ℝ =>
        (1 + ‖z.1‖) ^ (-m)) := by fun_prop
    exact (hind.comp measurable_snd).mul hbracket
  have hprofile : AEStronglyMeasurable
      (associatedPressureSpatialProfile K m) (volume : Measure (Vec3 × ℝ)) :=
    hprofileMeas.aestronglyMeasurable
  exact (integrable_norm_rpow_iff hprofile hp0 ENNReal.ofReal_ne_top).mp
    (by simpa only [hrto] using hprofilePower)

private theorem associatedPressureDecayRpow_le_profileTwo
    (x : Vec3) (k : ℕ) (hk : 2 ≤ k) :
    (1 + vec3EuclideanNorm x) ^ (-(k : ℝ)) ≤ (1 + ‖x‖) ^ (-(2 : ℝ)) := by
  have hnorm := CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm x
  calc
    (1 + vec3EuclideanNorm x) ^ (-(k : ℝ)) ≤
        (1 + ‖x‖) ^ (-(k : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity)
        (by linarith only [hnorm]) (by norm_num)
    _ ≤ (1 + ‖x‖) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith only [norm_nonneg x]) (by
        exact neg_le_neg (by exact_mod_cast hk))

private theorem associatedPressureProfile_four_le_two
    (K : Set ℝ) (z : Vec3 × ℝ) :
    rieszPressurePotentialSpatialProfile K z ≤
      associatedPressureSpatialProfile K 2 z := by
  by_cases hz : z.2 ∈ K
  · simp only [rieszPressurePotentialSpatialProfile, associatedPressureSpatialProfile,
      Set.indicator_of_mem hz, one_mul]
    exact Real.rpow_le_rpow_of_exponent_le
      (by nlinarith only [norm_nonneg z.1]) (by norm_num)
  · simp [rieszPressurePotentialSpatialProfile, associatedPressureSpatialProfile, hz]

/-- Uniform spatial-profile control of the Hessian of a cutoff potential. -/
theorem associatedPressurePotentialCutoff_hessian_profile_bound
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {K : Set ℝ} (hzero : ∀ t ∉ K, ∀ x, ψ (x, t) = 0)
    (hdecay : RieszPressurePotentialDecay ψ) (i j : Fin 3)
    (n : ℕ) (z : Vec3 × ℝ) :
    |rieszPressureJointHessian
        (rieszPressurePotentialCutoffTest ψ n) i j z| ≤
      (2 * Classical.choose hdecay.hessian_bound +
        6 * CKN.cutoffGradientConstant * Classical.choose hdecay.gradient_bound +
        9 * CKN.cutoffSecondDerivativeConstant * Classical.choose hdecay.value_bound) *
        associatedPressureSpatialProfile K 2 z := by
  by_cases ht : z.2 ∈ K
  · have hsource := rieszPressurePotentialDecay_hessian_bound_norm hdecay i j z
    have herr := rieszPressurePotentialHessianCutoffError_bound
      hψ hzero hdecay i j n z
    have hC0 : 0 ≤ Classical.choose hdecay.value_bound :=
      (Classical.choose_spec hdecay.value_bound).1
    have hC1 : 0 ≤ Classical.choose hdecay.gradient_bound :=
      (Classical.choose_spec hdecay.gradient_bound).1
    have hC2 : 0 ≤ Classical.choose hdecay.hessian_bound :=
      (Classical.choose_spec hdecay.hessian_bound).1
    have hGradUnit := CKN.mollifiedBallCutoff_gradient_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    have hGradC : 0 ≤ CKN.cutoffGradientConstant := by
      have h := le_trans (CKN.vecEuclideanNorm_nonneg _) hGradUnit
      simpa using h
    have hSecondUnit := CKN.mollifiedBallCutoff_second_derivative_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    have hSecondC : 0 ≤ CKN.cutoffSecondDerivativeConstant := by
      have h := le_trans (norm_nonneg _) hSecondUnit
      simpa using h
    have hcoeff : 0 ≤ 2 * Classical.choose hdecay.hessian_bound +
        6 * CKN.cutoffGradientConstant * Classical.choose hdecay.gradient_bound +
        9 * CKN.cutoffSecondDerivativeConstant * Classical.choose hdecay.value_bound := by
      positivity
    have hprofile : rieszPressurePotentialSpatialProfile K z ≤
        associatedPressureSpatialProfile K 2 z :=
      associatedPressureProfile_four_le_two K z
    have hsource' : |rieszPressureJointHessian ψ i j z| ≤
        Classical.choose hdecay.hessian_bound * rieszPressurePotentialSpatialProfile K z := by
      have hprofileEq : rieszPressurePotentialSpatialProfile K z =
          (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
        simp [rieszPressurePotentialSpatialProfile, ht]
      rw [hprofileEq]
      exact hsource
    have hrelation : rieszPressureJointHessian
        (rieszPressurePotentialCutoffTest ψ n) i j z =
          rieszPressureJointHessian ψ i j z +
            rieszPressurePotentialHessianCutoffError ψ i j n z := by
      simp [rieszPressurePotentialHessianCutoffError]
    rw [hrelation]
    calc
      |rieszPressureJointHessian ψ i j z +
          rieszPressurePotentialHessianCutoffError ψ i j n z| ≤
          |rieszPressureJointHessian ψ i j z| +
            |rieszPressurePotentialHessianCutoffError ψ i j n z| := abs_add_le _ _
      _ ≤ (Classical.choose hdecay.hessian_bound +
          Classical.choose hdecay.hessian_bound +
            6 * CKN.cutoffGradientConstant * Classical.choose hdecay.gradient_bound +
            9 * CKN.cutoffSecondDerivativeConstant * Classical.choose hdecay.value_bound) *
          rieszPressurePotentialSpatialProfile K z := by
        calc
          _ ≤ Classical.choose hdecay.hessian_bound *
              rieszPressurePotentialSpatialProfile K z +
                (Classical.choose hdecay.hessian_bound +
                  6 * CKN.cutoffGradientConstant * Classical.choose hdecay.gradient_bound +
                  9 * CKN.cutoffSecondDerivativeConstant *
                    Classical.choose hdecay.value_bound) *
                rieszPressurePotentialSpatialProfile K z := add_le_add hsource' herr
          _ = _ := by ring
      _ = (2 * Classical.choose hdecay.hessian_bound +
            6 * CKN.cutoffGradientConstant * Classical.choose hdecay.gradient_bound +
            9 * CKN.cutoffSecondDerivativeConstant * Classical.choose hdecay.value_bound) *
          rieszPressurePotentialSpatialProfile K z := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprofile hcoeff
  · have hsourceSlice : (fun x : Vec3 => ψ (x, z.2)) = fun _ => (0 : ℝ) := by
      funext x
      exact hzero z.2 ht x
    have htestSlice : (fun x : Vec3 =>
        rieszPressurePotentialCutoffTest ψ n (x, z.2)) = fun _ => (0 : ℝ) := by
      funext x
      simp [rieszPressurePotentialCutoffTest, hzero z.2 ht x]
    have htest := rieszPressureJointHessian_zero_of_slice_zero
      (rieszPressurePotentialCutoffTest_contDiff hψ n) htestSlice i j
    simp [htest, associatedPressureSpatialProfile, ht]

private theorem associatedPressureJointDirection_zero_of_slice_zero
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hzero : (fun x : Vec3 => ψ (x, z.2)) = fun _ => (0 : ℝ))
    (i : Fin 3) : rieszPressureJointDirection ψ i z = 0 := by
  rw [← rieszPressure_sliceSpatialDeriv_eq_joint hψ i z]
  rw [hzero]
  simp [CKN.spatialDeriv]

private theorem associatedPressurePotentialCutoff_direction_formula
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i : Fin 3) (n : ℕ) (z : Vec3 × ℝ) :
    rieszPressureJointDirection
      (rieszPressurePotentialCutoffTest ψ n) i z =
      CKN.spatialDeriv (rieszPressurePotentialCutoff n) i z.1 * ψ z +
        rieszPressurePotentialCutoff n z.1 *
          rieszPressureJointDirection ψ i z := by
  rw [← rieszPressure_sliceSpatialDeriv_eq_joint
      (rieszPressurePotentialCutoffTest_contDiff hψ n) i z,
    ← rieszPressure_sliceSpatialDeriv_eq_joint hψ i z]
  have hη : ContDiff ℝ (⊤ : ℕ∞) (rieszPressurePotentialCutoff n) :=
    CKN.mollifiedBallCutoff_smooth 0 (rieszPressurePotentialCutoffRadius_pos n)
  have hψslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => ψ (x, z.2)) :=
    hψ.comp (contDiff_id.prodMk contDiff_const)
  have hprod := CKN.spatialDeriv_mul
    ((hη.differentiable (by simp)) z.1)
    ((hψslice.differentiable (by simp)) z.1) i
  simpa [rieszPressurePotentialCutoffTest] using hprod

/-- Uniform spatial-profile control of the gradient of a cutoff potential. -/
theorem associatedPressurePotentialCutoff_direction_profile_bound
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {K : Set ℝ} (hzero : ∀ t ∉ K, ∀ x, ψ (x, t) = 0)
    (hdecay : RieszPressurePotentialDecay ψ) (i : Fin 3)
    (n : ℕ) (z : Vec3 × ℝ) :
    |rieszPressureJointDirection
      (rieszPressurePotentialCutoffTest ψ n) i z| ≤
      (Classical.choose hdecay.gradient_bound +
        CKN.cutoffGradientConstant * Classical.choose hdecay.value_bound) *
        associatedPressureSpatialProfile K 2 z := by
  let η : Vec3 → ℝ := rieszPressurePotentialCutoff n
  have htest : ContDiff ℝ (⊤ : ℕ∞) (rieszPressurePotentialCutoffTest ψ n) :=
    rieszPressurePotentialCutoffTest_contDiff hψ n
  have hformula := associatedPressurePotentialCutoff_direction_formula hψ i n z
  have hC0 : 0 ≤ Classical.choose hdecay.value_bound :=
    (Classical.choose_spec hdecay.value_bound).1
  have hC1 : 0 ≤ Classical.choose hdecay.gradient_bound :=
    (Classical.choose_spec hdecay.gradient_bound).1
  have hGradUnit := CKN.mollifiedBallCutoff_gradient_bound 0
    (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
  have hGradC : 0 ≤ CKN.cutoffGradientConstant := by
    have h := le_trans (CKN.vecEuclideanNorm_nonneg _) hGradUnit
    simpa using h
  have hscale : 1 ≤ rieszPressurePotentialCutoffScale n :=
    rieszPressurePotentialCutoffScale_ge_one n
  have hcutoffBounds := rieszPressurePotentialCutoff_bounds n z.1
  have hcutoffAbs : |η z.1| ≤ 1 := abs_le.mpr ⟨
    (by norm_num : (-1 : ℝ) ≤ 0).trans hcutoffBounds.1, hcutoffBounds.2⟩
  have hcutoffGrad : |CKN.spatialDeriv η i z.1| ≤ CKN.cutoffGradientConstant := by
    have h := rieszPressurePotentialCutoff_gradient_bound n i z.1
    exact h.trans (div_le_self hGradC hscale)
  by_cases ht : z.2 ∈ K
  · have hprofile : associatedPressureSpatialProfile K 2 z =
        (1 + ‖z.1‖) ^ (-(2 : ℝ)) := by
      simp [associatedPressureSpatialProfile, ht]
    have hvalue : |ψ z| ≤ Classical.choose hdecay.value_bound *
        associatedPressureSpatialProfile K 2 z := by
      have hbound := (Classical.choose_spec hdecay.value_bound).2 z
      rw [hprofile]
      exact hbound.trans (mul_le_mul_of_nonneg_left
        (associatedPressureDecayRpow_le_profileTwo z.1 2 (by norm_num)) hC0)
    have hdirection : |rieszPressureJointDirection ψ i z| ≤
        Classical.choose hdecay.gradient_bound *
          associatedPressureSpatialProfile K 2 z := by
      have hbound := (Classical.choose_spec hdecay.gradient_bound).2 i z
      rw [hprofile]
      exact hbound.trans (mul_le_mul_of_nonneg_left
        (associatedPressureDecayRpow_le_profileTwo z.1 3 (by norm_num)) hC1)
    rw [hformula]
    calc
      |CKN.spatialDeriv η i z.1 * ψ z +
          η z.1 * rieszPressureJointDirection ψ i z| ≤
        |CKN.spatialDeriv η i z.1 * ψ z| +
          |η z.1 * rieszPressureJointDirection ψ i z| := abs_add_le _ _
      _ ≤ CKN.cutoffGradientConstant *
            Classical.choose hdecay.value_bound *
              associatedPressureSpatialProfile K 2 z +
          Classical.choose hdecay.gradient_bound *
            associatedPressureSpatialProfile K 2 z := by
        rw [abs_mul, abs_mul]
        calc
          _ ≤ CKN.cutoffGradientConstant *
                (Classical.choose hdecay.value_bound *
                  associatedPressureSpatialProfile K 2 z) +
              1 * (Classical.choose hdecay.gradient_bound *
                associatedPressureSpatialProfile K 2 z) := add_le_add
              (mul_le_mul hcutoffGrad hvalue (abs_nonneg _) hGradC)
              (mul_le_mul hcutoffAbs hdirection (abs_nonneg _) (by norm_num))
          _ = _ := by ring
      _ = _ := by ring
  · have hslice : (fun x : Vec3 => ψ (x, z.2)) = fun _ => (0 : ℝ) := by
      funext x
      exact hzero z.2 ht x
    have hzeroTest : (fun x : Vec3 =>
        rieszPressurePotentialCutoffTest ψ n (x, z.2)) = fun _ => (0 : ℝ) := by
      funext x
      simp [rieszPressurePotentialCutoffTest, hzero z.2 ht x]
    have hzeroTestDirection := associatedPressureJointDirection_zero_of_slice_zero
      htest hzeroTest i
    have hprofile : associatedPressureSpatialProfile K 2 z = 0 := by
      simp [associatedPressureSpatialProfile, ht]
    rw [hzeroTestDirection, hprofile]
    simp

/-- At each fixed point, the cutoff potential gradient eventually agrees with
the uncut gradient. -/
theorem associatedPressurePotentialCutoff_direction_eventually_eq
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i : Fin 3) (z : Vec3 × ℝ) :
    ∀ᶠ n : ℕ in atTop,
      rieszPressureJointDirection
        (rieszPressurePotentialCutoffTest ψ n) i z =
          rieszPressureJointDirection ψ i z := by
  obtain ⟨N, hN⟩ := exists_nat_gt (CKN.vecEuclideanNorm z.1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnorm : CKN.vecEuclideanNorm z.1 <
      rieszPressurePotentialCutoffScale n := by
    dsimp [rieszPressurePotentialCutoffScale]
    linarith only [hN, hNn]
  have hxBall : z.1 ∈ CKN.euclideanBall 0
      (rieszPressurePotentialCutoffScale n) :=
    (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (rieszPressurePotentialCutoffScale_pos n)).2 (by simpa using hnorm)
  have hscaleNonneg : 0 ≤ rieszPressurePotentialCutoffScale n :=
    le_trans (by norm_num) (rieszPressurePotentialCutoffScale_ge_one n)
  have hxClosed : z.1 ∈ CKN.euclideanClosedBall 0
      (rieszPressurePotentialCutoffScale n) :=
    (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hscaleNonneg).2
      (by simpa using hnorm.le)
  have heta := rieszPressurePotentialCutoff_eq_one n hxBall
  have hderivs := rieszPressurePotentialCutoff_derivatives_zero_on_inner n hxClosed
  have hcutgrad : CKN.spatialDeriv (rieszPressurePotentialCutoff n) i z.1 = 0 := by
    change CKN.classicalGradient (rieszPressurePotentialCutoff n) z.1 i = 0
    rw [hderivs.1]
    simp
  rw [associatedPressurePotentialCutoff_direction_formula hψ i n z,
    hcutgrad, heta]
  simp

/-- The cutoff potential Hessian agrees with the original Hessian on the
inner ball where the cutoff is constant. -/
theorem associatedPressurePotentialCutoff_hessian_eq_of_inner
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i j : Fin 3) (n : ℕ) (z : Vec3 × ℝ)
    (hxBall : z.1 ∈ CKN.euclideanBall 0
      (rieszPressurePotentialCutoffScale n))
    (hxClosed : z.1 ∈ CKN.euclideanClosedBall 0
      (rieszPressurePotentialCutoffScale n)) :
    rieszPressureJointHessian
      (rieszPressurePotentialCutoffTest ψ n) i j z =
        rieszPressureJointHessian ψ i j z := by
  have heta := rieszPressurePotentialCutoff_eq_one n hxBall
  have hderivs := rieszPressurePotentialCutoff_derivatives_zero_on_inner n hxClosed
  have hgrad (k : Fin 3) :
      CKN.spatialDeriv (rieszPressurePotentialCutoff n) k z.1 = 0 := by
    change CKN.classicalGradient (rieszPressurePotentialCutoff n) z.1 k = 0
    rw [hderivs.1]
    simp
  have hhess (k l : Fin 3) :
      CKN.mixedSecond (rieszPressurePotentialCutoff n) k l z.1 = 0 := by
    have hη := CKN.mollifiedBallCutoff_smooth 0
      (rieszPressurePotentialCutoffRadius_pos n)
    have hgradSmooth : ContDiff ℝ (⊤ : ℕ∞)
        (CKN.classicalGradient (rieszPressurePotentialCutoff n)) := by
      rw [contDiff_pi]
      intro m
      change ContDiff ℝ (⊤ : ℕ∞)
        (CKN.spatialDeriv (rieszPressurePotentialCutoff n) m)
      exact CKN.contDiff_spatialDeriv_smooth hη m
    change CKN.spatialDeriv
      (CKN.spatialDeriv (rieszPressurePotentialCutoff n) l) k z.1 = 0
    change (fderiv ℝ (fun y : Vec3 =>
      CKN.classicalGradient (rieszPressurePotentialCutoff n) y l) z.1)
      (CKN.basisVec k) = 0
    rw [fderiv_apply (hgradSmooth.differentiable (by simp) z.1) l,
      hderivs.2]
    rfl
  rw [rieszPressurePotentialCutoffTest_hessian_formula hψ n i j z,
    hhess i j, hgrad i, hgrad j, heta]
  ring

private theorem spatial_curl_eq_of_second_partials
    (A B : Vec3 × ℝ → Vec3)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hB : ContDiff ℝ (⊤ : ℕ∞) B)
    (i j : Fin 3) (z : Vec3 × ℝ)
    (hdouble : ∀ k l : Fin 3,
      CKN.spatialPartialProd
        (CKN.spatialPartialProd (fun w => B w k) l) j z =
      CKN.spatialPartialProd
        (CKN.spatialPartialProd (fun w => A w k) l) j z) :
    CKN.spatialPartialProd (fun w => associatedPressureTestCurl B w i) j z =
      CKN.spatialPartialProd (fun w => associatedPressureTestCurl A w i) j z := by
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun w => A w k) :=
    (contDiff_apply ℝ ℝ k).comp hA
  have hBcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun w => B w k) :=
    (contDiff_apply ℝ ℝ k).comp hB
  have hsub {f g : Vec3 × ℝ → ℝ}
      (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
      CKN.spatialPartialProd (fun w => f w - g w) j z =
        CKN.spatialPartialProd f j z - CKN.spatialPartialProd g j z := by
    have hfSlice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => f (x, z.2)) :=
      hf.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)
    have hgSlice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, z.2)) :=
      hg.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)
    have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec j))
      (fderiv_fun_sub (hfSlice.differentiable (by simp) z.1)
        (hgSlice.differentiable (by simp) z.1))
    simpa [CKN.spatialPartialProd, CKN.spatialPartial] using h
  have hpartial (k l : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞)
        (CKN.spatialPartialProd
          (fun w : Vec3 × ℝ => A w k) l) :=
    CKN.spatialPartial_contDiff (hAcomp k) l
  fin_cases i
  · change CKN.spatialPartialProd
        (fun w => CKN.spatialPartialProd
          (fun q : Vec3 × ℝ =>
                B q 2) 1 w -
          CKN.spatialPartialProd
          (fun q : Vec3 × ℝ =>
                B q 1) 2 w) j z =
      CKN.spatialPartialProd
        (fun w => CKN.spatialPartialProd
          (fun q : Vec3 × ℝ =>
                A q 2) 1 w -
          CKN.spatialPartialProd
          (fun q : Vec3 × ℝ =>
                A q 1) 2 w) j z
    have hcutSub := hsub
      (f := fun w => CKN.spatialPartialProd
        (fun q : Vec3 × ℝ =>
                B q 2) 1 w)
      (g := fun w => CKN.spatialPartialProd
        (fun q : Vec3 × ℝ =>
                B q 1) 2 w)
      (CKN.spatialPartial_contDiff (hBcomp 2) 1)
      (CKN.spatialPartial_contDiff (hBcomp 1) 2)
    have hA_sub := hsub
      (f := fun w => CKN.spatialPartialProd
        (fun q : Vec3 × ℝ =>
                A q 2) 1 w)
      (g := fun w => CKN.spatialPartialProd
        (fun q : Vec3 × ℝ =>
                A q 1) 2 w)
      (hpartial 2 1) (hpartial 1 2)
    calc
      _ = CKN.spatialPartialProd
            (fun w => CKN.spatialPartialProd
              (fun q : Vec3 × ℝ =>
                B q 2) 1 w) j z -
          CKN.spatialPartialProd
            (fun w => CKN.spatialPartialProd
              (fun q : Vec3 × ℝ =>
                B q 1) 2 w) j z := hcutSub
      _ = CKN.spatialPartialProd
            (fun w => CKN.spatialPartialProd
              (fun q : Vec3 × ℝ =>
                A q 2) 1 w) j z -
          CKN.spatialPartialProd
            (fun w => CKN.spatialPartialProd
              (fun q : Vec3 × ℝ =>
                A q 1) 2 w) j z := by
        rw [hdouble 2 1, hdouble 1 2]
      _ = _ := hA_sub.symm
  · change CKN.spatialPartialProd
        (fun w => CKN.spatialPartialProd
          (fun q : Vec3 × ℝ =>
                B q 0) 2 w -
          CKN.spatialPartialProd
          (fun q : Vec3 × ℝ =>
                B q 2) 0 w) j z =
      CKN.spatialPartialProd
        (fun w => CKN.spatialPartialProd
          (fun q : Vec3 × ℝ =>
                A q 0) 2 w -
          CKN.spatialPartialProd
          (fun q : Vec3 × ℝ =>
                A q 2) 0 w) j z
    have hcutSub := hsub
      (f := fun w => CKN.spatialPartialProd
        (fun q : Vec3 × ℝ =>
                B q 0) 2 w)
      (g := fun w => CKN.spatialPartialProd
        (fun q : Vec3 × ℝ =>
                B q 2) 0 w)
      (CKN.spatialPartial_contDiff (hBcomp 0) 2)
      (CKN.spatialPartial_contDiff (hBcomp 2) 0)
    have hA_sub := hsub
      (f := fun w => CKN.spatialPartialProd
        (fun q : Vec3 × ℝ =>
                A q 0) 2 w)
      (g := fun w => CKN.spatialPartialProd
        (fun q : Vec3 × ℝ =>
                A q 2) 0 w)
      (hpartial 0 2) (hpartial 2 0)
    calc
      _ = CKN.spatialPartialProd
            (fun w => CKN.spatialPartialProd
              (fun q : Vec3 × ℝ =>
                B q 0) 2 w) j z -
          CKN.spatialPartialProd
            (fun w => CKN.spatialPartialProd
              (fun q : Vec3 × ℝ =>
                B q 2) 0 w) j z := hcutSub
      _ = CKN.spatialPartialProd
            (fun w => CKN.spatialPartialProd
              (fun q : Vec3 × ℝ =>
                A q 0) 2 w) j z -
          CKN.spatialPartialProd
            (fun w => CKN.spatialPartialProd
              (fun q : Vec3 × ℝ =>
                A q 2) 0 w) j z := by
        rw [hdouble 0 2, hdouble 2 0]
      _ = _ := hA_sub.symm
  · change CKN.spatialPartialProd
        (fun w => CKN.spatialPartialProd
          (fun q : Vec3 × ℝ =>
                B q 1) 0 w -
          CKN.spatialPartialProd
          (fun q : Vec3 × ℝ =>
                B q 0) 1 w) j z =
      CKN.spatialPartialProd
        (fun w => CKN.spatialPartialProd
          (fun q : Vec3 × ℝ =>
                A q 1) 0 w -
          CKN.spatialPartialProd
          (fun q : Vec3 × ℝ =>
                A q 0) 1 w) j z
    have hcutSub := hsub
      (f := fun w => CKN.spatialPartialProd
        (fun q : Vec3 × ℝ =>
                B q 1) 0 w)
      (g := fun w => CKN.spatialPartialProd
        (fun q : Vec3 × ℝ =>
                B q 0) 1 w)
      (CKN.spatialPartial_contDiff (hBcomp 1) 0)
      (CKN.spatialPartial_contDiff (hBcomp 0) 1)
    have hA_sub := hsub
      (f := fun w => CKN.spatialPartialProd
        (fun q : Vec3 × ℝ =>
                A q 1) 0 w)
      (g := fun w => CKN.spatialPartialProd
        (fun q : Vec3 × ℝ =>
                A q 0) 1 w)
      (hpartial 1 0) (hpartial 0 1)
    calc
      _ = CKN.spatialPartialProd
            (fun w => CKN.spatialPartialProd
              (fun q : Vec3 × ℝ =>
                B q 1) 0 w) j z -
          CKN.spatialPartialProd
            (fun w => CKN.spatialPartialProd
              (fun q : Vec3 × ℝ =>
                B q 0) 1 w) j z := hcutSub
      _ = CKN.spatialPartialProd
            (fun w => CKN.spatialPartialProd
              (fun q : Vec3 × ℝ =>
                A q 1) 0 w) j z -
          CKN.spatialPartialProd
            (fun w => CKN.spatialPartialProd
              (fun q : Vec3 × ℝ =>
                A q 0) 1 w) j z := by
        rw [hdouble 1 0, hdouble 0 1]
      _ = _ := hA_sub.symm


/-- Spatial derivatives of the cutoff curl eventually agree pointwise with
those of the full Helmholtz curl. -/
theorem associatedPressureHelmholtzCutoffCurl_spatial_eventually_eq
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (i j : Fin 3) (z : Vec3 × ℝ) :
    ∀ᶠ n : ℕ in atTop,
      CKN.spatialPartialProd
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) w i) j z =
      CKN.spatialPartialProd
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotential φ) w i) j z := by
  obtain ⟨N, hN⟩ := exists_nat_gt (CKN.vecEuclideanNorm z.1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnorm : CKN.vecEuclideanNorm z.1 <
      rieszPressurePotentialCutoffScale n := by
    dsimp [rieszPressurePotentialCutoffScale]
    linarith only [hN, hNn]
  have hxBall : z.1 ∈ CKN.euclideanBall 0
      (rieszPressurePotentialCutoffScale n) :=
    (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (rieszPressurePotentialCutoffScale_pos n)).2 (by simpa using hnorm)
  have hscaleNonneg : 0 ≤ rieszPressurePotentialCutoffScale n :=
    le_trans (by norm_num) (rieszPressurePotentialCutoffScale_ge_one n)
  have hxClosed : z.1 ∈ CKN.euclideanClosedBall 0
      (rieszPressurePotentialCutoffScale n) :=
    (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hscaleNonneg).2
      (by simpa using hnorm.le)
  have hA : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzVectorPotential φ) :=
    associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hcut : ∀ n : ℕ, ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzCutoffVectorPotential φ n) := by
    intro m
    exact (associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction
      hφ m).1
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => associatedPressureHelmholtzVectorPotential φ w k) :=
    (contDiff_apply ℝ ℝ k).comp hA
  have hcutComp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ =>
        associatedPressureHelmholtzCutoffVectorPotential φ n w k) :=
    (contDiff_apply ℝ ℝ k).comp (hcut n)
  have hdouble (k l : Fin 3) :
      CKN.spatialPartialProd
          (CKN.spatialPartialProd
            (fun w : Vec3 × ℝ =>
              associatedPressureHelmholtzCutoffVectorPotential φ n w k) l) j z =
      CKN.spatialPartialProd
          (CKN.spatialPartialProd
            (fun w : Vec3 × ℝ => associatedPressureHelmholtzVectorPotential φ w k) l) j z := by
    have hEq := associatedPressurePotentialCutoff_hessian_eq_of_inner
      (hAcomp k) j l n z hxBall hxClosed
    have hcutId := rieszPressure_sliceMixedSecond_eq_joint (hcutComp k) j l z
    have hAId := rieszPressure_sliceMixedSecond_eq_joint (hAcomp k) j l z
    change CKN.mixedSecond
        (fun x : Vec3 => associatedPressureHelmholtzCutoffVectorPotential φ n (x, z.2) k)
        j l z.1 = _
    exact hcutId.trans (hEq.trans hAId.symm)
  exact spatial_curl_eq_of_second_partials
    (associatedPressureHelmholtzVectorPotential φ)
    (associatedPressureHelmholtzCutoffVectorPotential φ n) hA (hcut n) i j z hdouble

end CKN.Leray

end
