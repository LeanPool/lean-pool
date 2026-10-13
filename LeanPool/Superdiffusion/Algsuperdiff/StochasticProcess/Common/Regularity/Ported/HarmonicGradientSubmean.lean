/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.Carrier
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.FluxSubharmonic
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderLapTransfer
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepWeylRepresentative
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.EuclideanL2CZ
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.H1Transport
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# HarmonicGradientSubmean

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Submean structure of the energy of a harmonic gradient

This file supplies the smooth analytic half of the constant-one concentric-ball
energy comparison used by the small-contrast Schauder iteration.  It is kept on
the coordinate carrier long enough to reuse the established mixed-derivative
calculus, then transported to the Euclidean carrier used by the sphere/flux
machinery.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open InnerProductSpace
open MeasureTheory Metric Set
open HCPolySupport
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-- Identification of the gradient of a smooth representative with the weak
gradient on an open subwindow. -/
theorem ae_eq_euclideanGradient_of_ae_eq_of_contDiff
    {U V : Set (Vec d)} (hV : IsOpen V) (hVU : V ⊆ U)
    [IsFiniteMeasure (volumeMeasureOn V)]
    (h : H1Function U) {v : Vec d → ℝ} (hv : ContDiff ℝ 1 v)
    (hae : v =ᵐ[volume.restrict V] h.toFun) :
    euclideanGradient v =ᵐ[volume.restrict V] h.grad := by
  have hgv : HasWeakGradientOn V v (euclideanGradient v) :=
    HasWeakGradientOn.of_contDiff hv
  have hcoord : ∀ i : Fin d,
      (fun x ↦ euclideanGradient v x i) =ᵐ[volume.restrict V]
        fun x ↦ h.grad x i := by
    intro i
    apply Book.Ch03.HasWeakPartialDerivOn.ae_eq_of_toFun_ae_eq hV hae
    · have hcont : Continuous (fun x ↦ euclideanGradient v x i) := by
        simpa [euclideanGradient, euclideanCoordDeriv] using
          (hv.continuous_fderiv (by simp)).clm_apply
            (continuous_const (y := basisVec i))
      exact hcont.locallyIntegrable.locallyIntegrableOn V
    · have hL2 : MemL2On V (fun x ↦ h.grad x i) :=
        memL2On_mono hVU (h.grad_memL2 i)
      have hint : IntegrableOn (fun x ↦ h.grad x i) V volume :=
        hL2.integrable (by norm_num)
      exact hint.locallyIntegrableOn
    · exact hgv i
    · exact HasWeakPartialDerivOn.restrict hV hVU (h.hasWeakGradient i)
  have hall : ∀ᵐ x ∂(volume.restrict V), ∀ i : Fin d,
      euclideanGradient v x i = h.grad x i := ae_all_iff.2 hcoord
  filter_upwards [hall] with x hx
  funext i
  exact hx i

private theorem euclideanCoordDeriv_eq_zero_of_eventuallyEq
    {f : Vec d → ℝ} {c : ℝ} {x : Vec d}
    (h : f =ᶠ[nhds x] fun _ : Vec d ↦ c) (i : Fin d) :
    euclideanCoordDeriv i f x = 0 := by
  rw [euclideanCoordDeriv, h.fderiv_eq]
  simp

/-- A coordinate derivative of a smooth coordinate-harmonic function is
coordinate-harmonic. -/
theorem euclideanCoordLaplacian_euclideanCoordDeriv_eq_zero
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {U : Set (Vec d)} (hU : IsOpen U)
    (hharm : ∀ y ∈ U, euclideanCoordLaplacian u y = 0)
    {x : Vec d} (hx : x ∈ U) (i : Fin d) :
    euclideanCoordLaplacian (euclideanCoordDeriv i u) x = 0 := by
  have hstep : ∀ j : Fin d,
      euclideanCoordSecondDeriv j j (euclideanCoordDeriv i u) x =
        euclideanCoordDeriv i (euclideanCoordSecondDeriv j j u) x := fun j ↦
    euclideanCoordThirdDeriv_diag_right_comm hu i j x
  have hg : ∀ j : Fin d, HasFDerivAt (euclideanCoordSecondDeriv j j u)
      (fderiv ℝ (euclideanCoordSecondDeriv j j u) x) x := fun j ↦
    ((contDiff_euclideanCoordSecondDeriv hu j j).differentiable (by simp) x).hasFDerivAt
  have hL : HasFDerivAt (fun y : Vec d ↦ ∑ j : Fin d, euclideanCoordSecondDeriv j j u y)
      (∑ j : Fin d, fderiv ℝ (euclideanCoordSecondDeriv j j u) x) x := by
    have hres := HasFDerivAt.sum fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) ↦ hg j
    have hfun : (∑ j : Fin d, euclideanCoordSecondDeriv j j u) =
        fun y : Vec d ↦ ∑ j : Fin d, euclideanCoordSecondDeriv j j u y := by
      funext y
      simp [Finset.sum_apply]
    rw [hfun] at hres
    exact hres
  have hzero : euclideanCoordDeriv i (euclideanCoordLaplacian u) x = 0 :=
    euclideanCoordDeriv_eq_zero_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hharm) i
  have hsplit : euclideanCoordDeriv i (euclideanCoordLaplacian u) x =
      ∑ j : Fin d, euclideanCoordDeriv i (euclideanCoordSecondDeriv j j u) x := by
    rw [euclideanCoordDeriv,
      show euclideanCoordLaplacian u =
        fun y : Vec d ↦ ∑ j : Fin d, euclideanCoordSecondDeriv j j u y from rfl,
      hL.fderiv]
    simp [euclideanCoordDeriv]
  rw [euclideanCoordLaplacian]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) ↦ hstep j, ← hsplit, hzero]

/-- The coordinate Laplacian of a square is twice the squared coordinate
gradient plus twice the function times its Laplacian. -/
theorem euclideanCoordLaplacian_sq
    {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Vec d) :
    euclideanCoordLaplacian (fun y ↦ g y ^ 2) x =
      2 * ∑ j : Fin d, (euclideanCoordDeriv j g x) ^ 2 +
        2 * g x * euclideanCoordLaplacian g x := by
  classical
  have hD : ∀ j : Fin d, ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv j g) :=
    fun j ↦ contDiff_euclideanCoordDeriv hg j
  have hsecond : ∀ j : Fin d,
      euclideanCoordSecondDeriv j j (fun y ↦ g y ^ 2) x =
        2 * (euclideanCoordDeriv j g x) ^ 2 +
          2 * g x * euclideanCoordSecondDeriv j j g x := by
    intro j
    rw [euclideanCoordSecondDeriv]
    have hfirst : euclideanCoordDeriv j (fun y ↦ g y ^ 2) =
        fun y ↦ 2 * g y * euclideanCoordDeriv j g y := by
      funext y
      exact euclideanCoordDeriv_sq hg j y
    rw [hfirst]
    unfold euclideanCoordDeriv
    have hgdiff : DifferentiableAt ℝ g x := (hg.differentiable (by simp)) x
    have hDdiff : DifferentiableAt ℝ (euclideanCoordDeriv j g) x :=
      ((hD j).differentiable (by simp)) x
    have h2gdiff : DifferentiableAt ℝ (fun y ↦ (2 : ℝ) * g y) x :=
      differentiableAt_const (c := (2 : ℝ)).mul hgdiff
    change (fderiv ℝ ((fun y ↦ (2 : ℝ) * g y) * euclideanCoordDeriv j g) x)
        (basisVec j) = _
    rw [fderiv_mul h2gdiff hDdiff]
    simp only [add_apply, smul_apply]
    rw [fderiv_const_mul hgdiff]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    simp only [euclideanCoordSecondDeriv, euclideanCoordDeriv]
    ring
  rw [euclideanCoordLaplacian, Finset.sum_congr rfl
    (fun j (_ : j ∈ Finset.univ) ↦ hsecond j), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [euclideanCoordLaplacian]

/-- The squared coordinate derivative of a smooth harmonic function is
subharmonic. -/
theorem euclideanCoordLaplacian_sq_euclideanCoordDeriv_nonneg
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {U : Set (Vec d)} (hU : IsOpen U)
    (hharm : ∀ y ∈ U, euclideanCoordLaplacian u y = 0)
    {x : Vec d} (hx : x ∈ U) (i : Fin d) :
    0 ≤ euclideanCoordLaplacian (fun y ↦ (euclideanCoordDeriv i u y) ^ 2) x := by
  rw [euclideanCoordLaplacian_sq (contDiff_euclideanCoordDeriv hu i),
    euclideanCoordLaplacian_euclideanCoordDeriv_eq_zero hu hU hharm hx i, mul_zero, add_zero]
  positivity

/-- Pure one-dimensional radial arithmetic: the normalized weighted integral
of a continuous nonnegative nondecreasing profile is nondecreasing. -/
theorem normalized_radialIntegral_mono [NeZero d]
    {F : ℝ → ℝ} (hF : Continuous F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hFmono : MonotoneOn F (Set.Ioc 0 b)) :
    (d : ℝ) / a ^ d * ∫ t in (0 : ℝ)..a, t ^ (d - 1) * F t ≤
      (d : ℝ) / b ^ d * ∫ t in (0 : ℝ)..b, t ^ (d - 1) * F t := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hb : 0 < b := ha.trans_le hab
  have hpowCont : Continuous (fun t : ℝ ↦ t ^ (d - 1)) := continuous_pow _
  have hIntCont : Continuous (fun t : ℝ ↦ t ^ (d - 1) * F t) := hpowCont.mul hF
  have hIa : ∫ t in (0 : ℝ)..a, t ^ (d - 1) * F t ≤ F a * (a ^ d / d) := by
    calc
      ∫ t in (0 : ℝ)..a, t ^ (d - 1) * F t ≤
          ∫ t in (0 : ℝ)..a, t ^ (d - 1) * F a := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo ha.le
          (hIntCont.intervalIntegrable 0 a)
          ((hpowCont.mul continuous_const).intervalIntegrable 0 a)
        intro t ht
        exact mul_le_mul_of_nonneg_left
          (hFmono ⟨ht.1, ht.2.le.trans hab⟩ ⟨ha, hab⟩ ht.2.le) (pow_nonneg ht.1.le _)
      _ = F a * (a ^ d / d) := by
        rw [intervalIntegral.integral_mul_const, integral_pow]
        simp only [zero_pow (NeZero.ne d), Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)), Nat.cast_sub
          (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)), Nat.cast_one]
        ring
  have hJ : F a * ((b ^ d - a ^ d) / d) ≤
      ∫ t in a..b, t ^ (d - 1) * F t := by
    calc
      F a * ((b ^ d - a ^ d) / d) =
          ∫ t in a..b, t ^ (d - 1) * F a := by
        rw [intervalIntegral.integral_mul_const, integral_pow]
        simp only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)),
          Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)), Nat.cast_one]
        ring
      _ ≤ ∫ t in a..b, t ^ (d - 1) * F t := by
        apply intervalIntegral.integral_mono_on hab
          ((hpowCont.mul continuous_const).intervalIntegrable a b)
          (hIntCont.intervalIntegrable a b)
        intro t ht
        exact mul_le_mul_of_nonneg_left
          (hFmono ⟨ha, hab⟩ ⟨ha.trans_le ht.1, ht.2⟩ ht.1)
          (pow_nonneg (ha.le.trans ht.1) _)
  have hsplit : ∫ t in (0 : ℝ)..b, t ^ (d - 1) * F t =
      (∫ t in (0 : ℝ)..a, t ^ (d - 1) * F t) +
        ∫ t in a..b, t ^ (d - 1) * F t := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hIntCont.intervalIntegrable 0 a) (hIntCont.intervalIntegrable a b)).symm
  have haPow : 0 < a ^ d := pow_pos ha d
  have hbPow : 0 < b ^ d := pow_pos hb d
  have hgap : 0 ≤ b ^ d - a ^ d :=
    sub_nonneg.mpr (pow_le_pow_left₀ ha.le hab d)
  have hkey : (b ^ d - a ^ d) *
      (∫ t in (0 : ℝ)..a, t ^ (d - 1) * F t) ≤
        a ^ d * ∫ t in a..b, t ^ (d - 1) * F t := by
    calc
      _ ≤ (b ^ d - a ^ d) * (F a * (a ^ d / d)) :=
        mul_le_mul_of_nonneg_left hIa hgap
      _ = a ^ d * (F a * ((b ^ d - a ^ d) / d)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hJ haPow.le
  rw [hsplit]
  field_simp
  nlinarith only [hkey]

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- Polar decomposition of an integral over a Euclidean ball, normalized only
at the sphere level. -/
theorem integral_metricBall_eq_sphereMeasure_mul_radialSphereAverage [NeZero d]
    {u : 𝔼 → ℝ} (hu : Continuous u) (x : 𝔼) {r : ℝ} (hr : 0 < r) :
    ∫ y in Metric.ball x r, u y =
      (sphereMeasure d).real Set.univ *
        ∫ s in (0 : ℝ)..r, s ^ (d - 1) * sphereAverage x s u := by
  classical
  set G : 𝔼 → ℝ :=
    fun z ↦ Set.indicator (Metric.ball (0 : 𝔼) r) (fun w ↦ u (x + w)) z with hG
  have hGint : Integrable G := by
    rw [hG]
    exact ((hu.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : 𝔼) r) |>.mono_set Metric.ball_subset_closedBall)
        |>.integrable_indicator measurableSet_ball
  have htrans : ∫ z, G z = ∫ y in Metric.ball x r, u y := by
    have h := integral_add_left_eq_self (μ := (volume : Measure 𝔼))
      (fun y : 𝔼 ↦ Set.indicator (Metric.ball x r) u y) x
    have hfun : (fun y : 𝔼 ↦ Set.indicator (Metric.ball x r) u (x + y)) = G := by
      funext y
      change Set.indicator (Metric.ball x r) u (x + y) =
        Set.indicator (Metric.ball 0 r) (fun w ↦ u (x + w)) y
      by_cases hy : y ∈ Metric.ball 0 r
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem]
        simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, add_sub_cancel_left, sub_zero]
          using hy
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem]
        simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, add_sub_cancel_left, sub_zero]
          using hy
    rw [hfun] at h
    simpa only [MeasureTheory.integral_indicator measurableSet_ball] using h
  have hpolar := integral_eq_integral_Ioi_sphere (G := G) hGint
  have hinner : ∀ s ∈ Set.Ioi (0 : ℝ),
      ∫ ω, G (s • (ω : 𝔼)) ∂(sphereMeasure d) =
        Set.indicator (Set.Iio r)
          (fun t ↦ (sphereMeasure d).real Set.univ * sphereAverage x t u) s := by
    intro s hs
    by_cases hsr : s < r
    · rw [Set.indicator_of_mem (show s ∈ Set.Iio r from hsr)]
      have hmem : ∀ ω : Metric.sphere (0 : 𝔼) 1,
          s • (ω : 𝔼) ∈ Metric.ball 0 r := by
        intro ω
        rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos hs, mem_sphere_zero_iff_norm.mp ω.2, mul_one]
        exact hsr
      have hfun : (fun ω : Metric.sphere (0 : 𝔼) 1 ↦ G (s • (ω : 𝔼))) =
          fun ω : Metric.sphere (0 : 𝔼) 1 ↦ u (x + s • (ω : 𝔼)) := by
        funext ω
        change Set.indicator (Metric.ball 0 r) (fun w ↦ u (x + w)) (s • (ω : 𝔼)) = _
        rw [Set.indicator_of_mem (hmem ω)]
      rw [hfun, integral_sphere_eq_measureReal_smul_sphereAverage, smul_eq_mul]
    · rw [Set.indicator_of_notMem (show s ∉ Set.Iio r from hsr)]
      have hnotmem : ∀ ω : Metric.sphere (0 : 𝔼) 1,
          s • (ω : 𝔼) ∉ Metric.ball 0 r := by
        intro ω hmem
        rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos hs, mem_sphere_zero_iff_norm.mp ω.2, mul_one] at hmem
        exact hsr hmem
      simp only [hG, Set.indicator_of_notMem (hnotmem _), integral_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs ↦ by rw [hinner s hs])] at hpolar
  have hcollapse :
      ∫ s in Set.Ioi (0 : ℝ),
        s ^ (d - 1) • Set.indicator (Set.Iio r)
          (fun t ↦ (sphereMeasure d).real Set.univ * sphereAverage x t u) s =
      (sphereMeasure d).real Set.univ *
        ∫ s in (0 : ℝ)..r, s ^ (d - 1) * sphereAverage x s u := by
    rw [intervalIntegral.integral_of_le hr.le]
    rw [← integral_const_mul]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    have haene : ∀ᵐ s : ℝ ∂volume, s ≠ r := by simp [ae_iff, measure_singleton]
    filter_upwards [haene] with s hsrne
    by_cases hs0 : 0 < s
    · by_cases hsr : s < r
      · rw [Set.indicator_of_mem (show s ∈ Set.Ioc 0 r from ⟨hs0, hsr.le⟩),
          Set.indicator_of_mem (show s ∈ Set.Ioi 0 from hs0),
          Set.indicator_of_mem (show s ∈ Set.Iio r from hsr), smul_eq_mul]
        ring
      · have hrs : r < s := lt_of_le_of_ne (le_of_not_gt hsr) (Ne.symm hsrne)
        rw [Set.indicator_of_notMem (show s ∉ Set.Ioc 0 r from fun hmem ↦
              (not_lt_of_ge hmem.2) hrs),
          Set.indicator_of_mem (show s ∈ Set.Ioi 0 from hs0),
          Set.indicator_of_notMem (show s ∉ Set.Iio r from hsr)]
        simp
    · rw [Set.indicator_of_notMem (show s ∉ Set.Ioc 0 r from fun hmem ↦ hs0 hmem.1),
        Set.indicator_of_notMem (show s ∉ Set.Ioi 0 from hs0)]
  rw [hcollapse] at hpolar
  rw [← htrans, hpolar]

/-- The real volume of a Euclidean ball, expressed with the surface measure
normalization used by `sphereAverage`. -/
theorem volume_metricBall_toReal_eq_sphereMeasure_mul_pow_div [NeZero d]
    (x : 𝔼) {r : ℝ} (hr : 0 < r) :
    (volume (Metric.ball x r)).toReal =
      (sphereMeasure d).real Set.univ * (r ^ d / d) := by
  have hpolar := integral_metricBall_eq_sphereMeasure_mul_radialSphereAverage
    (d := d) (u := fun _ : 𝔼 ↦ (1 : ℝ)) continuous_const x hr
  simp only [integral_const, smul_eq_mul, mul_one,
    measureReal_restrict_apply_univ] at hpolar
  simp_rw [sphereAverage_const] at hpolar
  simp only [mul_one] at hpolar
  rw [integral_pow] at hpolar
  simp only [zero_pow (NeZero.ne d), Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)), Nat.cast_sub
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)), Nat.cast_one, sub_zero] at hpolar
  simpa [Measure.real] using hpolar

/-- Polar representation of the volume-normalized average on a Euclidean
ball.  The sphere-area constant cancels exactly. -/
theorem normalizedIntegral_metricBall_eq_radialSphereAverage [NeZero d]
    {u : 𝔼 → ℝ} (hu : Continuous u) (x : 𝔼) {r : ℝ} (hr : 0 < r) :
    (volume (Metric.ball x r)).toReal⁻¹ * ∫ y in Metric.ball x r, u y =
      (d : ℝ) / r ^ d *
        ∫ s in (0 : ℝ)..r, s ^ (d - 1) * sphereAverage x s u := by
  rw [integral_metricBall_eq_sphereMeasure_mul_radialSphereAverage hu x hr,
    volume_metricBall_toReal_eq_sphereMeasure_mul_pow_div x hr]
  have hσ : (sphereMeasure d).real Set.univ ≠ 0 := sphereMeasure_real_univ_ne_zero
  have hrpow : r ^ d ≠ 0 := pow_ne_zero d hr.ne'
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  field_simp

open scoped Laplacian

/-- The volume-normalized ball average of a smooth subharmonic function is
nondecreasing with the radius.  This is the constant-one submean comparison
needed by the Schauder iteration. -/
theorem normalizedIntegral_metricBall_mono_of_laplacian_nonneg [NeZero d]
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u) {x : 𝔼} {R : ℝ}
    (hlap : ∀ y ∈ Metric.ball x R, 0 ≤ Δ u y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) :
    (volume (Metric.ball x a)).toReal⁻¹ * ∫ y in Metric.ball x a, u y ≤
      (volume (Metric.ball x b)).toReal⁻¹ * ∫ y in Metric.ball x b, u y := by
  rw [normalizedIntegral_metricBall_eq_radialSphereAverage hu.continuous x ha,
    normalizedIntegral_metricBall_eq_radialSphereAverage hu.continuous x
      (ha.trans_le hab)]
  apply normalized_radialIntegral_mono (continuous_sphereAverage hu.continuous x) ha hab
  intro s hs t ht hst
  exact sphereAverage_mono_of_laplacian_nonneg hu hlap hs.1 hst
    (ht.2.trans_lt hbR)

/-- Constant-one normalized ball comparison for one squared coordinate of the
gradient of a smooth coordinate-harmonic function. -/
theorem normalizedIntegral_sq_euclideanCoordDeriv_mono [NeZero d]
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {z : Vec d} {R : ℝ} (hR : 0 < R)
    (hharm : ∀ y ∈ euclideanBall z R, euclideanCoordLaplacian u y = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) (i : Fin d) :
    (volume (Metric.ball (toEuc z) a)).toReal⁻¹ *
        ∫ y in Metric.ball (toEuc z) a,
          (euclideanCoordDeriv i u (toEuc.symm y)) ^ 2 ≤
      (volume (Metric.ball (toEuc z) b)).toReal⁻¹ *
        ∫ y in Metric.ball (toEuc z) b,
          (euclideanCoordDeriv i u (toEuc.symm y)) ^ 2 := by
  let q : Vec d → ℝ := fun y ↦ (euclideanCoordDeriv i u y) ^ 2
  have hq : ContDiff ℝ (⊤ : ℕ∞) q :=
    (contDiff_euclideanCoordDeriv hu i).pow 2
  have hlap : ∀ y ∈ Metric.ball (toEuc z) R, 0 ≤ Δ (q ∘ toEuc.symm) y := by
    intro y hy
    rw [← euclideanCoordLaplacian_eq_laplacian_comp_toEuc_symm
      (hq.of_le (by
        change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top))]
    apply euclideanCoordLaplacian_sq_euclideanCoordDeriv_nonneg hu
      (isOpen_euclideanBall z R) hharm
    exact (mem_euclideanBall_toEuc_iff (toEuc.symm y) z hR).mp (by simpa using hy)
  exact normalizedIntegral_metricBall_mono_of_laplacian_nonneg
    ((hq.comp toEuc.symm.contDiff).of_le
      (by
        change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top))
    hlap ha hab hbR

/-- The smooth constant-one comparison after summing all gradient
coordinates. -/
theorem normalizedIntegral_vecNormSq_euclideanGradient_mono [NeZero d]
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {z : Vec d} {R : ℝ} (hR : 0 < R)
    (hharm : ∀ y ∈ euclideanBall z R, euclideanCoordLaplacian u y = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) :
    (volume (Metric.ball (toEuc z) a)).toReal⁻¹ *
        ∫ y in Metric.ball (toEuc z) a,
          vecNormSq (euclideanGradient u (toEuc.symm y)) ≤
      (volume (Metric.ball (toEuc z) b)).toReal⁻¹ *
        ∫ y in Metric.ball (toEuc z) b,
          vecNormSq (euclideanGradient u (toEuc.symm y)) := by
  classical
  let q : Fin d → 𝔼 → ℝ := fun i y ↦
    (euclideanCoordDeriv i u (toEuc.symm y)) ^ 2
  have hqcont : ∀ i, Continuous (q i) := fun i ↦
    (((contDiff_euclideanCoordDeriv hu i).comp toEuc.symm.contDiff).pow 2).continuous
  have hqint : ∀ i r, Integrable (q i) (volume.restrict (Metric.ball (toEuc z) r)) := by
    intro i r
    exact ((hqcont i).continuousOn.integrableOn_compact
      (isCompact_closedBall (toEuc z) r) |>.mono_set Metric.ball_subset_closedBall)
  have hsum :
      ∑ i : Fin d,
          (volume (Metric.ball (toEuc z) a)).toReal⁻¹ *
            ∫ y in Metric.ball (toEuc z) a, q i y ≤
        ∑ i : Fin d,
          (volume (Metric.ball (toEuc z) b)).toReal⁻¹ *
            ∫ y in Metric.ball (toEuc z) b, q i y := by
    apply Finset.sum_le_sum
    intro i _
    exact normalizedIntegral_sq_euclideanCoordDeriv_mono hu hR hharm ha hab hbR i
  have hpoint : ∀ y : 𝔼,
      vecNormSq (euclideanGradient u (toEuc.symm y)) = ∑ i : Fin d, q i y := by
    intro y
    simp only [q, vecNormSq, vecDot, euclideanGradient, pow_two]
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hqint i a),
    integral_finsetSum Finset.univ (fun i _ ↦ hqint i b),
    Finset.mul_sum, Finset.mul_sum]
  exact hsum

/-- The measure-preserving coordinate dictionary for normalized smooth
gradient energy on a Euclidean ball. -/
theorem volumeAverage_vecNormSq_euclideanGradient_euclideanBall_eq
    (v : Vec d → ℝ) (z : Vec d) {r : ℝ} (hr : 0 < r) :
    volumeAverage (euclideanBall z r) (fun x ↦ vecNormSq (euclideanGradient v x)) =
      (volume (Metric.ball (toEuc z) r)).toReal⁻¹ *
        ∫ y in Metric.ball (toEuc z) r,
          vecNormSq (euclideanGradient v (toEuc.symm y)) := by
  have hpre : toEuc ⁻¹' Metric.ball (toEuc z) r = euclideanBall z r := by
    simpa using preimage_ball_toEuc (toEuc z) hr
  have hvol : volume (euclideanBall z r) = volume (Metric.ball (toEuc z) r) := by
    rw [← hpre, (measurePreserving_toEuc d).measure_preimage
      measurableSet_ball.nullMeasurableSet]
  have hint :
      ∫ x in euclideanBall z r, vecNormSq (euclideanGradient v x) =
        ∫ y in Metric.ball (toEuc z) r,
          vecNormSq (euclideanGradient v (toEuc.symm y)) := by
    rw [← hpre]
    have h := (measurePreserving_toEuc d).setIntegral_preimage_emb
      (measurableEmbedding_toEuc d)
      (fun y : 𝔼 ↦ vecNormSq (euclideanGradient v (toEuc.symm y)))
      (Metric.ball (toEuc z) r)
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
  unfold volumeAverage
  rw [hvol, hint]

/-- Constant-one normalized energy comparison for a globally smooth
coordinate-harmonic function. -/
theorem volumeAverage_vecNormSq_euclideanGradient_mono [NeZero d]
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {z : Vec d} {R : ℝ} (hR : 0 < R)
    (hharm : ∀ y ∈ euclideanBall z R, euclideanCoordLaplacian u y = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) :
    volumeAverage (euclideanBall z a) (fun x ↦ vecNormSq (euclideanGradient u x)) ≤
      volumeAverage (euclideanBall z b) (fun x ↦ vecNormSq (euclideanGradient u x)) := by
  rw [volumeAverage_vecNormSq_euclideanGradient_euclideanBall_eq u z ha,
    volumeAverage_vecNormSq_euclideanGradient_euclideanBall_eq u z (ha.trans_le hab)]
  exact normalizedIntegral_vecNormSq_euclideanGradient_mono hu hR hharm ha hab hbR

/-- Constant-one comparison for the weak gradient, with the outer comparison
radius strictly inside the weak-harmonicity ball. -/
theorem volumeAverage_vecNormSq_grad_mono_euclideanBall_lt [NeZero d]
    {z : Vec d} {R : ℝ} (hR : 0 < R)
    (h : H1Function (euclideanBall z R))
    (hh : IsUnitWeaklyHarmonicOn (euclideanBall z R) h)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) :
    volumeAverage (euclideanBall z a) (fun x ↦ vecNormSq (h.grad x)) ≤
      volumeAverage (euclideanBall z b) (fun x ↦ vecNormSq (h.grad x)) := by
  let c : ℝ := (b + R) / 2
  have hb : 0 < b := ha.trans_le hab
  have hbc : b < c := by dsimp [c]; linarith only [hbR]
  have hcR : c < R := by dsimp [c]; linarith only [hbR]
  have hc : 0 < c := hb.trans hbc
  let gap : ℝ := R - c
  have hgap : 0 < gap := by dsimp [gap]; linarith only [hcR]
  let eps : ℝ := gap / (2 * ((d : ℝ) + 1))
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hW : euclideanBall z c ⊆ innerRegion (euclideanBall z R) eps := by
    intro p hp q hq
    have hqp : q ∈ euclideanBall p gap := by
      apply HCPolySupport.metricClosedBall_div_two_natCast_succ_subset_euclideanBall hgap
      simpa only [eps]
    have hqpE : toEuc q ∈ Metric.ball (toEuc p) gap :=
      (mem_euclideanBall_toEuc_iff q p hgap).2 hqp
    have hpE : toEuc p ∈ Metric.ball (toEuc z) c :=
      (mem_euclideanBall_toEuc_iff p z hc).2 hp
    apply (mem_euclideanBall_toEuc_iff q z hR).1
    rw [Metric.mem_ball] at hqpE hpE ⊢
    calc
      dist (toEuc q) (toEuc z) ≤
          dist (toEuc q) (toEuc p) + dist (toEuc p) (toEuc z) := dist_triangle _ _ _
      _ < gap + c := add_lt_add hqpE hpE
      _ = R := by dsimp [gap]; ring
  obtain ⟨v, hv, hvharm, hvae⟩ := exists_harmonicRepresentative_on
    (isOpen_euclideanBall z R) hh heps
    (isOpen_euclideanBall z c).measurableSet hW
  have hvzero : ∀ y ∈ euclideanBall z c, euclideanCoordLaplacian v y = 0 := by
    intro y hy
    have hzero := (hvharm (toEuc y) ⟨y, hy, rfl⟩).2.self_of_nhds
    rw [← laplacian_comp_toEuc_symm_apply
      (hv.of_le (by
        change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top))]
    simpa using hzero
  let finiteVolumeInnerBall := Book.Ch01.isFiniteMeasure_volumeMeasureOn_euclideanBall z c
  have hvgrad : euclideanGradient v =ᵐ[volume.restrict (euclideanBall z c)] h.grad :=
    ae_eq_euclideanGradient_of_ae_eq_of_contDiff
      (isOpen_euclideanBall z c)
      (euclideanBall_subset_euclideanBall hc.le hcR) h
      (hv.of_le (by
        change (↑(1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)) hvae
  have hsuba : euclideanBall z a ⊆ euclideanBall z c :=
    euclideanBall_subset_euclideanBall ha.le (hab.trans_lt hbc)
  have hsubb : euclideanBall z b ⊆ euclideanBall z c :=
    euclideanBall_subset_euclideanBall hb.le hbc
  have hvgrada := hvgrad.filter_mono
    (ae_mono (Measure.restrict_mono hsuba le_rfl))
  have hvgradb := hvgrad.filter_mono
    (ae_mono (Measure.restrict_mono hsubb le_rfl))
  have heqa : volumeAverage (euclideanBall z a)
      (fun x ↦ vecNormSq (euclideanGradient v x)) =
      volumeAverage (euclideanBall z a) (fun x ↦ vecNormSq (h.grad x)) := by
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    exact hvgrada.mono fun x hx ↦ congrArg vecNormSq hx
  have heqb : volumeAverage (euclideanBall z b)
      (fun x ↦ vecNormSq (euclideanGradient v x)) =
      volumeAverage (euclideanBall z b) (fun x ↦ vecNormSq (h.grad x)) := by
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    exact hvgradb.mono fun x hx ↦ congrArg vecNormSq hx
  rw [← heqa, ← heqb]
  exact volumeAverage_vecNormSq_euclideanGradient_mono hv hc hvzero ha hab hbc

/-- Exact real volume of the project-carrier Euclidean ball, in the same
surface-area normalization as the polar formula. -/
theorem volume_euclideanBall_toReal_eq_sphereMeasure_mul_pow_div [NeZero d]
    (z : Vec d) {r : ℝ} (hr : 0 < r) :
    (volume (euclideanBall z r)).toReal =
      (sphereMeasure d).real Set.univ * (r ^ d / d) := by
  have hpre : toEuc ⁻¹' Metric.ball (toEuc z) r = euclideanBall z r := by
    simpa using preimage_ball_toEuc (toEuc z) hr
  have hvol : volume (euclideanBall z r) = volume (Metric.ball (toEuc z) r) := by
    rw [← hpre, (measurePreserving_toEuc d).measure_preimage
      measurableSet_ball.nullMeasurableSet]
  rw [hvol, volume_metricBall_toReal_eq_sphereMeasure_mul_pow_div (toEuc z) hr]

/-- The weak-gradient normalized energy comparison including the outer
radius.  The endpoint is obtained from the strict comparison and exact ball
volume continuity; no interior-estimate constant is spent. -/
theorem volumeAverage_vecNormSq_grad_mono_euclideanBall [NeZero d]
    {z : Vec d} {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (hsR : s ≤ R)
    (h : H1Function (euclideanBall z R))
    (hh : IsUnitWeaklyHarmonicOn (euclideanBall z R) h) :
    volumeAverage (euclideanBall z s) (fun x ↦ vecNormSq (h.grad x)) ≤
      volumeAverage (euclideanBall z R) (fun x ↦ vecNormSq (h.grad x)) := by
  rcases hsR.eq_or_lt with rfl | hsRlt
  · exact le_rfl
  let A : ℝ := volumeAverage (euclideanBall z s) (fun x ↦ vecNormSq (h.grad x))
  let I : ℝ := ∫ x in euclideanBall z R, vecNormSq (h.grad x)
  let σ : ℝ := (sphereMeasure d).real Set.univ
  have hRvol : 0 < (volume (euclideanBall z R)).toReal :=
    ENNReal.toReal_pos
      (ne_of_gt ((isOpen_euclideanBall z R).measure_pos volume
        (euclideanBall_nonempty z hR)))
      (Book.Ch01.volume_euclideanBall_ne_top z R)
  apply (le_inv_mul_iff₀ hRvol).2
  change (volume (euclideanBall z R)).toReal * A ≤ I
  rw [mul_comm]
  have hlim : Filter.Tendsto (fun t : ℝ ↦ A * (σ * (t ^ d / d)))
      (nhdsWithin R (Set.Iio R)) (nhds (A * (volume (euclideanBall z R)).toReal)) := by
    have hcont : ContinuousAt (fun t : ℝ ↦ A * (σ * (t ^ d / d))) R :=
      continuousAt_const.mul
        (continuousAt_const.mul ((continuousAt_id.pow d).div_const (d : ℝ)))
    have ht := hcont.tendsto.mono_left
      (show nhdsWithin R (Set.Iio R) ≤ nhds R from inf_le_left)
    rw [volume_euclideanBall_toReal_eq_sphereMeasure_mul_pow_div z hR]
    exact ht
  apply le_of_tendsto hlim
  have hslt : ∀ᶠ t in nhdsWithin R (Set.Iio R), s < t :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.2
      ⟨Set.Ioi s, Ioi_mem_nhds hsRlt, Set.inter_subset_left⟩
  have htR : ∀ᶠ t in nhdsWithin R (Set.Iio R), t < R := self_mem_nhdsWithin
  filter_upwards [hslt, htR] with t hst htR'
  have ht : 0 < t := hs.trans hst
  have havg := volumeAverage_vecNormSq_grad_mono_euclideanBall_lt
    hR h hh hs hst.le htR'
  have htvol : 0 < (volume (euclideanBall z t)).toReal :=
    ENNReal.toReal_pos
      (ne_of_gt ((isOpen_euclideanBall z t).measure_pos volume
        (euclideanBall_nonempty z ht)))
      (Book.Ch01.volume_euclideanBall_ne_top z t)
  have hscaled : A * (volume (euclideanBall z t)).toReal ≤
      ∫ x in euclideanBall z t, vecNormSq (h.grad x) := by
    have hvA := (le_inv_mul_iff₀ htvol).1
      (show A ≤ (volume (euclideanBall z t)).toReal⁻¹ *
        ∫ x in euclideanBall z t, vecNormSq (h.grad x) by
          simpa only [A, volumeAverage] using havg)
    simpa only [mul_comm] using hvA
  have hsub : euclideanBall z t ⊆ euclideanBall z R :=
    euclideanBall_subset_euclideanBall ht.le htR'
  have hmono : ∫ x in euclideanBall z t, vecNormSq (h.grad x) ≤ I := by
    dsimp only [I]
    apply setIntegral_mono_set (integrableOn_vecNormSq_h1Grad h)
    · exact Filter.Eventually.of_forall fun x ↦ vecNormSq_nonneg _
    · exact Filter.Eventually.of_forall hsub
  rw [volume_euclideanBall_toReal_eq_sphereMeasure_mul_pow_div z ht] at hscaled
  exact hscaled.trans hmono

/-- The manuscript-facing constant-one concentric-ball comparison for the
normalized `L²` norm of the weak harmonic gradient. -/
theorem vectorNormalizedL2On_grad_mono_euclideanBall [NeZero d]
    {z : Vec d} {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (hsR : s ≤ R)
    (h : H1Function (euclideanBall z R))
    (hh : IsUnitWeaklyHarmonicOn (euclideanBall z R) h) :
    vectorNormalizedL2On (euclideanBall z s) h.grad ≤
      vectorNormalizedL2On (euclideanBall z R) h.grad := by
  have havg := volumeAverage_vecNormSq_grad_mono_euclideanBall hR hs hsR h hh
  unfold vectorNormalizedL2On normalizedL2On
  simpa only [euclideanNorm_sq] using Real.sqrt_le_sqrt havg

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
