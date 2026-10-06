/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureDualityPotentialEstimates
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.Neighborhoods
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball

/-!
# Noncompact potential tests for space-time pressure

The compact distributional identity extends first to arbitrary input classes
and then to decaying potential tests by spatial cutoff and dominated convergence.
-/

public section

open MeasureTheory
open scoped ENNReal
open scoped Topology
open CKN.Foundation.Parabolic
open Filter

noncomputable section

namespace CKN.Leray

private theorem rieszPressureComponent_laplacian_pairing_compact
    (r : ℝ) (hr : 1 < r) (q : ℝ) (hq : 1 < q)
    (hHolder : r.HolderConjugate q) (i j : Fin 3)
    (u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)))
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ z, (rieszPressureSpaceTimeComponent r hr i j u :
      Vec3 × ℝ → ℝ) z * rieszPressureJointLaplacian ψ z =
      -∫ z, (u : Vec3 × ℝ → ℝ) z * rieszPressureJointHessian ψ i j z := by
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq.le⟩
  let : (ENNReal.ofReal r).HolderConjugate (ENNReal.ofReal q) :=
    Real.HolderConjugate.ennrealOfReal hHolder
  have hLapC : Continuous (rieszPressureJointLaplacian ψ) :=
    (rieszPressureJointLaplacian_contDiff hψ).continuous
  have hHessC : Continuous (rieszPressureJointHessian ψ i j) :=
    (rieszPressureJointHessian_contDiff hψ i j).continuous
  have hLapMem : MemLp (rieszPressureJointLaplacian ψ) (ENNReal.ofReal q)
      (volume : Measure (Vec3 × ℝ)) :=
    hLapC.memLp_of_hasCompactSupport
      (rieszPressureJointLaplacian_hasCompactSupport hψc)
  have hHessMem : MemLp (rieszPressureJointHessian ψ i j) (ENNReal.ofReal q)
      (volume : Measure (Vec3 × ℝ)) :=
    hHessC.memLp_of_hasCompactSupport
      (rieszPressureJointHessian_hasCompactSupport hψc i j)
  let vLap := hLapMem.toLp (rieszPressureJointLaplacian ψ)
  let vHess := hHessMem.toLp (rieszPressureJointHessian ψ i j)
  let T := rieszPressureSpaceTimeComponent r hr i j
  let A : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) →L[ℝ] ℝ :=
    (rieszPressureLpPairingCLM r hr q hq hHolder vLap).comp T
  let B : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) →L[ℝ] ℝ :=
    -(rieszPressureLpPairingCLM r hr q hq hHolder vHess)
  have hClosed : IsClosed {w | A w = B w} := isClosed_eq A.continuous B.continuous
  have hOnCore : ∀ w : rieszPressureSpaceTimeCore r hr, A w = B w := by
    intro w
    rcases w.property with ⟨G, hG⟩
    have hGmem : MemLp G.value (ENNReal.ofReal r)
        (volume : Measure (Vec3 × ℝ)) :=
      G.continuous_value.memLp_of_hasCompactSupport G.compact_support_value
    have hGclass : (w : Lp ℝ (ENNReal.ofReal r)
        (volume : Measure (Vec3 × ℝ))) = hGmem.toLp G.value := by
      simpa only [rieszPressureCompactInputLpClass] using hG
    have hwG : (w : Vec3 × ℝ → ℝ) =ᵐ[volume] G.value := by
      filter_upwards [(Lp.ext_iff).1 hGclass, hGmem.coeFn_toLp] with z hw hGz
      exact hw.trans hGz
    have hTcompact := rieszPressureSpaceTimeComponent_eq_compact r hr i j
      G.continuous_value G.compact_support_value
    have hT : T (w : Lp ℝ (ENNReal.ofReal r)
        (volume : Measure (Vec3 × ℝ))) =
        rieszPressureComponentCompactClass r hr i j (F := G.value)
          G.continuous_value G.compact_support_value := by
      rw [hGclass]
      exact hTcompact
    have hTae : (T (w : Lp ℝ (ENNReal.ofReal r)
        (volume : Measure (Vec3 × ℝ))) : Vec3 × ℝ → ℝ) =ᵐ[volume]
        (rieszPressureComponentCompactClass r hr i j (F := G.value)
          G.continuous_value G.compact_support_value : Vec3 × ℝ → ℝ) :=
      (Lp.ext_iff).1 hT
    have hCompact := rieszPressureComponentCompactClass_laplacian_pairing
      r hr q hHolder i j G.continuous_value G.compact_support_value hψ hψc
    have hAeval : A w = ∫ z,
        (rieszPressureComponentCompactClass r hr i j (F := G.value)
          G.continuous_value G.compact_support_value : Vec3 × ℝ → ℝ) z *
          rieszPressureJointLaplacian ψ z := by
      change rieszPressureLpPairingCLM r hr q hq hHolder vLap (T w) = _
      rw [rieszPressureLpPairingCLM_apply]
      apply integral_congr_ae
      filter_upwards [hTae, hLapMem.coeFn_toLp] with z hTz hLapz
      rw [hTz, hLapz]
    have hBeval : B w = -∫ z, G.value z *
        rieszPressureJointHessian ψ i j z := by
      change -(rieszPressureLpPairingCLM r hr q hq hHolder vHess w) = _
      rw [rieszPressureLpPairingCLM_apply]
      congr 1
      apply integral_congr_ae
      filter_upwards [hwG, hHessMem.coeFn_toLp] with z hwz hHessz
      rw [hwz, hHessz]
    rw [hAeval, hBeval]
    exact hCompact
  have hEq : A u = B u := by
    apply isClosed_property
      (denseRange_subtype_val.mpr (rieszPressureSpaceTimeCore_dense r hr)) hClosed
    rintro ⟨w, hw⟩
    exact hOnCore ⟨w, hw⟩
  have hAeval : A u = ∫ z,
      (rieszPressureSpaceTimeComponent r hr i j u : Vec3 × ℝ → ℝ) z *
        rieszPressureJointLaplacian ψ z := by
    change rieszPressureLpPairingCLM r hr q hq hHolder vLap (T u) = _
    rw [rieszPressureLpPairingCLM_apply]
    apply integral_congr_ae
    filter_upwards [hLapMem.coeFn_toLp] with z hLapz
    rw [hLapz]
  have hBeval : B u = -∫ z, (u : Vec3 × ℝ → ℝ) z *
      rieszPressureJointHessian ψ i j z := by
    change -(rieszPressureLpPairingCLM r hr q hq hHolder vHess u) = _
    rw [rieszPressureLpPairingCLM_apply]
    congr 1
    apply integral_congr_ae
    filter_upwards [hHessMem.coeFn_toLp] with z hHessz
    rw [hHessz]
  calc
    _ = A u := hAeval.symm
    _ = B u := hEq
    _ = _ := hBeval

private theorem rieszPressurePotentialCutoffTest_hessian_eventually_eq
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i j : Fin 3) (z : Vec3 × ℝ) :
    ∀ᶠ n : ℕ in atTop,
      rieszPressureJointHessian (rieszPressurePotentialCutoffTest ψ n) i j z =
        rieszPressureJointHessian ψ i j z := by
  obtain ⟨N, hN⟩ := exists_nat_gt (CKN.vecEuclideanNorm z.1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnorm : CKN.vecEuclideanNorm z.1 < rieszPressurePotentialCutoffScale n := by
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
    (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      hscaleNonneg).2 (by simpa using (le_of_lt hnorm))
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
    rw [fderiv_apply (hgradSmooth.differentiable (by norm_num) z.1) l,
      hderivs.2]
    rfl
  rw [rieszPressurePotentialCutoffTest_hessian_formula hψ n i j z]
  rw [heta, hgrad i, hgrad j, hhess i j]
  ring

private theorem rieszPressurePotentialCutoffTest_laplacian_eventually_eq
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : Vec3 × ℝ) :
    ∀ᶠ n : ℕ in atTop,
      rieszPressureJointLaplacian (rieszPressurePotentialCutoffTest ψ n) z =
        rieszPressureJointLaplacian ψ z := by
  obtain ⟨N, hN⟩ := exists_nat_gt (CKN.vecEuclideanNorm z.1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnorm : CKN.vecEuclideanNorm z.1 < rieszPressurePotentialCutoffScale n := by
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
    (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      hscaleNonneg).2 (by simpa using (le_of_lt hnorm))
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
    rw [fderiv_apply (hgradSmooth.differentiable (by norm_num) z.1) l,
      hderivs.2]
    rfl
  have hlap : CKN.spatialLaplacian (rieszPressurePotentialCutoff n) z.1 = 0 := by
    rw [CKN.spatialLaplacian]
    apply Finset.sum_eq_zero
    intro k hk
    exact hhess k k
  rw [rieszPressurePotentialCutoffTest_laplacian_formula hψ n z]
  rw [heta, hlap]
  simp [CKN.spatialGradDot, hgrad]

private theorem rieszPressurePotentialSpatialProfile_nonneg
    (K : Set ℝ) (z : Vec3 × ℝ) :
    0 ≤ rieszPressurePotentialSpatialProfile K z := by
  by_cases ht : z.2 ∈ K
  · simp [rieszPressurePotentialSpatialProfile, ht]
    positivity
  · simp [rieszPressurePotentialSpatialProfile, ht]

private theorem rieszPressurePotentialCutoffTest_hessian_bound
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {K : Set ℝ} (hzero : ∀ t ∉ K, ∀ x, ψ (x, t) = 0)
    (hdecay : RieszPressurePotentialDecay ψ) (i j : Fin 3)
    (n : ℕ) (z : Vec3 × ℝ) :
    |rieszPressureJointHessian (rieszPressurePotentialCutoffTest ψ n) i j z| ≤
      (2 * Classical.choose hdecay.hessian_bound +
        6 * CKN.cutoffGradientConstant * Classical.choose hdecay.gradient_bound +
        9 * CKN.cutoffSecondDerivativeConstant * Classical.choose hdecay.value_bound) *
        rieszPressurePotentialSpatialProfile K z := by
  by_cases ht : z.2 ∈ K
  · have hprofile : rieszPressurePotentialSpatialProfile K z =
        (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
      simp [rieszPressurePotentialSpatialProfile, ht]
    have hsource := rieszPressurePotentialDecay_hessian_bound_norm hdecay i j z
    have herr := rieszPressurePotentialHessianCutoffError_bound
      hψ hzero hdecay i j n z
    have hrelation :
        rieszPressureJointHessian (rieszPressurePotentialCutoffTest ψ n) i j z =
          rieszPressureJointHessian ψ i j z +
            rieszPressurePotentialHessianCutoffError ψ i j n z := by
      simp [rieszPressurePotentialHessianCutoffError]
    rw [hrelation]
    calc
      |rieszPressureJointHessian ψ i j z +
          rieszPressurePotentialHessianCutoffError ψ i j n z| ≤
          |rieszPressureJointHessian ψ i j z| +
            |rieszPressurePotentialHessianCutoffError ψ i j n z| :=
        abs_add_le _ _
      _ ≤ Classical.choose hdecay.hessian_bound *
            rieszPressurePotentialSpatialProfile K z +
          (Classical.choose hdecay.hessian_bound +
            6 * CKN.cutoffGradientConstant * Classical.choose hdecay.gradient_bound +
            9 * CKN.cutoffSecondDerivativeConstant *
              Classical.choose hdecay.value_bound) *
            rieszPressurePotentialSpatialProfile K z := by
        exact add_le_add (by simpa [hprofile] using hsource) herr
      _ = (2 * Classical.choose hdecay.hessian_bound +
            6 * CKN.cutoffGradientConstant * Classical.choose hdecay.gradient_bound +
            9 * CKN.cutoffSecondDerivativeConstant *
              Classical.choose hdecay.value_bound) *
            rieszPressurePotentialSpatialProfile K z := by ring
  · have hsourceSlice : (fun x : Vec3 => ψ (x, z.2)) = fun _ => (0 : ℝ) := by
      funext x
      exact hzero z.2 ht x
    have htestSlice : (fun x : Vec3 =>
        rieszPressurePotentialCutoffTest ψ n (x, z.2)) = fun _ => (0 : ℝ) := by
      funext x
      simp [rieszPressurePotentialCutoffTest, hzero z.2 ht x]
    have htest := rieszPressureJointHessian_zero_of_slice_zero
      (rieszPressurePotentialCutoffTest_contDiff hψ n) htestSlice i j
    simp [htest, rieszPressurePotentialSpatialProfile, ht]

private theorem rieszPressurePotentialCutoffTest_laplacian_bound
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {K : Set ℝ} (hzero : ∀ t ∉ K, ∀ x, ψ (x, t) = 0)
    (hdecay : RieszPressurePotentialDecay ψ) (n : ℕ) (z : Vec3 × ℝ) :
    |rieszPressureJointLaplacian (rieszPressurePotentialCutoffTest ψ n) z| ≤
      (6 * Classical.choose hdecay.hessian_bound +
        18 * CKN.cutoffGradientConstant * Classical.choose hdecay.gradient_bound +
        27 * CKN.cutoffSecondDerivativeConstant * Classical.choose hdecay.value_bound) *
        rieszPressurePotentialSpatialProfile K z := by
  by_cases ht : z.2 ∈ K
  · have hprofile : rieszPressurePotentialSpatialProfile K z =
        (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
      simp [rieszPressurePotentialSpatialProfile, ht]
    have hsource := rieszPressurePotentialDecay_laplacian_bound_norm hdecay z
    have herr := rieszPressurePotentialLaplacianCutoffError_bound
      hψ hzero hdecay n z
    have hrelation :
        rieszPressureJointLaplacian (rieszPressurePotentialCutoffTest ψ n) z =
          rieszPressureJointLaplacian ψ z +
            rieszPressurePotentialLaplacianCutoffError ψ n z := by
      simp [rieszPressurePotentialLaplacianCutoffError]
    rw [hrelation]
    calc
      |rieszPressureJointLaplacian ψ z +
          rieszPressurePotentialLaplacianCutoffError ψ n z| ≤
          |rieszPressureJointLaplacian ψ z| +
            |rieszPressurePotentialLaplacianCutoffError ψ n z| :=
        abs_add_le _ _
      _ ≤ (3 * Classical.choose hdecay.hessian_bound) *
            rieszPressurePotentialSpatialProfile K z +
          (3 * Classical.choose hdecay.hessian_bound +
            18 * CKN.cutoffGradientConstant * Classical.choose hdecay.gradient_bound +
            27 * CKN.cutoffSecondDerivativeConstant *
              Classical.choose hdecay.value_bound) *
            rieszPressurePotentialSpatialProfile K z := by
        exact add_le_add (by simpa [hprofile] using hsource) herr
      _ = (6 * Classical.choose hdecay.hessian_bound +
            18 * CKN.cutoffGradientConstant * Classical.choose hdecay.gradient_bound +
            27 * CKN.cutoffSecondDerivativeConstant *
              Classical.choose hdecay.value_bound) *
            rieszPressurePotentialSpatialProfile K z := by ring
  · have hsourceSlice : (fun x : Vec3 => ψ (x, z.2)) = fun _ => (0 : ℝ) := by
      funext x
      exact hzero z.2 ht x
    have htestSlice : (fun x : Vec3 =>
        rieszPressurePotentialCutoffTest ψ n (x, z.2)) = fun _ => (0 : ℝ) := by
      funext x
      simp [rieszPressurePotentialCutoffTest, hzero z.2 ht x]
    have htest := rieszPressureJointLaplacian_zero_of_slice_zero
      (rieszPressurePotentialCutoffTest_contDiff hψ n) htestSlice
    simp [htest, rieszPressurePotentialSpatialProfile, ht]

private theorem rieszPressurePotentialProfile_integrable_mul
    {K : Set ℝ} (hK : IsCompact K)
    (u : Lp ℝ (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ))) :
    Integrable (fun z : Vec3 × ℝ => ‖(u : Vec3 × ℝ → ℝ) z‖ *
      rieszPressurePotentialSpatialProfile K z)
      (volume : Measure (Vec3 × ℝ)) := by
  let : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
  let : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩
  have hHolder : (3 / 2 : ℝ).HolderConjugate 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
  let : (ENNReal.ofReal (3 / 2 : ℝ)).HolderConjugate
      (ENNReal.ofReal (3 : ℝ)) := Real.HolderConjugate.ennrealOfReal hHolder
  have hprofile := rieszPressurePotentialSpatialProfile_memLp3 hK
  have hproduct := (Lp.memLp u).integrable_mul hprofile
  have hnonneg := fun z => rieszPressurePotentialSpatialProfile_nonneg K z
  have hnorm := hproduct.norm
  apply hnorm.congr
  filter_upwards [] with z
  calc
    ‖((u : Vec3 × ℝ → ℝ) * rieszPressurePotentialSpatialProfile K) z‖ =
        ‖(u : Vec3 × ℝ → ℝ) z‖ *
          ‖rieszPressurePotentialSpatialProfile K z‖ := norm_mul _ _
    _ = ‖(u : Vec3 × ℝ → ℝ) z‖ *
          rieszPressurePotentialSpatialProfile K z := by
      rw [Real.norm_eq_abs (rieszPressurePotentialSpatialProfile K z),
        abs_of_nonneg (hnonneg z)]

private theorem rieszPressureComponent_laplacian_pairing_potential
    (u : Lp ℝ (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)))
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hdecay : RieszPressurePotentialDecay ψ) (i j : Fin 3) :
    ∫ z, (rieszPressureSpaceTimeComponent (3 / 2 : ℝ)
        (by norm_num) i j u : Vec3 × ℝ → ℝ) z *
        rieszPressureJointLaplacian ψ z =
      -∫ z, (u : Vec3 × ℝ → ℝ) z * rieszPressureJointHessian ψ i j z := by
  let r : ℝ := 3 / 2
  let q : ℝ := 3
  have hr : 1 < r := by norm_num [r]
  have hq : 1 < q := by norm_num [q]
  have hHolder : r.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    norm_num [r, q]
  obtain ⟨K, hK, hzero⟩ := hdecay.timeSupport
  let C0 := Classical.choose hdecay.value_bound
  let C1 := Classical.choose hdecay.gradient_bound
  let C2 := Classical.choose hdecay.hessian_bound
  let CL := 6 * C2 + 18 * CKN.cutoffGradientConstant * C1 +
    27 * CKN.cutoffSecondDerivativeConstant * C0
  let CH := 2 * C2 + 6 * CKN.cutoffGradientConstant * C1 +
    9 * CKN.cutoffSecondDerivativeConstant * C0
  let T := rieszPressureSpaceTimeComponent r hr i j
  let p := T u
  have hprofileInt := rieszPressurePotentialProfile_integrable_mul hK p
  have hcutLapBound (n : ℕ) (z : Vec3 × ℝ) :
      |rieszPressureJointLaplacian (rieszPressurePotentialCutoffTest ψ n) z| ≤
        CL * rieszPressurePotentialSpatialProfile K z := by
    simpa [CL, C2, C1, C0] using
      rieszPressurePotentialCutoffTest_laplacian_bound hψ hzero hdecay n z
  have hcutHessBound (n : ℕ) (z : Vec3 × ℝ) :
      |rieszPressureJointHessian (rieszPressurePotentialCutoffTest ψ n) i j z| ≤
        CH * rieszPressurePotentialSpatialProfile K z := by
    simpa [CH, C2, C1, C0] using
      rieszPressurePotentialCutoffTest_hessian_bound hψ hzero hdecay i j n z
  have hLapContinuous (n : ℕ) :
      Continuous (rieszPressureJointLaplacian
        (rieszPressurePotentialCutoffTest ψ n)) :=
    (rieszPressureJointLaplacian_contDiff
      (rieszPressurePotentialCutoffTest_contDiff hψ n)).continuous
  have hHessContinuous (n : ℕ) :
      Continuous (rieszPressureJointHessian
        (rieszPressurePotentialCutoffTest ψ n) i j) :=
    (rieszPressureJointHessian_contDiff
      (rieszPressurePotentialCutoffTest_contDiff hψ n) i j).continuous
  have hLapContinuousLimit : Continuous (rieszPressureJointLaplacian ψ) :=
    (rieszPressureJointLaplacian_contDiff hψ).continuous
  have hHessContinuousLimit : Continuous (rieszPressureJointHessian ψ i j) :=
    (rieszPressureJointHessian_contDiff hψ i j).continuous
  let boundLap (z : Vec3 × ℝ) :=
    (‖(p : Vec3 × ℝ → ℝ) z‖ * rieszPressurePotentialSpatialProfile K z) * CL
  let boundHess (z : Vec3 × ℝ) :=
    (‖(u : Vec3 × ℝ → ℝ) z‖ * rieszPressurePotentialSpatialProfile K z) * CH
  have hboundLapInt : Integrable boundLap (volume : Measure (Vec3 × ℝ)) :=
    hprofileInt.mul_const CL
  have hprofileU := rieszPressurePotentialProfile_integrable_mul hK u
  have hboundHessInt : Integrable boundHess (volume : Measure (Vec3 × ℝ)) :=
    hprofileU.mul_const CH
  have hLapMeas (n : ℕ) : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => (p : Vec3 × ℝ → ℝ) z *
        rieszPressureJointLaplacian
          (rieszPressurePotentialCutoffTest ψ n) z)
      (volume : Measure (Vec3 × ℝ)) :=
    (Lp.aestronglyMeasurable p).mul (hLapContinuous n).aestronglyMeasurable
  have hHessMeas (n : ℕ) : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => (u : Vec3 × ℝ → ℝ) z *
        rieszPressureJointHessian
          (rieszPressurePotentialCutoffTest ψ n) i j z)
      (volume : Measure (Vec3 × ℝ)) :=
    (Lp.aestronglyMeasurable u).mul (hHessContinuous n).aestronglyMeasurable
  have hLapBound (n : ℕ) : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      ‖(p : Vec3 × ℝ → ℝ) z * rieszPressureJointLaplacian
          (rieszPressurePotentialCutoffTest ψ n) z‖ ≤ boundLap z := by
    filter_upwards [] with z
    calc
      _ = ‖(p : Vec3 × ℝ → ℝ) z‖ *
          |rieszPressureJointLaplacian
            (rieszPressurePotentialCutoffTest ψ n) z| := by
          rw [norm_mul, Real.norm_eq_abs
            (rieszPressureJointLaplacian (rieszPressurePotentialCutoffTest ψ n) z)]
      _ ≤ ‖(p : Vec3 × ℝ → ℝ) z‖ *
          (CL * rieszPressurePotentialSpatialProfile K z) :=
        mul_le_mul_of_nonneg_left (hcutLapBound n z) (norm_nonneg _)
      _ = boundLap z := by dsimp [boundLap]; ring
  have hHessBound (n : ℕ) : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      ‖(u : Vec3 × ℝ → ℝ) z * rieszPressureJointHessian
          (rieszPressurePotentialCutoffTest ψ n) i j z‖ ≤ boundHess z := by
    filter_upwards [] with z
    calc
      _ = ‖(u : Vec3 × ℝ → ℝ) z‖ *
          |rieszPressureJointHessian
            (rieszPressurePotentialCutoffTest ψ n) i j z| := by
          rw [norm_mul, Real.norm_eq_abs
            (rieszPressureJointHessian (rieszPressurePotentialCutoffTest ψ n) i j z)]
      _ ≤ ‖(u : Vec3 × ℝ → ℝ) z‖ *
          (CH * rieszPressurePotentialSpatialProfile K z) :=
        mul_le_mul_of_nonneg_left (hcutHessBound n z) (norm_nonneg _)
      _ = boundHess z := by dsimp [boundHess]; ring
  have hLapPointwise : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      Tendsto (fun n => (p : Vec3 × ℝ → ℝ) z *
        rieszPressureJointLaplacian
          (rieszPressurePotentialCutoffTest ψ n) z)
        atTop (𝓝 ((p : Vec3 × ℝ → ℝ) z * rieszPressureJointLaplacian ψ z)) := by
    filter_upwards [] with z
    have hseq := tendsto_nhds_of_eventually_eq
      (rieszPressurePotentialCutoffTest_laplacian_eventually_eq hψ z)
    exact tendsto_const_nhds.mul hseq
  have hHessPointwise : ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      Tendsto (fun n => (u : Vec3 × ℝ → ℝ) z *
        rieszPressureJointHessian
          (rieszPressurePotentialCutoffTest ψ n) i j z)
        atTop (𝓝 ((u : Vec3 × ℝ → ℝ) z * rieszPressureJointHessian ψ i j z)) := by
    filter_upwards [] with z
    have hseq := tendsto_nhds_of_eventually_eq
      (rieszPressurePotentialCutoffTest_hessian_eventually_eq hψ i j z)
    exact tendsto_const_nhds.mul hseq
  have hLapIntegral := tendsto_integral_of_dominated_convergence boundLap
    hLapMeas hboundLapInt hLapBound hLapPointwise
  have hHessIntegral := tendsto_integral_of_dominated_convergence boundHess
    hHessMeas hboundHessInt hHessBound hHessPointwise
  have hCompact (n : ℕ) := rieszPressureComponent_laplacian_pairing_compact
    r hr q hq hHolder i j u
    (rieszPressurePotentialCutoffTest_contDiff hψ n)
    (rieszPressurePotentialCutoffTest_hasCompactSupport hK hzero n)
  have hSeq : (fun n => ∫ z, (p : Vec3 × ℝ → ℝ) z *
      rieszPressureJointLaplacian
        (rieszPressurePotentialCutoffTest ψ n) z) =ᶠ[atTop]
      fun n => -(∫ z, (u : Vec3 × ℝ → ℝ) z *
        rieszPressureJointHessian
          (rieszPressurePotentialCutoffTest ψ n) i j z) :=
    Filter.Eventually.of_forall hCompact
  have hNegIntegral := hHessIntegral.neg
  have hLeftLimit := (tendsto_congr' hSeq).2 hNegIntegral
  exact (tendsto_nhds_unique hLeftLimit hLapIntegral).symm

/-- The noncompact-potential identity holds for every space-time tensor class
in `L^(3/2)`, as asserted in `lem:riesz-duality`. -/
theorem rieszPressureSpaceTimeClass_noncompactPotential_duality
    (F : RieszPressureSpaceTimeTensorLp (3 / 2 : ℝ))
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hdecay : RieszPressurePotentialDecay ψ) :
    letI : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
    ∫ z, (rieszPressureSpaceTimeClass (3 / 2 : ℝ) (by norm_num) F :
        Vec3 × ℝ → ℝ) z * rieszPressureJointLaplacian ψ z =
      -∑ i : Fin 3, ∑ j : Fin 3, ∫ z, (F i j : Vec3 × ℝ → ℝ) z *
        rieszPressureJointHessian ψ i j z := by
  let : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
  let : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩
  have hq : 1 < (3 : ℝ) := by norm_num
  have hr : 1 < (3 / 2 : ℝ) := by norm_num
  have hHolder : (3 / 2 : ℝ).HolderConjugate 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hLapMem := rieszPressureJointLaplacian_memLp3 hψ hdecay
  let vLap := hLapMem.toLp (rieszPressureJointLaplacian ψ)
  let Pair : Lp ℝ (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) →L[ℝ] ℝ :=
    rieszPressureLpPairingCLM (3 / 2 : ℝ) hr 3 hq hHolder vLap
  have hEntry (i j : Fin 3) :
      Pair (rieszPressureSpaceTimeComponent (3 / 2 : ℝ) hr i j (F i j)) =
        -∫ z, (F i j : Vec3 × ℝ → ℝ) z *
          rieszPressureJointHessian ψ i j z := by
    dsimp [Pair]
    calc
      rieszPressureLpPairingCLM (3 / 2 : ℝ) hr 3 hq hHolder vLap
          (rieszPressureSpaceTimeComponent (3 / 2 : ℝ) hr i j (F i j)) =
        ∫ z, (rieszPressureSpaceTimeComponent (3 / 2 : ℝ) hr i j
          (F i j) : Vec3 × ℝ → ℝ) z *
            rieszPressureJointLaplacian ψ z :=
          calc
            _ = ∫ z, (rieszPressureSpaceTimeComponent (3 / 2 : ℝ) hr i j
                (F i j) : Vec3 × ℝ → ℝ) z * (vLap : Vec3 × ℝ → ℝ) z :=
              rieszPressureLpPairingCLM_apply (3 / 2 : ℝ) hr 3 hq hHolder
                vLap (rieszPressureSpaceTimeComponent (3 / 2 : ℝ) hr i j (F i j))
            _ = _ := by
              apply integral_congr_ae
              filter_upwards [hLapMem.coeFn_toLp] with z hz
              rw [hz]
      _ = -∫ z, (F i j : Vec3 × ℝ → ℝ) z *
          rieszPressureJointHessian ψ i j z :=
        rieszPressureComponent_laplacian_pairing_potential (F i j) hψ hdecay i j
  calc
    ∫ z, (rieszPressureSpaceTimeClass (3 / 2 : ℝ) hr F :
        Vec3 × ℝ → ℝ) z * rieszPressureJointLaplacian ψ z =
        Pair (rieszPressureSpaceTimeClass (3 / 2 : ℝ) hr F) := by
          symm
          calc
            _ = ∫ z, (rieszPressureSpaceTimeClass (3 / 2 : ℝ) hr F :
                Vec3 × ℝ → ℝ) z * (vLap : Vec3 × ℝ → ℝ) z :=
              rieszPressureLpPairingCLM_apply (3 / 2 : ℝ) hr 3 hq hHolder
                vLap (rieszPressureSpaceTimeClass (3 / 2 : ℝ) hr F)
            _ = _ := by
              apply integral_congr_ae
              filter_upwards [hLapMem.coeFn_toLp] with z hz
              rw [hz]
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
          Pair (rieszPressureSpaceTimeComponent (3 / 2 : ℝ) hr i j (F i j)) := by
          dsimp [Pair, rieszPressureSpaceTimeClass]
          simp only [map_sum]
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
          -∫ z, (F i j : Vec3 × ℝ → ℝ) z *
            rieszPressureJointHessian ψ i j z := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hEntry i j
    _ = -∑ i : Fin 3, ∑ j : Fin 3, ∫ z,
          (F i j : Vec3 × ℝ → ℝ) z *
            rieszPressureJointHessian ψ i j z := by
          simp only [Finset.sum_neg_distrib]

/-- The measurable space-time pressure representative satisfies the
noncompact-potential identity in `lem:riesz-duality`. -/
theorem rieszPressureSpaceTime_noncompactPotential_duality
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hdecay : RieszPressurePotentialDecay ψ) :
    ∫ z, rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF z *
        rieszPressureJointLaplacian ψ z =
      -∑ i : Fin 3, ∑ j : Fin 3, ∫ z, F i j z *
        rieszPressureJointHessian ψ i j z := by
  let hr : 1 < (3 / 2 : ℝ) := by norm_num
  let Fclass := rieszPressureSpaceTimeTensorToLp (3 / 2 : ℝ) hr F hF
  have hClassDual := rieszPressureSpaceTimeClass_noncompactPotential_duality
    Fclass hψ hdecay
  have hPae : (rieszPressureSpaceTime (3 / 2 : ℝ) hr F hF : Vec3 × ℝ → ℝ) =ᵐ[volume]
      (rieszPressureSpaceTimeClass (3 / 2 : ℝ) hr Fclass : Vec3 × ℝ → ℝ) := by
    dsimp [rieszPressureSpaceTime]
    exact ((Lp.aestronglyMeasurable
      (rieszPressureSpaceTimeClass (3 / 2 : ℝ) hr Fclass)).aemeasurable.ae_eq_mk).symm
  have hFae (i j : Fin 3) :
      (Fclass i j : Vec3 × ℝ → ℝ) =ᵐ[volume] F i j := by
    dsimp [Fclass, rieszPressureSpaceTimeTensorToLp]
    exact (hF i j).coeFn_toLp
  calc
    ∫ z, rieszPressureSpaceTime (3 / 2 : ℝ) hr F hF z *
        rieszPressureJointLaplacian ψ z =
      ∫ z, (rieszPressureSpaceTimeClass (3 / 2 : ℝ) hr Fclass :
        Vec3 × ℝ → ℝ) z * rieszPressureJointLaplacian ψ z := by
          apply integral_congr_ae
          filter_upwards [hPae] with z hz
          rw [hz]
    _ = -∑ i : Fin 3, ∑ j : Fin 3, ∫ z,
          (Fclass i j : Vec3 × ℝ → ℝ) z *
            rieszPressureJointHessian ψ i j z := hClassDual
    _ = -∑ i : Fin 3, ∑ j : Fin 3, ∫ z, F i j z *
          rieszPressureJointHessian ψ i j z := by
          have hSum : ∑ i : Fin 3, ∑ j : Fin 3, ∫ z,
              (Fclass i j : Vec3 × ℝ → ℝ) z *
                rieszPressureJointHessian ψ i j z =
              ∑ i : Fin 3, ∑ j : Fin 3, ∫ z, F i j z *
                rieszPressureJointHessian ψ i j z := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            apply integral_congr_ae
            filter_upwards [hFae i j] with z hz
            rw [hz]
          exact congrArg Neg.neg hSum

end CKN.Leray

end
