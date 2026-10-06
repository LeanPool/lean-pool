/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.CompactTestDensity
public import LeanPool.HighContrastHomogenization.Analytic.DualNormJunk
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.EuclideanWspSmoothDualFieldPairing

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.NegativeSobolevCubeDuality

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Negative Sobolev duality on triadic cubes

Below order one half, the compact-test negative Sobolev norm agrees with the
normalized smooth-dual cube norm. The resulting pairing estimate extends to
the full square-integrable fractional class.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem volumeAverage_openCubeSet_eq_normalizedIntegral
    {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (openCubeSet Q) f =
      ∫ x, f x ∂normalizedCubeMeasure Q := by
  calc
    volumeAverage (openCubeSet Q) f =
        (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q, f x ∂volume := by
      unfold volumeAverage
      rw [volume_openCubeSet_toReal]
    _ = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, f x ∂volume := by
      rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]
    _ = cubeAverage Q f := rfl
    _ = ∫ x, f x ∂normalizedCubeMeasure Q :=
      cubeAverage_eq_integral_normalizedCubeMeasure Q f

private theorem memLp_hilbert_normalizedCubeMeasure_of_memLp_openCubeSet
    {d : ℕ} (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : MemLp F 2 (volume.restrict (openCubeSet Q))) :
    MemLp (fun x => HilbertVec.ofVec (F x)) 2 (normalizedCubeMeasure Q) := by
  have hHilbert : MemLp (fun x => HilbertVec.ofVec (F x)) 2
      (volume.restrict (openCubeSet Q)) := by
    simpa only [HilbertVec.ofVecL_apply] using
      hF.continuousLinearMap_comp (HilbertVec.ofVecL d)
  rw [← cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  apply ((cubeBoundedMeasurableDomain Q).memLp_normalizedVolume_iff 2
    (fun x => HilbertVec.ofVec (F x))).2
  rw [cubeBoundedMeasurableDomain_restrictedVolume_eq_cubeMeasure]
  unfold cubeMeasure
  rwa [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

@[expose]
public noncomputable def cubeEuclideanWspL2FieldOfHsNormSq
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2)
    (G : Vec d → Vec d)
    (hGmeas : AEStronglyMeasurable G
      (volume.restrict (openCubeSet Q)))
    (hGfinite : hsNormSq (openCubeSet Q) s G ≠ ⊤) :
    CubeEuclideanWspL2Field Q
      (⟨s, hs, hsHalf.trans (by norm_num)⟩ : FractionalOrder)
      FiniteLpExponent.two := by
  let sF : FractionalOrder := ⟨s, hs, hsHalf.trans (by norm_num)⟩
  have hvolEq : volume (openCubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    exact (ENNReal.toReal_eq_toReal_iff'
      (volume_openCubeSet_lt_top Q).ne ENNReal.ofReal_ne_top).1 (by
        rw [volume_openCubeSet_toReal,
          ENNReal.toReal_ofReal (cubeVolume_nonneg Q)])
  have hvolPos : 0 < volume (openCubeSet Q) := by
    rw [hvolEq]
    exact ENNReal.ofReal_pos.mpr (cubeVolume_pos Q)
  have hweight0 :
      volume (openCubeSet Q) ^ (-(2 * s) / (d : ℝ)) ≠ 0 :=
    ne_of_gt (ENNReal.rpow_pos hvolPos (volume_openCubeSet_lt_top Q).ne)
  have hparts :
      volume (openCubeSet Q) ^ (-(2 * s) / (d : ℝ)) *
          eVolumeAverage (openCubeSet Q)
            (fun x => ENNReal.ofReal (vecNormSq (G x))) ≠ ⊤ ∧
        fracSeminormSq (openCubeSet Q) s G ≠ ⊤ :=
    ENNReal.add_ne_top.mp (by simpa only [hsNormSq] using hGfinite)
  have haverageTop :
      eVolumeAverage (openCubeSet Q)
          (fun x => ENNReal.ofReal (vecNormSq (G x))) ≠ ⊤ := by
    intro havg
    apply hparts.1
    rw [havg, ENNReal.mul_top hweight0]
  have hGnormMeas : AEStronglyMeasurable G (normalizedCubeMeasure Q) := by
    unfold normalizedCubeMeasure cubeMeasure
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact AEStronglyMeasurable.mono_ac Measure.smul_absolutelyContinuous hGmeas
  have hGhilbertMeas : AEStronglyMeasurable
      (fun x => HilbertVec.ofVec (G x)) (normalizedCubeMeasure Q) :=
    (HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable hGnormMeas
  have hL2sq :
      (eLpNorm (fun x => HilbertVec.ofVec (G x)) 2
          (normalizedCubeMeasure Q)) ^ (2 : ℕ) =
        eVolumeAverage (openCubeSet Q)
          (fun x => ENNReal.ofReal (vecNormSq (G x))) := by
    simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      euclideanNorm_eq_norm_ofVec, eLpNorm_norm _ hGhilbertMeas] using
        normalizedEuclideanLpENorm_two_sq_eq_eVolumeAverage Q G
          (by simpa only [euclideanNorm_eq_norm_ofVec] using hGhilbertMeas.norm)
  have hL2top : eLpNorm (fun x => HilbertVec.ofVec (G x)) 2
      (normalizedCubeMeasure Q) ≠ ⊤ := by
    intro htop
    apply haverageTop
    rw [← hL2sq, htop]
    norm_num
  have hGmemL2 : MemLp (fun x => HilbertVec.ofVec (G x)) 2
      (normalizedCubeMeasure Q) :=
    lt_top_iff_ne_top.mpr hL2top
  have hsemisq :
      (cubeEuclideanWspESeminorm Q sF FiniteLpExponent.two G) ^ (2 : ℕ) =
        fracSeminormSq (openCubeSet Q) s G := by
    simpa only [sF] using
      cubeEuclideanWspESeminorm_two_sq_eq_fracSeminormSq Q sF G hGmeas
  have hsemitop : cubeEuclideanWspESeminorm Q sF FiniteLpExponent.two G ≠ ⊤ := by
    intro htop
    apply hparts.2
    rw [← hsemisq, htop]
    norm_num
  exact
    { toField := G
      euclideanMemLp := hGmemL2
      euclideanMemWsp := memCubeEuclideanWsp_of_memLp_of_eSeminorm_lt_top
        hGmemL2 (lt_top_iff_ne_top.mpr hsemitop)
      euclideanMemL2 := hGmemL2 }

private theorem ofReal_abs_volumeAverage_le_sqrt_mul_negSobolevNorm
    {d : ℕ} {V : Set (Vec d)} {s K : ℝ}
    (F psi : Vec d → Vec d) (hK : 0 < K)
    (hpsi : IsLocalVecTest V psi)
    (hpsiNorm : hsNormSq V s psi ≤ ENNReal.ofReal K) :
    ENNReal.ofReal |volumeAverage V (fun x => vecDot (F x) (psi x))| ≤
      ENNReal.ofReal (Real.sqrt K) * negSobolevNorm V s F := by
  let r : ℝ := Real.sqrt K
  have hr : 0 < r := Real.sqrt_pos.mpr hK
  have hrsq : r ^ 2 = K := Real.sq_sqrt hK.le
  let phi : Vec d → Vec d := fun x => r⁻¹ • psi x
  have hphi : IsLocalVecTest V phi := hpsi.const_smul r⁻¹
  have hphiNorm : hsNormSq V s phi ≤ 1 := by
    rw [show phi = (fun x => r⁻¹ • psi x) by rfl, hsNormSq_smul]
    refine le_trans (mul_le_mul_right hpsiNorm _) ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg _), inv_pow, hrsq,
      inv_mul_cancel₀ hK.ne', ENNReal.ofReal_one]
  have hunit := ofReal_abs_pairing_le_negSobolevNorm V s F phi hphi hphiNorm
  have hrecover : (fun x => r • phi x) = psi := by
    funext x
    dsimp only [phi]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have havg : volumeAverage V (fun x => vecDot (F x) (psi x)) =
      r * volumeAverage V (fun x => vecDot (F x) (phi x)) := by
    rw [← hrecover]
    simp_rw [vecDot_smul_right]
    exact volumeAverage_smul V r (fun x => vecDot (F x) (phi x))
  rw [havg, abs_mul, abs_of_pos hr, ENNReal.ofReal_mul hr.le]
  gcongr

private theorem compact_test_norm_le_perturbed_unit
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {s : ℝ}
    (hs : 0 < s) (hsHalf : s < 1 / 2)
    (h : CubeEuclideanWspSmoothTest Q
      (⟨s, hs, hsHalf.trans (by norm_num)⟩ : FractionalOrder)
      FiniteLpExponent.two.conjugate)
    (hunit : cubeEuclideanWspFullENorm Q
      (⟨s, hs, hsHalf.trans (by norm_num)⟩ : FractionalOrder)
      FiniteLpExponent.two.conjugate h.toField ≤ 1)
    {delta : ℝ} (hdelta : 0 < delta) (psi : Vec d → Vec d)
    (hpsi : IsLocalVecTest (openCubeSet Q) psi)
    (herr : hsNormSq (openCubeSet Q) s (fun x => psi x - h.toField x) <
      (ENNReal.ofReal delta) ^ (2 : ℕ)) :
    hsNormSq (openCubeSet Q) s psi ≤ ENNReal.ofReal ((1 + delta) ^ 2) := by
  let sF : FractionalOrder := ⟨s, hs, hsHalf.trans (by norm_num)⟩
  let deltaE : ℝ≥0∞ := ENNReal.ofReal delta
  have honeDelta : 0 ≤ 1 + delta := by linarith only [hdelta]
  let psiS : CubeEuclideanWspSmoothTest Q sF
      FiniteLpExponent.two.conjugate :=
    { toField := psi
      contDiff := hpsi.contDiff }
  let errS : CubeEuclideanWspSmoothTest Q sF
      FiniteLpExponent.two.conjugate :=
    { toField := fun x => psi x - h.toField x
      contDiff := hpsi.contDiff.sub h.contDiff }
  have herrMeas : AEStronglyMeasurable (fun x => psi x - h.toField x)
      (volume.restrict (openCubeSet Q)) :=
    hpsi.contDiff.continuous.aestronglyMeasurable.sub
      h.contDiff.continuous.aestronglyMeasurable
  have herrBridge :
      (cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two
          (fun x => psi x - h.toField x)) ^
          (2 : ℕ) =
        hsNormSq (openCubeSet Q) s (fun x => psi x - h.toField x) := by
    calc
      (cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two
          (fun x => psi x - h.toField x)) ^
          (2 : ℕ) =
          (cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two
            (fun x => psi x - h.toField x)) ^
            (2 : ℝ) :=
        (ENNReal.rpow_natCast _ 2).symm
      _ = hsNormSq (openCubeSet Q) s (fun x => psi x - h.toField x) := by
        simpa only [sF] using
          cubeEuclideanWspFullENorm_two_sq_eq_hsNormSq Q sF
            (fun x => psi x - h.toField x) herrMeas
  have herrFullPow :
      (cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two
          (fun x => psi x - h.toField x)) ^
          (2 : ℕ) < deltaE ^ (2 : ℕ) := by
    rw [herrBridge]
    exact herr
  have herrFull :
      cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two
          (fun x => psi x - h.toField x) <
        deltaE :=
    (ENNReal.pow_lt_pow_left_iff (by norm_num)).mp herrFullPow
  have hsplit : psiS = h + errS := by
    apply CubeEuclideanWspSmoothTest.ext
    funext x
    simp only [psiS, errS, CubeEuclideanWspSmoothTest.toField_add,
      Pi.add_apply]
    abel
  have hpsiFullConj :
      cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two.conjugate psi ≤
        cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two.conjugate h.toField +
          cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two.conjugate
            (fun x => psi x - h.toField x) := by
    calc
      cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two.conjugate psiS.toField =
          ‖CubeEuclideanWspSmoothTest.graph psiS‖ₑ :=
        (CubeEuclideanWspSmoothTest.graph_enorm_eq_cubeEuclideanWspFullENorm
          psiS).symm
      _ = ‖CubeEuclideanWspSmoothTest.graph h +
          CubeEuclideanWspSmoothTest.graph errS‖ₑ := by
        rw [hsplit, map_add]
      _ ≤ ‖CubeEuclideanWspSmoothTest.graph h‖ₑ +
          ‖CubeEuclideanWspSmoothTest.graph errS‖ₑ := enorm_add_le _ _
      _ = cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two.conjugate h.toField +
          cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two.conjugate errS.toField := by
        rw [CubeEuclideanWspSmoothTest.graph_enorm_eq_cubeEuclideanWspFullENorm,
          CubeEuclideanWspSmoothTest.graph_enorm_eq_cubeEuclideanWspFullENorm]
  have hpsiFull :
      cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two psi ≤
        cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two h.toField +
          cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two
            (fun x => psi x - h.toField x) := by
    simpa only [FiniteLpExponent.conjugate_two, psiS, errS] using hpsiFullConj
  have hunitTwo : cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two
      h.toField ≤ 1 := by
    simpa only [FiniteLpExponent.conjugate_two] using hunit
  have hpsiFullBound :
      cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two psi ≤
        1 + deltaE :=
    hpsiFull.trans (add_le_add hunitTwo herrFull.le)
  have hpsiMeas : AEStronglyMeasurable psi
      (volume.restrict (openCubeSet Q)) :=
    hpsi.contDiff.continuous.aestronglyMeasurable
  have hpsiBridge :
      (cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two psi) ^
          (2 : ℕ) = hsNormSq (openCubeSet Q) s psi := by
    calc
      (cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two psi) ^
          (2 : ℕ) =
          (cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two psi) ^
            (2 : ℝ) :=
        (ENNReal.rpow_natCast _ 2).symm
      _ = hsNormSq (openCubeSet Q) s psi := by
        simpa only [sF] using
          cubeEuclideanWspFullENorm_two_sq_eq_hsNormSq Q sF psi hpsiMeas
  have hpsiNorm :
      hsNormSq (openCubeSet Q) s psi ≤ ENNReal.ofReal ((1 + delta) ^ 2) := by
    rw [← hpsiBridge]
    calc
      (cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two psi) ^
          (2 : ℕ) ≤ (1 + deltaE) ^ (2 : ℕ) :=
        ENNReal.pow_le_pow_left hpsiFullBound
      _ = ENNReal.ofReal ((1 + delta) ^ 2) := by
        rw [show 1 + deltaE = ENNReal.ofReal (1 + delta) by
          dsimp only [deltaE]
          simpa only [ENNReal.ofReal_one] using
            (ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hdelta.le).symm]
        rw [ENNReal.ofReal_pow honeDelta]
  exact hpsiNorm

theorem cubeEuclideanNegativeWspSmoothDualENorm_le_negSobolevNorm
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    cubeEuclideanNegativeWspSmoothDualENorm Q
        (⟨s, hs, hsHalf.trans (by norm_num)⟩ : FractionalOrder)
        FiniteLpExponent.two F ≤
      negSobolevNorm (openCubeSet Q) s F.toField := by
  let sF : FractionalOrder := ⟨s, hs, hsHalf.trans (by norm_num)⟩
  let N : ℝ≥0∞ := negSobolevNorm (openCubeSet Q) s F.toField
  change cubeEuclideanNegativeWspSmoothDualENorm Q sF
      FiniteLpExponent.two F ≤ N
  unfold cubeEuclideanNegativeWspSmoothDualENorm
  apply iSup_le
  rintro ⟨h, hunit⟩
  change ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| ≤ N
  by_cases hNtop : N = ⊤
  · rw [hNtop]
    exact le_top
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hNtop).mp
  rw [ENNReal.toReal_ofReal (abs_nonneg _)]
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  let A : ℝ := (eLpNorm (fun x => HilbertVec.ofVec (F.toField x)) 2
    (normalizedCubeMeasure Q)).toReal
  let delta : ℝ := epsilon / (A + N.toReal + 1)
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hN : 0 ≤ N.toReal := ENNReal.toReal_nonneg
  have hden : 0 < A + N.toReal + 1 := by positivity
  have hdelta : 0 < delta := div_pos hepsilon hden
  have honeDelta : 0 ≤ 1 + delta := by linarith only [hdelta]
  let deltaE : ℝ≥0∞ := ENNReal.ofReal delta
  let W : ℝ≥0∞ := volume (openCubeSet Q) ^ (-(2 * s) / (d : ℝ))
  have hvolEq : volume (openCubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    exact (ENNReal.toReal_eq_toReal_iff'
      (volume_openCubeSet_lt_top Q).ne ENNReal.ofReal_ne_top).1 (by
        rw [volume_openCubeSet_toReal,
          ENNReal.toReal_ofReal (cubeVolume_nonneg Q)])
  have hvolPos : 0 < volume (openCubeSet Q) := by
    rw [hvolEq]
    exact ENNReal.ofReal_pos.mpr (cubeVolume_pos Q)
  have hWpos : 0 < W := by
    exact ENNReal.rpow_pos hvolPos (volume_openCubeSet_lt_top Q).ne
  have hWtop : W ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero
    hvolPos.ne' (volume_openCubeSet_lt_top Q).ne
  have hdeltaE : 0 < deltaE := ENNReal.ofReal_pos.mpr hdelta
  let q : ℝ≥0∞ := min (deltaE ^ (2 : ℕ)) (W * deltaE ^ (2 : ℕ))
  have hq : 0 < q := by
    exact lt_min (ENNReal.pow_pos hdeltaE 2)
      (ENNReal.mul_pos hWpos.ne' (ENNReal.pow_pos hdeltaE 2).ne')
  obtain ⟨psi, hpsi, herr⟩ :=
    exists_localVecTest_hsNormSq_sub_lt_smooth_of_lt_half Q hs hsHalf
      h.toField h.contDiff (epsilon := q) hq
  let psiS : CubeEuclideanWspSmoothTest Q sF
      FiniteLpExponent.two.conjugate :=
    { toField := psi
      contDiff := hpsi.contDiff }
  have hpsiNorm : hsNormSq (openCubeSet Q) s psi ≤
      ENNReal.ofReal ((1 + delta) ^ 2) :=
    compact_test_norm_le_perturbed_unit Q hs hsHalf h hunit hdelta psi hpsi
      (herr.trans_le (min_le_left _ _))
  have hpairPsi :=
    ofReal_abs_volumeAverage_le_sqrt_mul_negSobolevNorm F.toField psi
      (K := (1 + delta) ^ 2) (by positivity) hpsi hpsiNorm
  have hsqrt : Real.sqrt ((1 + delta) ^ 2) = 1 + delta := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
  rw [hsqrt] at hpairPsi
  change ENNReal.ofReal |volumeAverage (openCubeSet Q)
      (fun x => vecDot (F.toField x) (psi x))| ≤
        ENNReal.ofReal (1 + delta) * N at hpairPsi
  have hpairPsiReal :
      |volumeAverage (openCubeSet Q)
          (fun x => vecDot (F.toField x) (psi x))| ≤
        (1 + delta) * N.toReal := by
    have hrightTop : ENNReal.ofReal (1 + delta) * N ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hNtop
    have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hrightTop).mpr
      hpairPsi
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal honeDelta] using hreal
  let L2err : ℝ≥0∞ := eLpNorm
    (fun x => HilbertVec.ofVec (psi x - h.toField x)) 2
      (normalizedCubeMeasure Q)
  have hL2sq : L2err ^ (2 : ℕ) =
      eVolumeAverage (openCubeSet Q)
        (fun x => ENNReal.ofReal (vecNormSq (psi x - h.toField x))) := by
    have herrHilbertMeas : AEStronglyMeasurable
        (fun x => HilbertVec.ofVec (psi x - h.toField x)) (normalizedCubeMeasure Q) :=
      ((HilbertVec.ofVecL d).continuous.comp
        (hpsi.contDiff.continuous.sub h.contDiff.continuous)).aestronglyMeasurable
    simpa only [L2err, BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      euclideanNorm_eq_norm_ofVec, eLpNorm_norm _ herrHilbertMeas] using
        normalizedEuclideanLpENorm_two_sq_eq_eVolumeAverage Q
          (fun x => psi x - h.toField x)
          (by simpa only [euclideanNorm_eq_norm_ofVec] using herrHilbertMeas.norm)
  have hweighted : W * L2err ^ (2 : ℕ) ≤
      hsNormSq (openCubeSet Q) s (fun x => psi x - h.toField x) := by
    unfold hsNormSq
    rw [hL2sq]
    exact le_add_right le_rfl
  have hweightedLt : W * L2err ^ (2 : ℕ) < W * deltaE ^ (2 : ℕ) :=
    hweighted.trans_lt (herr.trans_le (min_le_right _ _))
  have hL2pow : L2err ^ (2 : ℕ) < deltaE ^ (2 : ℕ) :=
    (ENNReal.mul_lt_mul_iff_right hWpos.ne' hWtop).mp hweightedLt
  have hL2err : L2err < deltaE :=
    (ENNReal.pow_lt_pow_left_iff (by norm_num)).mp hL2pow
  have hL2errTop : L2err ≠ ⊤ := hL2err.ne_top
  have hL2errReal : L2err.toReal ≤ delta := by
    have hlt := (ENNReal.toReal_lt_toReal hL2errTop ENNReal.ofReal_ne_top).mpr hL2err
    simpa only [deltaE, ENNReal.toReal_ofReal hdelta.le] using hlt.le
  have hflip : eLpNorm
      (fun x => HilbertVec.ofVec (h.toField x - psi x)) 2
        (normalizedCubeMeasure Q) = L2err := by
    have hfun : (fun x => HilbertVec.ofVec (h.toField x - psi x)) =
        -(fun x => HilbertVec.ofVec (psi x - h.toField x)) := by
      funext x
      change (HilbertVec.ofVecL d) (h.toField x - psi x) =
        -(HilbertVec.ofVecL d) (psi x - h.toField x)
      rw [show h.toField x - psi x = -(psi x - h.toField x) by abel,
        map_neg]
    rw [hfun, eLpNorm_neg]
  have hpairEq : cubeEuclideanNormalizedSmoothPairing F psiS =
      volumeAverage (openCubeSet Q)
        (fun x => vecDot (F.toField x) (psi x)) := by
    unfold cubeEuclideanNormalizedSmoothPairing
    rw [volumeAverage_openCubeSet_eq_normalizedIntegral]
  have hdifference :
      |cubeEuclideanNormalizedSmoothPairing F h -
          volumeAverage (openCubeSet Q)
            (fun x => vecDot (F.toField x) (psi x))| ≤ A * delta := by
    rw [← hpairEq]
    have hsub : cubeEuclideanNormalizedSmoothPairing F h -
        cubeEuclideanNormalizedSmoothPairing F psiS =
        ∫ x, vecDot (F.toField x) (h.toField x - psi x)
          ∂normalizedCubeMeasure Q := by
      unfold cubeEuclideanNormalizedSmoothPairing
      rw [← integral_sub
        (cubeEuclideanNormalizedSmoothPairing_integrable F h)
        (cubeEuclideanNormalizedSmoothPairing_integrable F psiS)]
      apply integral_congr_ae
      filter_upwards with x
      simp only [psiS, sub_eq_add_neg, vecDot_add_right, vecDot_neg_right]
    rw [hsub]
    calc
      |∫ x, vecDot (F.toField x) (h.toField x - psi x)
          ∂normalizedCubeMeasure Q| ≤
          A * (eLpNorm (fun x => HilbertVec.ofVec (h.toField x - psi x)) 2
            (normalizedCubeMeasure Q)).toReal := by
        dsimp only [A]
        apply CubeCalderonZygmund.INTERNAL.abs_integral_vecDot_le_eLpNorm_toReal_mul
        · simpa only [FiniteLpExponent.two_exponent] using F.euclideanMemLp
        · simpa only [HilbertVec.ofVecL_apply] using!
            h.euclideanMemLp_two.sub psiS.euclideanMemLp_two
      _ = A * L2err.toReal := by rw [hflip]
      _ ≤ A * delta := mul_le_mul_of_nonneg_left hL2errReal hA
  calc
    |cubeEuclideanNormalizedSmoothPairing F h| ≤
        |volumeAverage (openCubeSet Q)
          (fun x => vecDot (F.toField x) (psi x))| +
        |cubeEuclideanNormalizedSmoothPairing F h -
          volumeAverage (openCubeSet Q)
            (fun x => vecDot (F.toField x) (psi x))| := by
      calc
        |cubeEuclideanNormalizedSmoothPairing F h| =
            |volumeAverage (openCubeSet Q)
                (fun x => vecDot (F.toField x) (psi x)) +
              (cubeEuclideanNormalizedSmoothPairing F h -
                volumeAverage (openCubeSet Q)
                  (fun x => vecDot (F.toField x) (psi x)))| := by
          congr 1
          ring
        _ ≤ _ := abs_add_le _ _
    _ ≤ (1 + delta) * N.toReal + A * delta :=
      add_le_add hpairPsiReal hdifference
    _ = N.toReal + (N.toReal + A) * delta := by ring
    _ ≤ N.toReal + epsilon := by
      gcongr
      rw [show (N.toReal + A) * delta =
        (epsilon * (N.toReal + A)) / (A + N.toReal + 1) by
          dsimp only [delta]
          ring]
      apply (div_le_iff₀ hden).mpr
      apply mul_le_mul_of_nonneg_left
      · linarith only [hA, hN]
      · exact hepsilon.le

/-- Below the trace threshold, every compactly supported smooth unit test for
the compact-test negative Sobolev norm is a unit test for the normalized cube
smooth-dual norm. -/
theorem negSobolevNorm_le_cubeEuclideanNegativeWspSmoothDualENorm
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    negSobolevNorm (openCubeSet Q) s F.toField ≤
      cubeEuclideanNegativeWspSmoothDualENorm Q
        (⟨s, hs, hsHalf.trans (by norm_num)⟩ : FractionalOrder)
        FiniteLpExponent.two F := by
  let sF : FractionalOrder := ⟨s, hs, hsHalf.trans (by norm_num)⟩
  unfold negSobolevNorm
  apply iSup_le
  rintro ⟨psi, hpsi, hpsiUnit⟩
  let psiS : CubeEuclideanWspSmoothTest Q sF
      FiniteLpExponent.two.conjugate :=
    { toField := psi
      contDiff := hpsi.contDiff }
  have hpsiMeas : AEStronglyMeasurable psi
      (volume.restrict (openCubeSet Q)) :=
    hpsi.contDiff.continuous.aestronglyMeasurable
  have hbridge :
      (cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two psi) ^
          (2 : ℕ) = hsNormSq (openCubeSet Q) s psi := by
    calc
      (cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two psi) ^
          (2 : ℕ) =
          (cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two psi) ^
            (2 : ℝ) :=
        (ENNReal.rpow_natCast _ 2).symm
      _ = hsNormSq (openCubeSet Q) s psi := by
        simpa only [sF] using
          cubeEuclideanWspFullENorm_two_sq_eq_hsNormSq Q sF psi hpsiMeas
  have hfull :
      cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two.conjugate psi ≤ 1 := by
    have hpow :
        (cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two psi) ^
            (2 : ℕ) ≤ 1 ^ (2 : ℕ) := by
      rw [hbridge]
      simpa only [one_pow] using hpsiUnit
    simpa only [FiniteLpExponent.conjugate_two] using
      (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpow
  have hintCube : IntegrableOn (fun x => vecDot (F.toField x) (psi x))
      (cubeSet Q) volume :=
    integrableOn_of_integrable_normalizedCubeMeasure Q
      (cubeEuclideanNormalizedSmoothPairing_integrable F psiS)
  have hint : IntegrableOn (fun x => vecDot (F.toField x) (psi x))
      (openCubeSet Q) volume := by
    change Integrable (fun x => vecDot (F.toField x) (psi x))
      (volume.restrict (openCubeSet Q))
    rw [← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact hintCube
  have hpair : volumeAverage (openCubeSet Q)
      (fun x => vecDot (F.toField x) (psi x)) =
        cubeEuclideanNormalizedSmoothPairing F psiS := by
    rw [volumeAverage_openCubeSet_eq_normalizedIntegral]
    rfl
  rw [dualPairing_eq_ofReal _ _ _ hint, hpair]
  exact le_trans (ENNReal.ofReal_le_ofReal (le_abs_self _))
    (le_iSup
      (fun h : CubeEuclideanWspSmoothUnitTest Q sF
          FiniteLpExponent.two.conjugate =>
        ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h.1|)
      ⟨psiS, hfull⟩)

/-- For `p = 2` and orders below one half, the compact-test negative
Sobolev norm is exactly the normalized cube smooth-dual norm. -/
theorem negSobolevNorm_eq_cubeEuclideanNegativeWspSmoothDualENorm
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    negSobolevNorm (openCubeSet Q) s F.toField =
      cubeEuclideanNegativeWspSmoothDualENorm Q
        (⟨s, hs, hsHalf.trans (by norm_num)⟩ : FractionalOrder)
        FiniteLpExponent.two F := by
  apply le_antisymm
  · exact negSobolevNorm_le_cubeEuclideanNegativeWspSmoothDualENorm
      Q hs hsHalf F
  · exact cubeEuclideanNegativeWspSmoothDualENorm_le_negSobolevNorm
      Q hs hsHalf F

/-- The normalized pairing with a finite fractional field extends from compact
smooth tests to the full square-integrable fractional class. -/
theorem ofReal_abs_volumeAverage_le_sqrt_hsNormSq_mul_negSobolevNorm
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2)
    (F G : Vec d → Vec d)
    (hF : MemLp F 2
      (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hGmeas : AEStronglyMeasurable G
      (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hGfinite : hsNormSq (openCubeSet Q) s G ≠ ⊤) :
    ENNReal.ofReal
        |volumeAverage (openCubeSet Q) (fun x => vecDot (F x) (G x))| ≤
      (hsNormSq (openCubeSet Q) s G) ^ (1 / 2 : ℝ) *
        negSobolevNorm (openCubeSet Q) s F := by
  let sF : FractionalOrder := ⟨s, hs, hsHalf.trans (by norm_num)⟩
  let FF : CubeEuclideanLpField Q FiniteLpExponent.two :=
    { toField := F
      euclideanMemLp :=
        memLp_hilbert_normalizedCubeMeasure_of_memLp_openCubeSet Q hF }
  let GG : CubeEuclideanWspL2Field Q sF FiniteLpExponent.two :=
    cubeEuclideanWspL2FieldOfHsNormSq Q hs hsHalf G hGmeas hGfinite
  let Gconj : CubeEuclideanWspL2Field Q sF
      FiniteLpExponent.two.conjugate :=
    { toField := G
      euclideanMemLp := by
        simpa only [FiniteLpExponent.conjugate_two] using! GG.euclideanMemLp
      euclideanMemWsp := by
        simpa only [FiniteLpExponent.conjugate_two] using! GG.euclideanMemWsp
      euclideanMemL2 := GG.euclideanMemL2 }
  have hGconjField : Gconj.toField = G := by
    rfl
  have hpair : volumeAverage (openCubeSet Q)
      (fun x => vecDot (F x) (G x)) =
        cubeEuclideanNormalizedFieldPairing FF Gconj := by
    rw [volumeAverage_openCubeSet_eq_normalizedIntegral]
    unfold cubeEuclideanNormalizedFieldPairing
    simp only [FF, hGconjField]
  have hraw :=
    ennreal_ofReal_abs_cubeEuclideanNormalizedFieldPairing_le
      (p := FiniteLpExponent.two) FF Gconj
  have hdual : cubeEuclideanNegativeWspSmoothDualENorm Q sF
      FiniteLpExponent.two FF ≤ negSobolevNorm (openCubeSet Q) s F := by
    simpa only [sF, FF] using
      cubeEuclideanNegativeWspSmoothDualENorm_le_negSobolevNorm Q hs hsHalf FF
  have hfullSq :
      (cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two G) ^ (2 : ℝ) =
        hsNormSq (openCubeSet Q) s G := by
    simpa only [sF] using
      cubeEuclideanWspFullENorm_two_sq_eq_hsNormSq Q sF G hGmeas
  have hfull : cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two G =
      (hsNormSq (openCubeSet Q) s G) ^ (1 / 2 : ℝ) := by
    calc
      cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two G =
          (cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two G) ^ (1 : ℝ) :=
        (ENNReal.rpow_one _).symm
      _ = (cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two G) ^
          ((2 : ℝ) * (1 / 2 : ℝ)) := by norm_num
      _ = ((cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two G) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) := ENNReal.rpow_mul _ _ _
      _ = (hsNormSq (openCubeSet Q) s G) ^ (1 / 2 : ℝ) := by rw [hfullSq]
  rw [hpair]
  calc
    ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing FF Gconj| ≤
        cubeEuclideanNegativeWspSmoothDualENorm Q sF FiniteLpExponent.two FF *
          cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two.conjugate
            Gconj.toField := hraw
    _ = cubeEuclideanNegativeWspSmoothDualENorm Q sF FiniteLpExponent.two FF *
          cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two G := by
      rw [hGconjField, FiniteLpExponent.conjugate_two]
    _ ≤ negSobolevNorm (openCubeSet Q) s F *
          cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two G := by
      gcongr
    _ = (hsNormSq (openCubeSet Q) s G) ^ (1 / 2 : ℝ) *
          negSobolevNorm (openCubeSet Q) s F := by
      rw [hfull]
      exact mul_comm _ _

end

end HighContrast
end HCPolySupport
