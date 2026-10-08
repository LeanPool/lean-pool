/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorAnchoredMeanTelescope
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorClassEnergy
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubePoisson.AnalyticInput

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorWeightedGradientBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# From weighted corrector energy to normalized Euclidean gradient control

The intrinsic good-tail estimate is coefficient-weighted.  The Liouville
function-growth argument uses ordinary normalized `L²` Poincare estimates.
This module records the exact conversion under a fixed positive global lower
ellipticity constant.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The weighted norm is invariant under a.e. replacement of its coefficient
representative on the integration domain. -/
theorem weightedGradNorm_congr_coeff_ae_on
    {d : ℕ} {U : Set (Vec d)} {a b : CoeffField d}
    (F : Vec d → Vec d) (hab : a =ᵐ[volumeMeasureOn U] b) :
    weightedGradNorm a U F = weightedGradNorm b U F := by
  unfold weightedGradNorm eVolumeAverage
  congr 2
  apply lintegral_congr_ae
  filter_upwards [hab] with x hx
  simp only [hx]

/-- The Euclidean magnitude of an `H¹` weak gradient belongs to normalized
`L²` on its cube. -/
theorem H1Function.memLp_euclideanGrad_normalizedCubeMeasure
    {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) :
    MemLp (fun x => euclideanNorm (u.grad x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
  let w : W1pFunction (openCubeSet Q) (2 : ℝ≥0∞) :=
    { toFun := u.toFun
      grad := u.grad
      memLp := u.memL2
      gradMemLp := u.gradMemL2
      hasWeakGradient := u.hasWeakGradient }
  have hmem := w.gradEuclideanMemLp
    ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
      (Book.Ch02.openCubeSet_nonempty Q)) (2 : ℝ≥0∞)
  rw [openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    at hmem
  simpa only [w] using hmem

private theorem euclideanNorm_sub_le {d : ℕ} (x y : Vec d) :
    euclideanNorm (x - y) ≤ euclideanNorm x + euclideanNorm y := by
  rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
    euclideanNorm_eq_norm_ofVec]
  change ‖WithLp.toLp 2 (x - y)‖ ≤
    ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 y‖
  rw [WithLp.toLp_sub]
  exact norm_sub_le _ _

/-- Subtracting a constant vector increases the normalized `L²` norm of the
Euclidean magnitude by at most that vector's Euclidean norm. -/
theorem cubeLpNorm_euclideanGrad_sub_const_le
    {d : ℕ} (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) (e : Vec d) :
    cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => euclideanNorm (u.grad x - e)) ≤
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) +
        euclideanNorm e := by
  by_cases hm : AEStronglyMeasurable (fun x => euclideanNorm (u.grad x - e))
      (normalizedCubeMeasure Q)
  swap
  · rw [cubeLpNorm, eLpNorm_of_not_aestronglyMeasurable hm, ENNReal.toReal_top]
    exact add_nonneg ENNReal.toReal_nonneg (euclideanNorm_nonneg e)
  have hfull := H1Function.memLp_euclideanGrad_normalizedCubeMeasure u
  have hconst : MemLp (fun _ : Vec d => euclideanNorm e) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := memLp_const _
  have hsum : MemLp
      (fun x => euclideanNorm (u.grad x) + euclideanNorm e) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := hfull.add hconst
  have hmonoRaw :
      eLpNorm (fun x => euclideanNorm (u.grad x - e)) 2
          (normalizedCubeMeasure Q) ≤
        eLpNorm (fun x => euclideanNorm (u.grad x) + euclideanNorm e) 2
          (normalizedCubeMeasure Q) := by
    apply eLpNorm_mono_ae hm
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (euclideanNorm_nonneg _), abs_of_nonneg (add_nonneg
        (euclideanNorm_nonneg _) (euclideanNorm_nonneg _))] using
      euclideanNorm_sub_le (u.grad x) e
  have hmono :
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x - e)) ≤
        cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x => euclideanNorm (u.grad x) + euclideanNorm e) := by
    unfold cubeLpNorm
    exact ENNReal.toReal_mono hsum.eLpNorm_ne_top hmonoRaw
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x - e)) ≤
        cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x => euclideanNorm (u.grad x) + euclideanNorm e) := hmono
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) +
        cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => euclideanNorm e) :=
      cubeLpNorm_add_le Q 2 _ _ hfull hconst (by norm_num)
    _ = cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) +
        euclideanNorm e := by
      rw [cubeLpNorm_const Q 2 (euclideanNorm e) (by norm_num),
        Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg e)]

/-- A weighted-gradient bound on a cube controls the normalized Euclidean
`L²` norm of the weak gradient, with the expected `lam⁻¹/²` loss. -/
theorem cubeLpNorm_euclideanGrad_le_div_sqrt_of_weightedGradNorm_le
    {d : ℕ} (Q : TriadicCube d)
    {b : CoeffField d} {lam Lam B : ℝ}
    (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) b)
    (u : H1Function (openCubeSet Q)) (hB : 0 ≤ B)
    (hweighted : weightedGradNorm b (openCubeSet Q) u.grad ≤
      ENNReal.ofReal B) :
    cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) ≤
      B / Real.sqrt lam := by
  have hgradMem : MemLp (fun x => euclideanNorm (u.grad x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) :=
    H1Function.memLp_euclideanGrad_normalizedCubeMeasure u
  let E : ℝ := normalizedLocalSymmetricEnergy hEll u.gradToHilbertVectorL2
  have hbridge : ENNReal.ofReal E =
      weightedGradNorm b (openCubeSet Q) u.grad ^ 2 := by
    simpa only [E, H1Function.gradToHilbertVectorL2] using
      ofReal_normalizedLocalSymmetricEnergy_eq_weightedGradNorm_sq
        hEll u.grad_memVectorL2
  have hweightedSq := ENNReal.pow_le_pow_left hweighted (n := 2)
  have hBpow : ENNReal.ofReal B ^ 2 = ENNReal.ofReal (B ^ 2) := by
    rw [ENNReal.ofReal_pow hB]
  have hE_le : E ≤ B ^ 2 := by
    rw [← hbridge, hBpow] at hweightedSq
    exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg B)).1 hweightedSq
  have hsqInt : IntegrableOn (fun x => vecNormSq (u.grad x))
      (openCubeSet Q) := integrableOn_vecNormSq_h1Grad u
  have henergyInt : IntegrableOn
      (coefficientEnergyDensity b u.grad) (openCubeSet Q) :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn
      hEll u.grad_memVectorL2
  have hmem : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), x ∈ openCubeSet Q :=
    (ae_restrict_iff' (measurableSet_openCubeSet Q)).2
      (Filter.Eventually.of_forall fun _x hx => hx)
  have hpoint : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      lam * vecNormSq (u.grad x) ≤ coefficientEnergyDensity b u.grad x := by
    filter_upwards [hmem] with x hx
    exact lowerBound_symmPart_of_isEllipticMatrix (hEll.2 x hx) (u.grad x)
  have hlower :
      lam * ∫ x in openCubeSet Q, vecNormSq (u.grad x) ∂volume ≤
        ∫ x in openCubeSet Q,
          coefficientEnergyDensity b u.grad x ∂volume := by
    calc
      lam * ∫ x in openCubeSet Q, vecNormSq (u.grad x) ∂volume =
          ∫ x in openCubeSet Q, lam * vecNormSq (u.grad x) ∂volume := by
            rw [integral_const_mul]
      _ ≤ ∫ x in openCubeSet Q,
          coefficientEnergyDensity b u.grad x ∂volume :=
        integral_mono_ae (hsqInt.const_mul lam) henergyInt hpoint
  have hnormSq :
      ∫ x in openCubeSet Q, vecNormSq (u.grad x) ∂volume =
        cubeVolume Q *
          (cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => euclideanNorm (u.grad x))) ^ (2 : ℕ) := by
    have hnorm :=
      setIntegral_openCubeSet_sq_eq_cubeVolume_mul_cubeLpNorm_two_rpow Q
        (fun x => euclideanNorm (u.grad x)) hgradMem
    calc
      ∫ x in openCubeSet Q, vecNormSq (u.grad x) ∂volume =
          ∫ x in openCubeSet Q,
            euclideanNorm (u.grad x) * euclideanNorm (u.grad x) ∂volume := by
              apply setIntegral_congr_fun (measurableSet_openCubeSet Q)
              intro x _hx
              change vecNormSq (u.grad x) =
                euclideanNorm (u.grad x) * euclideanNorm (u.grad x)
              rw [← euclideanNorm_sq]
              ring
      _ = cubeVolume Q *
          (cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => euclideanNorm (u.grad x))) ^ (2 : ℝ) := hnorm
      _ = cubeVolume Q *
          (cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => euclideanNorm (u.grad x))) ^ (2 : ℕ) := by
              rw [Real.rpow_two]
  have henergyEq : E = (cubeVolume Q)⁻¹ *
      ∫ x in openCubeSet Q,
        coefficientEnergyDensity b u.grad x ∂volume := by
    have h := normalizedLocalSymmetricEnergy_eq_volumeAverage
      hEll u.grad_memVectorL2
    simpa only [E, H1Function.gradToHilbertVectorL2, volumeAverage,
      volume_openCubeSet_toReal] using h
  have hvol : 0 < cubeVolume Q := cubeVolume_pos Q
  have hnormalizedLower :
      lam * (cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => euclideanNorm (u.grad x))) ^ 2 ≤ E := by
    rw [hnormSq] at hlower
    rw [henergyEq]
    calc
      lam * (cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x => euclideanNorm (u.grad x))) ^ 2 =
          (cubeVolume Q)⁻¹ *
            (lam * (cubeVolume Q *
              (cubeLpNorm Q (2 : ℝ≥0∞)
                (fun x => euclideanNorm (u.grad x))) ^ 2)) := by
                  field_simp [hvol.ne']
      _ ≤ (cubeVolume Q)⁻¹ *
          ∫ x in openCubeSet Q,
            coefficientEnergyDensity b u.grad x ∂volume := by
              apply mul_le_mul_of_nonneg_left
              · simpa only [mul_assoc] using hlower
              · exact inv_nonneg.mpr hvol.le
  have hsq :
      (cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => euclideanNorm (u.grad x))) ^ 2 ≤ B ^ 2 / lam := by
    apply (le_div_iff₀ hlam).2
    simpa only [mul_comm] using hnormalizedLower.trans hE_le
  have hsqrt : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hrhs : 0 ≤ B / Real.sqrt lam := div_nonneg hB hsqrt.le
  apply (sq_le_sq₀
    (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) _ ) hrhs).1
  calc
    (cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => euclideanNorm (u.grad x))) ^ 2 ≤ B ^ 2 / lam := hsq
    _ = (B / Real.sqrt lam) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hlam.le]

/-- The conversion remains valid when the available weighted estimate uses an
a.e.-equivalent local coefficient representative. -/
theorem cubeLpNorm_euclideanGrad_le_div_sqrt_of_ae_weightedGradNorm_le
    {d : ℕ} (Q : TriadicCube d)
    {a b : CoeffField d} {lam Lam B : ℝ}
    (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) b)
    (hab : a =ᵐ[volumeMeasureOn (openCubeSet Q)] b)
    (u : H1Function (openCubeSet Q)) (hB : 0 ≤ B)
    (hweighted : weightedGradNorm a (openCubeSet Q) u.grad ≤
      ENNReal.ofReal B) :
    cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) ≤
      B / Real.sqrt lam := by
  apply cubeLpNorm_euclideanGrad_le_div_sqrt_of_weightedGradNorm_le
    Q hlam hEll u hB
  rwa [← weightedGradNorm_congr_coeff_ae_on u.grad hab]

end

end HighContrast
end HCPolySupport
