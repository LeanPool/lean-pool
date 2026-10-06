/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorRealRadiusBallGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicCubeGrowth

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorNormalizedL2Bridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Bridge from cube `L²` norms to the frozen normalized ball norm

The regularity chain uses the real-valued `cubeLpNorm`, while the frozen
Liouville carrier uses the non-vacuous `ENNReal`-valued `normalizedL2Norm`.
This module relates them without changing either public definition.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Probability-style normalization of volume on an arbitrary measurable
set.  No nonzero-volume assertion is built into the definition. -/
@[expose]
noncomputable def volumeNormalizedMeasure {d : ℕ} (V : Set (Vec d)) :
    Measure (Vec d) :=
  (volume V)⁻¹ • volume.restrict V

private theorem eLpNorm_two_eq_rpow_normalizedL2
    {A : Type*} [MeasurableSpace A]
    (f : A → ℝ) (mu : Measure A) (hf : AEStronglyMeasurable f mu) :
    eLpNorm f 2 mu =
      (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂mu) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  congr 1
  apply lintegral_congr
  intro x
  rw [← ofReal_norm, Real.norm_eq_abs]
  norm_num [ENNReal.rpow_two]
  calc
    ENNReal.ofReal |f x| ^ 2 = ENNReal.ofReal (|f x| ^ 2) :=
      (ENNReal.ofReal_pow (abs_nonneg (f x)) 2).symm
    _ = ENNReal.ofReal (f x ^ 2) := by rw [sq_abs]

/-- The frozen normalized `L²` norm is exactly the ordinary `eLpNorm` for
the explicitly volume-normalized restricted measure. -/
theorem normalizedL2Norm_eq_eLpNorm_volumeNormalizedMeasure
    {d : ℕ} (V : Set (Vec d)) (f : Vec d → ℝ)
    (hf : AEStronglyMeasurable f (volumeNormalizedMeasure V)) :
    normalizedL2Norm V f = eLpNorm f 2 (volumeNormalizedMeasure V) := by
  rw [eLpNorm_two_eq_rpow_normalizedL2 f _ hf]
  unfold normalizedL2Norm eVolumeAverage volumeNormalizedMeasure
  rw [lintegral_smul_measure, smul_eq_mul, ENNReal.div_eq_inv_mul]

/-- Restricting a normalized `L²` norm to a smaller positive finite-volume
set costs the square root of the volume ratio. -/
theorem normalizedL2Norm_mono_set_le_volumeRatio
    {d : ℕ} {U V : Set (Vec d)} (hUV : U ⊆ V)
    (hUzero : volume U ≠ 0) (hUtop : volume U ≠ ⊤)
    (hVzero : volume V ≠ 0) (hVtop : volume V ≠ ⊤)
    (f : Vec d → ℝ) :
    normalizedL2Norm U f ≤
      (volume V / volume U) ^ (1 / 2 : ℝ) * normalizedL2Norm V f := by
  let IU : ℝ≥0∞ := ∫⁻ x in U, ENNReal.ofReal (f x ^ 2) ∂volume
  let IV : ℝ≥0∞ := ∫⁻ x in V, ENNReal.ofReal (f x ^ 2) ∂volume
  have hI : IU ≤ IV := by
    dsimp only [IU, IV]
    exact lintegral_mono'
      (Measure.restrict_mono_set volume hUV) le_rfl
  have hbase : IU / volume U ≤
      (volume V / volume U) * (IV / volume V) := by
    rw [ENNReal.div_le_iff hUzero hUtop]
    have hcancel :
        (volume V / volume U) * (IV / volume V) * volume U = IV := by
      calc
        (volume V / volume U) * (IV / volume V) * volume U =
            (volume V / volume U * volume U) * (IV / volume V) := by
              ac_rfl
        _ = volume V * (IV / volume V) := by
          rw [ENNReal.div_mul_cancel hUzero hUtop]
        _ = IV := ENNReal.mul_div_cancel hVzero hVtop
    exact hI.trans_eq hcancel.symm
  have hrpow := ENNReal.rpow_le_rpow hbase (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hrpow
  simpa only [normalizedL2Norm, eVolumeAverage, IU, IV] using hrpow

/-- On an open triadic cube, the frozen normalized norm is the `ENNReal`
lift of `cubeLpNorm`, provided the local `L²` norm is finite. -/
theorem normalizedL2Norm_openCubeSet_eq_ofReal_cubeLpNorm
    {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    normalizedL2Norm (openCubeSet Q) f =
      ENNReal.ofReal (cubeLpNorm Q 2 f) := by
  have hmeasure : volumeNormalizedMeasure (openCubeSet Q) =
      normalizedCubeMeasure Q := by
    unfold volumeNormalizedMeasure normalizedCubeMeasure cubeMeasure
    rw [volume_openCubeSet_eq_volume_cubeSet,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    congr 1
    rw [← ENNReal.ofReal_toReal (volume_cubeSet_lt_top Q).ne]
    simp only [volume_cubeSet_toReal, ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q)]
  rw [normalizedL2Norm_eq_eLpNorm_volumeNormalizedMeasure _ f
    (hmeasure ▸ hf.aestronglyMeasurable), hmeasure]
  unfold cubeLpNorm
  exact (ENNReal.ofReal_toReal hf.eLpNorm_ne_top).symm

/-- The global representative of a normalized local carrier is square
integrable for the normalized measure on every exhaustion cube. -/
theorem NormalizedLocalH1Carrier.memLp_globalValueRepresentative_normalizedCubeMeasure
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (q : ℕ) :
    MemLp z.globalValueRepresentative 2
      (normalizedCubeMeasure (originCube d (q : ℤ))) := by
  have haeVolume : z.globalValueRepresentative
      =ᵐ[volumeMeasureOn (localGradientCube d q)]
        (z.localH1Function q).toFun :=
    z.globalValueRepresentative_ae_eq_localH1Function q
  have haeNormalized : z.globalValueRepresentative
      =ᵐ[normalizedCubeMeasure (originCube d (q : ℤ))]
        (z.localH1Function q).toFun := by
    simpa only [localGradientCube, volumeMeasureOn, normalizedCubeMeasure,
      cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using!
      Measure.ae_smul_measure haeVolume
        (ENNReal.ofReal ((cubeVolume (originCube d (q : ℤ)))⁻¹))
  exact (memLp_congr_ae haeNormalized).mpr
    (z.localH1Function q).memL2_normalizedCubeMeasure

/-- The frozen normalized ball norm is controlled by the normalized norm on
the canonical enclosing triadic cube with a dimension-only `ENNReal` factor. -/
theorem normalizedL2Norm_euclideanBall_le_outerCube
    {d : ℕ} [NeZero d] {r : ℝ} (hr : 0 < r)
    (f : Vec d → ℝ)
    (hf : MemLp f 2 (normalizedCubeMeasure
      (originCube d (outerTriadicGeneration (2 * r) (by positivity))))) :
    normalizedL2Norm (euclideanBall d r) f ≤
      (ENNReal.ofReal ((3 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal
          (cubeLpNorm
            (originCube d (outerTriadicGeneration (2 * r) (by positivity)))
            2 f) := by
  let Q : TriadicCube d :=
    originCube d (outerTriadicGeneration (2 * r) (by positivity))
  have hballzero : volume (euclideanBall d r) ≠ 0 := by
    exact ne_of_gt (IsOpen.measure_pos volume (isOpen_euclideanBall d r)
      (euclideanBall_nonempty (0 : Vec d) hr))
  have hballtop : volume (euclideanBall d r) ≠ ⊤ :=
    (isOpenBoundedConvexDomain_euclideanBallAt (0 : Vec d) hr).volume_lt_top.ne
  have hQzero : volume (openCubeSet Q) ≠ 0 := by
    intro hzero
    have hvolume := volume_openCubeSet_toReal Q
    rw [hzero] at hvolume
    simp only [ENNReal.toReal_zero] at hvolume
    exact (cubeVolume_pos Q).ne' hvolume.symm
  have hQtop : volume (openCubeSet Q) ≠ ⊤ :=
    (volume_openCubeSet_lt_top Q).ne
  have hratioTop : volume (openCubeSet Q) / volume (euclideanBall d r) ≠ ⊤ :=
    ENNReal.div_ne_top hQtop hballzero
  have hdim : 0 ≤ (3 * Real.sqrt d) ^ d := by positivity
  have hratio : volume (openCubeSet Q) / volume (euclideanBall d r) ≤
      ENNReal.ofReal ((3 * Real.sqrt d) ^ d) := by
    apply (ENNReal.le_ofReal_iff_toReal_le hratioTop hdim).2
    rw [ENNReal.toReal_div]
    exact le_of_lt (by
      simpa only [Q] using
        outerTriadicGeneration_volume_ratio_lt_euclideanBall (d := d) hr)
  have hrestrict := normalizedL2Norm_mono_set_le_volumeRatio
    (euclideanBall_subset_openCubeSet_originCube_outerTriadicGeneration
      (d := d) hr)
    hballzero hballtop hQzero hQtop f
  have hfactor := ENNReal.rpow_le_rpow hratio
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    normalizedL2Norm (euclideanBall d r) f ≤
        (volume (openCubeSet Q) / volume (euclideanBall d r)) ^ (1 / 2 : ℝ) *
          normalizedL2Norm (openCubeSet Q) f := hrestrict
    _ ≤ (ENNReal.ofReal ((3 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ) *
          normalizedL2Norm (openCubeSet Q) f :=
      mul_le_mul_left hfactor _
    _ = (ENNReal.ofReal ((3 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (cubeLpNorm Q 2 f) := by
      rw [normalizedL2Norm_openCubeSet_eq_ofReal_cubeLpNorm Q f (by
        simpa only [Q] using hf)]

end

end HighContrast
end HCPolySupport
