/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.FreezingRadius
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.LocalSplitBounds
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.LocalizedTailData

/-!
# LocalizedTailData

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Localized whole-space tail data for the stream field

This module packages the sharp-carrier scale decomposition as the analytic
split used by the localized Agmon estimate.  The negative shells form the
rough skew field and the nonnegative shells form the continuously
differentiable skew field.  Their quantitative hypotheses are the logarithmic
ball bounds from `LocalSplitBounds`.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
open DivergenceFormProcess.Decay
open DivergenceFormProcess.Form
open HCPolySupport
open HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The whole-space analytic coefficient furnished by one full stream-field
sample. -/
def streamWholeSpaceAnalyticData (M : ABKModel d)
    (omega : FullSample d M.gamma) : WholeSpaceAnalyticData d where
  a := streamCoefficient M.nu omega
  nu := M.nu
  hnu := M.nu_pos
  hsymm := symmPart_streamCoefficient M.nu omega
  hskewContinuous := by
    have hcont : Continuous fun y =>
        streamCoefficient M.nu omega y - M.nu • (1 : Mat d) := by
      rw [show (fun y => streamCoefficient M.nu omega y - M.nu • (1 : Mat d)) =
          streamField omega by
        funext y
        ext i j
        simp only [streamCoefficient, Matrix.sub_apply, Matrix.add_apply]
        ring]
      exact continuous_streamField omega
    exact hcont.continuousOn
  hd := M.shellPrefix.dimension
  hameas := (continuous_streamCoefficient M.nu omega).measurable

/-- The rough coefficient consisting of molecular diffusion and the negative
shells. -/
def streamRoughCoefficient (M : ABKModel d) (omega : FullSample d M.gamma) :
    CoeffField d := fun x => M.nu • (1 : Mat d) + streamFieldSmall omega x

omit [NeZero d] in
private theorem continuous_streamFieldSmall (M : ABKModel d)
    (omega : FullSample d M.gamma) : Continuous (streamFieldSmall omega) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hfull := continuous_streamField_entry omega i j
  have hlarge :=
    (contDiff_pi.mp (contDiff_pi.mp (streamFieldLarge_contDiff_one omega) i) j).continuous
  rw [show (fun x => streamFieldSmall omega x i j) = fun x =>
      streamField omega x i j - streamFieldLarge omega x i j by
    funext x
    have hsplit := streamField_eq_small_add_large omega x
    exact (sub_eq_iff_eq_add.mpr (congrFun (congrFun hsplit i) j)).symm]
  exact hfull.sub hlarge

omit [NeZero d] in
theorem symmPart_streamRoughCoefficient (M : ABKModel d)
    (omega : FullSample d M.gamma) (x : Vec d) :
    symmPart (streamRoughCoefficient M omega x) = M.nu • (1 : Mat d) :=
  symmPart_scalar_add_skew rfl (streamFieldSmall_skew omega x)

omit [NeZero d] in
theorem continuous_streamRoughSkew (M : ABKModel d)
    (omega : FullSample d M.gamma) : Continuous fun x =>
      streamRoughCoefficient M omega x - M.nu • (1 : Mat d) := by
  simpa only [streamRoughCoefficient, add_sub_cancel_left] using
    continuous_streamFieldSmall M omega

/-- A compactness-supplied upper ellipticity constant for the rough
coefficient on one exhaustion cube.  It is qualitative only and does not
enter the localized tail bound. -/
def streamRoughEllipticityUpper (M : ABKModel d)
    (omega : FullSample d M.gamma) (m : ℕ) : ℝ :=
  axisCubeEllipticUpper (fun _ => -((3 : ℝ) ^ m)) (2 * (3 : ℝ) ^ m)
    M.nu_pos (symmPart_streamRoughCoefficient M omega)
    ((continuous_streamRoughSkew M omega).continuousOn)

omit [NeZero d] in
theorem streamRoughEllipticity (M : ABKModel d)
    (omega : FullSample d M.gamma) (m : ℕ) :
    IsEllipticFieldOn M.nu (streamRoughEllipticityUpper M omega m)
      (wholeSpaceCube d m) (streamRoughCoefficient M omega) := by
  exact isEllipticFieldOn_axisCubeEllipticUpper
    (fun _ => -((3 : ℝ) ^ m)) (2 * (3 : ℝ) ^ m) M.nu_pos
    (symmPart_streamRoughCoefficient M omega)
    ((continuous_streamRoughSkew M omega).continuousOn)

/-- The fixed perturbative threshold used only after freezing. -/
def streamLocalizedTailDelta (d : ℕ) : ℝ :=
  smallContrastThreshold d (1 / 2 : ℝ)

theorem streamLocalizedTailDelta_pos (d : ℕ) :
    0 < streamLocalizedTailDelta d := by
  unfold streamLocalizedTailDelta smallContrastThreshold
  positivity

/-- The stream field supplies every structural and local quantitative input
of the split-skew tail estimate. -/
def streamLocalizedSplitData (M : ABKModel d)
    (omega : FullSample d M.gamma) :
    WholeSpaceLocalizedSplitData (streamWholeSpaceAnalyticData M omega) where
  ks := streamFieldSmall omega
  kl := streamFieldLarge omega
  split := fun y => by
    simp only [streamWholeSpaceAnalyticData, streamCoefficient]
    rw [streamField_eq_small_add_large omega y]
    abel
  ksSkew := streamFieldSmall_skew omega
  klSkew := streamFieldLarge_skew omega
  klContDiff := fun p q =>
    contDiff_pi.mp (contDiff_pi.mp (streamFieldLarge_contDiff_one omega) p) q
  roughEllipticityUpper := streamRoughEllipticityUpper M omega
  roughEllipticity := streamRoughEllipticity M omega
  holderExponent := 1 / 2
  holderExponent_mem := by constructor <;> norm_num
  delta := streamLocalizedTailDelta d
  delta_nonneg := (streamLocalizedTailDelta_pos d).le
  delta_le := le_rfl
  freezingRadius := streamFreezingRadius M omega M.nu (streamLocalizedTailDelta d)
  freezingRadius_pos := streamFreezingRadius_pos M omega M.nu_pos
    (streamLocalizedTailDelta_pos d)
  smallContrast := coefficientIdentityDistanceLE_streamCoefficient M omega
    M.nu_pos (streamLocalizedTailDelta_pos d)
  roughBound := streamFieldSmallLocalConst M omega
  smoothDivBound := streamFieldLargeDivLocalConst M omega
  roughBound_nonneg := fun x r hr =>
    streamFieldSmallLocalConst_nonneg M omega hr
  smoothDivBound_nonneg := fun x r hr =>
    streamFieldLargeDivLocalConst_nonneg M omega hr
  roughBound_spec := fun x r hr y hy v =>
    vecNormSq_matVecMul_streamFieldSmall_le M omega hr hy v
  smoothDivBound_spec := fun x r hr y hy =>
    vecNormSq_skewFieldDiv_streamFieldLarge_le M omega hr hy

end

end Algsuperdiff.Section5.Field
