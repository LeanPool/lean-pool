/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicSlope

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorIntrinsicSlopeCanonical

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Topological reduction of canonical intrinsic slope

This module isolates the topology-only part of normalized-slope identification.
The intrinsic full-gradient slope is equivalent to vanishing corrector-gradient
averages, and the average commutes with every fixed-cube joint local limit.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

open MeasureTheory

private instance intrinsicSlopeCanonicalCubeFiniteMeasure (d n : ℕ) :
    IsFiniteMeasure (volumeMeasureOn (localGradientCube d n)) := by
  simpa [localGradientCube, volumeMeasureOn] using
    (isOpenBoundedConvexDomain_openCubeSet
      (originCube d (n : ℤ))).isFiniteMeasure_restrict_volume

/-- Averaging a local gradient class is continuous. -/
theorem continuous_localGradientClassAverage {d n : ℕ} :
    Continuous (localGradientClassAverage : LocalGradientL2 d n → Vec d) := by
  apply continuous_pi
  intro i
  change Continuous (fun g : LocalGradientL2 d n =>
    (cubeVolume (originCube d (n : ℤ)))⁻¹ *
      hilbertVectorL2CoordSetIntegralCLM
        (U := localGradientCube d n)
        (localGradientCube d n)
        (by simpa only [localGradientCube] using
          measurableSet_openCubeSet (originCube d (n : ℤ))) i g)
  fun_prop

/-- The corrector part has asymptotically vanishing normalized gradient
average on the centered exhaustion. -/
@[expose]
def HasVanishingCorrectorGradientAverage {d : ℕ}
    (z : NormalizedLocalH1Carrier d) : Prop :=
  _root_.Filter.Tendsto
    (fun n => localGradientClassAverage (z.gradientComponent n))
    _root_.Filter.atTop (nhds 0)

/-- Vanishing corrector averages imply the intrinsic full-gradient slope. -/
theorem HasVanishingCorrectorGradientAverage.hasIntrinsicNormalizedSlope
    {d : ℕ} [NeZero d] {e : Vec d} {z : NormalizedLocalH1Carrier d}
    (h : HasVanishingCorrectorGradientAverage z) :
    HasIntrinsicNormalizedSlope e z := by
  have hsum := (tendsto_const_nhds :
    _root_.Filter.Tendsto (fun _n : ℕ => e) _root_.Filter.atTop (nhds e)).add h
  simpa only [HasIntrinsicNormalizedSlope, localGradientClassAverage_add,
    localGradientClassAverage_finiteAffineBoundaryH1, Pi.zero_apply,
    add_zero] using hsum

/-- Intrinsic full-gradient slope forces the corrector-class averages to
vanish. -/
theorem HasIntrinsicNormalizedSlope.hasVanishingCorrectorGradientAverage
    {d : ℕ} [NeZero d] {e : Vec d} {z : NormalizedLocalH1Carrier d}
    (h : HasIntrinsicNormalizedSlope e z) :
    HasVanishingCorrectorGradientAverage z := by
  have hsub := h.sub (tendsto_const_nhds :
    _root_.Filter.Tendsto (fun _n : ℕ => e) _root_.Filter.atTop (nhds e))
  simpa only [HasIntrinsicNormalizedSlope, HasVanishingCorrectorGradientAverage,
    localGradientClassAverage_add,
    localGradientClassAverage_finiteAffineBoundaryH1, add_sub_cancel_left,
    sub_self]
    using hsub

/-- On every fixed cube, the averages of normalized finite-corrector gradient
classes converge to the average of the canonical joint-limit component. -/
theorem finiteAffineCorrectionLocalGradientAverage_tendsto
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a) (e : Vec d) (n : ℕ) :
    _root_.Filter.Tendsto
      (fun k => localGradientClassAverage
        (normalizedLocalPair
          (finiteAffineCorrectionLocalSequence a e) n k).2)
      _root_.Filter.atTop
      (nhds (localGradientClassAverage
        ((finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent n))) := by
  exact
    (continuous_localGradientClassAverage.tendsto _).comp
      (finiteAffineCorrectionJointLocalLimit_isLimit a hCauchy e n).snd_nhds

end

end HighContrast
end HCPolySupport
