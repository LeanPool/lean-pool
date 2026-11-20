/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Reduction.ExactScalingParameters
public import LeanPool.FastDynamo.Global.CellGeometry
public import LeanPool.FastDynamo.Local.ParameterizedHelicalProfile
public import LeanPool.FastDynamo.Analysis.WholePlaneL4FormPerturbationHolder
public import LeanPool.FastDynamo.Analysis.WholePlaneLocalCompactnessUnconditional
public import LeanPool.FastDynamo.Operator.AnalyticFredholmContinuation
public import LeanPool.FastDynamo.Local.WholePlaneSliceRadius
public import LeanPool.FastDynamo.Analysis.WholePlaneSliceProductRule
public import LeanPool.FastDynamo.Analysis.WholePlaneUnitDiskSliceGeometry
public import LeanPool.FastDynamo.Analysis.WholePlaneUnitCircleWeightedSlices
public import LeanPool.FastDynamo.Local.PonomarenkoExteriorSecondPartialBounds
public import LeanPool.FastDynamo.Local.PonomarenkoCartesianPolarLaplacian
public import LeanPool.FastDynamo.Operator.WholePlanePivotAntiDual
public import LeanPool.FastDynamo.Operator.ResolventAnnulus
public import LeanPool.FastDynamo.Operator.CompactAtkinsonIndexZero
public import LeanPool.FastDynamo.Operator.RieszDomainCalculus

/-!
# The scaling parameters of a matching cell

A matching cell of a scale family (`ScaleFamily.MatchingCell`, `Global/CellGeometry.lean`) is
the cell selected by a given physical diffusivity.  This module bundles it, together with a free
axial translation `tau`, into the scaling parameters `WholePlaneExactScalingParameters` of
Lemma 5.2 (`lem:exact-renormalization`): `MatchingCell.exactScalingParameters`.  Its physical and
rescaled diffusivities, integer Fourier mode, transverse length, axial amplitude and local axial
wavenumber are the cell's, its translation slot is `tau`, and the frequency and shift matching
identities required by `eq:scaling` are proved from the matching conditions of the cell.  The
`simp` lemmas below read off each slot.  `Global/GlobalSpectralTransferConcrete.lean` uses the
package, with `tau` the global contour translation, to rescale the local resolvent of the
selected cell.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace ScaleFamily.MatchingCell

variable {p : LocalSeedParameters} {r : ScaleRatios p}
  {f : ScaleFamily r} {epsilon : ℝ}

/-- A matching cell supplies all scalar hypotheses of exact whole-plane
rescaling.  The axial translation `tau` remains free for the later global
spectral placement. -/
def exactScalingParameters (c : MatchingCell f epsilon) (tau : ℝ) :
    WholePlaneExactScalingParameters where
  epsilon := epsilon
  delta := c.delta
  K := f.fourierIndex c.index
  ell := f.ell c.index
  a := f.axialAmplitude tau c.index
  N := p.wavenumber
  tau := tau
  ell_pos := f.ell_pos c.index
  delta_eq := rfl
  N_eq := by
    simpa only [wholePlaneAxialWavenumber, Int.cast_natCast] using
      c.axial_wavenumber_match.symm
  tau_eq := by
    simpa only [wholePlaneAxialWavenumber, Int.cast_natCast] using
      (c.axialAmplitude_match tau).symm

/-- The scaling package of a matching cell carries the physical diffusivity `epsilon` unchanged. -/
@[simp] theorem exactScalingParameters_epsilon
    (c : MatchingCell f epsilon) (tau : ℝ) :
    (c.exactScalingParameters tau).epsilon = epsilon :=
  rfl

/-- Its rescaled diffusivity slot is the cell's `delta = epsilon / ell ^ 2`. -/
@[simp] theorem exactScalingParameters_delta
    (c : MatchingCell f epsilon) (tau : ℝ) :
    (c.exactScalingParameters tau).delta = c.delta :=
  rfl

/-- Its Fourier-mode slot is the cell's rounded frequency `K_n`. -/
@[simp] theorem exactScalingParameters_K
    (c : MatchingCell f epsilon) (tau : ℝ) :
    (c.exactScalingParameters tau).K = f.fourierIndex c.index :=
  rfl

/-- Its transverse length slot is the cell's core scale `ell_n`. -/
@[simp] theorem exactScalingParameters_ell
    (c : MatchingCell f epsilon) (tau : ℝ) :
    (c.exactScalingParameters tau).ell = f.ell c.index :=
  rfl

/-- Its axial-amplitude slot is the cell's added axial speed `a_n`. -/
@[simp] theorem exactScalingParameters_a
    (c : MatchingCell f epsilon) (tau : ℝ) :
    (c.exactScalingParameters tau).a = f.axialAmplitude tau c.index :=
  rfl

/-- Its local axial wavenumber slot is the seed's fixed wavenumber `N`; together with
`exactScalingParameters_K` and `_ell` this is the frequency matching `2 pi K_n ell_n = N` required
by the scaling identity `eq:scaling` of `lem:exact-renormalization`. -/
@[simp] theorem exactScalingParameters_N
    (c : MatchingCell f epsilon) (tau : ℝ) :
    (c.exactScalingParameters tau).N = p.wavenumber :=
  rfl

/-- Its spectral-translation slot is the free axial shift `tau`, the vertical translation appearing
in `lem:exact-renormalization`. -/
@[simp] theorem exactScalingParameters_tau
    (c : MatchingCell f epsilon) (tau : ℝ) :
    (c.exactScalingParameters tau).tau = tau :=
  rfl

end ScaleFamily.MatchingCell

end

end FastDynamo
