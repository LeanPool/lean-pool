/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedHeatStokesSemigroup
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedHeatStokesRealification
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedRealFourierCutoff

/-!
# Real heat and Stokes propagation laws

The real Fourier heat flow composes in time and propagates a real
Stokes output by adding elapsed times.
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Real heat evolution composes across nonnegative adjacent times. -/
theorem realHeatOperator_add
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (b : RealVectorL2) :
    realHeatOperator (s + t) (add_nonneg hs ht) b =
      realHeatOperator s hs (realHeatOperator t ht b) := by
  have hcomplex :
      complexifyVectorL2 (realHeatOperator (s + t) (add_nonneg hs ht) b) =
      complexifyVectorL2 (realHeatOperator s hs (realHeatOperator t ht b)) := by
    rw [← heatSemigroup_complexify_real,
      ← heatSemigroup_complexify_real,
      ← heatSemigroup_complexify_real,
      regularisedHeatSemigroup_add]
  have hreal := congrArg realPartVectorL2 hcomplex
  simpa only [realPartVectorL2_complexifyVectorL2] using hreal

/-- Real heat evolution of a Stokes output adds the two elapsed times. -/
theorem realHeatOperator_stokes
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 < t) (F : RealTensorL2) :
    realHeatOperator s hs (realStokesOperator ht F) =
      realStokesOperator (show 0 < s + t by positivity) F := by
  have hcomplex :
      complexifyVectorL2 (realHeatOperator s hs (realStokesOperator ht F)) =
      complexifyVectorL2
        (realStokesOperator (show 0 < s + t by positivity) F) := by
    rw [← heatSemigroup_complexify_real,
      ← stokesL2Operator_complexify_real,
      ← stokesL2Operator_complexify_real,
      regularisedHeatSemigroup_stokesL2Operator]
  have hreal := congrArg realPartVectorL2 hcomplex
  simpa only [realPartVectorL2_complexifyVectorL2] using hreal

end CKN.Leray

end
