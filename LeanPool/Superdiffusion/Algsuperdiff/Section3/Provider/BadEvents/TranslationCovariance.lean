/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Symmetry
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffCoarseBlockRepresentative
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.Translation
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.Translation
public import LeanPool.HighContrastHomogenization.Support.Geometry.TriadicCubeTranslation

/-!
# TranslationCovariance

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Deterministic translation covariance of the cutoff homogenization error

ABK26's induction state `d.mathcalS.def` controls the multiscale homogenization
error `mathcal E_{s,infinity,2}(square_m; a_m, sigma_m)` at the *centered* cube
`square_m`, while the local bad event `e.Bloc.def` lives at the off-centre cube
`z + square_j`.  The probabilistic half of the passage between them is the
translation invariance of the cutoff sample law
(`Cutoff.map_translateCutoffSample_cutoffSampleLaw`).  This module supplies the
missing deterministic half: the *pathwise* identity

```
mathcal E(z + square_j; a_j(omega))  =  mathcal E(square_j; a_j(tau_z omega)) ,
```

where `tau_z` is the translation action `Cutoff.translateCutoffSample z` on the
sample space and `z = triadicCubeShift Q` is the base point of the cube.

## Proof route

Nothing analytic is reproved.  The chain is:

* CoarseGraining's
  `Ch02.HomogenizationErrorOnCube_translateCube_of_normalizedBlockResponseMax`
  reduces the whole descendant tree to the *one-cube* covariance of
  `Ch02.normalizedBlockResponseMax`;
* the proved
  `Observable.normalizedBlockResponseMax_cutoff_eq_fromRawCoarseBlock` rewrites
  that one-cube maximum as a finite-dimensional sphere maximum of the raw
  coarse block matrix `coarseBlockMatrix (cubeSet Q) a`;
* CoarseGraining's `coarseBlockMatrix_translateSet_eq_translateCoeffField` is
  the covariance of the raw coarse block matrix under a real translation of the
  domain, and `Cutoff.coefficientCutoff_translateCutoffSample` transports the
  translation from the coefficient field to the sample.

The only genuinely new ingredient is the elementary triadic geometry
`cubeSet_translateCube_descendantTranslationShift`: a depth-`l` descendant of a
scale-`j` cube is shifted by the real vector `3^j z` when its index is shifted
by `descendantTranslationShift l z`.

## Main results

* `cubeSet_translateCube_descendantTranslationShift`
* `normalizedBlockResponseMax_translateCutoffSample`
* `homogenizationErrorOnCube_translateCutoffSample`

## References

* ABK26, `d.mathcalS.def` and `e.Bloc.def`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Triadic geometry of the descendant shift -/

/-- The half-open realization of a scale-`(j - l)` cube whose index is shifted
by `descendantTranslationShift l z` is the translate of the original by the
*scale-`j`* real vector `3^j z`.  This is the geometry that makes a single real
translation act simultaneously on all nine generations of descendants. -/
theorem cubeSet_translateCube_descendantTranslationShift (z : Fin d → ℤ) (l : ℕ)
    {R : TriadicCube d} {j : ℤ} (hR : R.scale = j - (l : ℤ)) :
    cubeSet (translateCube (descendantTranslationShift l z) R) =
      translateSet (fun i => (z i : ℝ) * (3 : ℝ) ^ j) (cubeSet R) := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hpow : (3 : ℝ) ^ (l : ℕ) * (3 : ℝ) ^ (j - (l : ℤ)) = (3 : ℝ) ^ j := by
    rw [← zpow_natCast (3 : ℝ) l, ← zpow_add₀ h3]
    congr 1
    ring
  have hvec :
      (fun i => ((descendantTranslationShift l z i : ℤ) : ℝ) * cubeScaleFactor R) =
        (fun i => (z i : ℝ) * (3 : ℝ) ^ j) := by
    funext i
    have hcast : ((descendantTranslationShift l z i : ℤ) : ℝ) =
        (3 : ℝ) ^ (l : ℕ) * (z i : ℝ) := by
      simp [descendantTranslationShift]
    calc ((descendantTranslationShift l z i : ℤ) : ℝ) * cubeScaleFactor R
        = ((3 : ℝ) ^ (l : ℕ) * (z i : ℝ)) * (3 : ℝ) ^ (j - (l : ℤ)) := by
          rw [hcast, cubeScaleFactor, hR]
      _ = (z i : ℝ) * ((3 : ℝ) ^ (l : ℕ) * (3 : ℝ) ^ (j - (l : ℤ))) := by ring
      _ = (z i : ℝ) * (3 : ℝ) ^ j := by rw [hpow]
  ext x
  rw [mem_cubeSet_translateCube_iff, mem_translateSet_iff_sub_mem, hvec]

/-! ## One-cube covariance of the normalized block-response maximum -/

/-- One-cube translation covariance for the actual coefficient cutoff: if the
half-open realization of `T` is the translate by `v` of that of `R`, then the
normalized block-response maximum of the cutoff at `T` equals the one at `R`
for the translated sample. -/
theorem normalizedBlockResponseMax_translateCutoffSample [NeZero d] (M : ABKModel d)
    (m : ℤ) (v : Vec d) {R T : TriadicCube d}
    (hset : cubeSet T = translateSet v (cubeSet R)) (a0 : Mat d)
    (omega : CutoffSample d) :
    Ch02.normalizedBlockResponseMax T
        (coefficientCutoffTriadicCoeffFamily M m omega) a0 =
      Ch02.normalizedBlockResponseMax R
        (coefficientCutoffTriadicCoeffFamily M m (translateCutoffSample v omega))
        a0 := by
  rw [Algsuperdiff.Section3.Observable.normalizedBlockResponseMax_cutoff_eq_fromRawCoarseBlock,
    Algsuperdiff.Section3.Observable.normalizedBlockResponseMax_cutoff_eq_fromRawCoarseBlock]
  congr 1
  change toFullBlockMat (coarseBlockMatrix (cubeSet T)
      (coefficientCutoff M.nu m omega).toFun) =
    toFullBlockMat (coarseBlockMatrix (cubeSet R)
      (coefficientCutoff M.nu m (translateCutoffSample v omega)).toFun)
  rw [hset, coarseBlockMatrix_translateSet_eq_translateCoeffField,
    coefficientCutoff_translateCutoffSample]
  rfl

/-! ## Covariance of the multiscale homogenization error -/

/-- **Deterministic translation covariance.**  For the actual coefficient
cutoff, the multiscale homogenization error on an arbitrary triadic cube `Q`
equals the one on the centered cube of the same scale, evaluated at the sample
translated by the base point `triadicCubeShift Q` of `Q`.

This is the deterministic half of the passage between ABK26's induction state
(stated at `square_j`) and the local bad event (stated at `z + square_j`). -/
theorem homogenizationErrorOnCube_translateCutoffSample [NeZero d] (M : ABKModel d)
    (m : ℤ) (Q : TriadicCube d) (s : ℝ) (p q : Ch02.MultiscaleExponent)
    (a0 : Mat d) (omega : CutoffSample d) :
    Ch02.HomogenizationErrorOnCube Q s p q
        (coefficientCutoffTriadicCoeffFamily M m omega) a0 =
      Ch02.HomogenizationErrorOnCube (originCube d Q.scale) s p q
        (coefficientCutoffTriadicCoeffFamily M m
          (translateCutoffSample (triadicCubeShift Q) omega)) a0 := by
  have hQ : translateCube Q.index (originCube d Q.scale) = Q := by
    cases Q with
    | mk scale index => simp [translateCube, originCube]
  have hrw : Ch02.HomogenizationErrorOnCube Q s p q
        (coefficientCutoffTriadicCoeffFamily M m omega) a0 =
      Ch02.HomogenizationErrorOnCube (translateCube Q.index (originCube d Q.scale))
        s p q (coefficientCutoffTriadicCoeffFamily M m omega) a0 := by
    rw [hQ]
  rw [hrw]
  refine Ch02.HomogenizationErrorOnCube_translateCube_of_normalizedBlockResponseMax
    _ _ Q.index (originCube d Q.scale) s p q a0 ?_
  intro l R hR
  have hk : (originCube d Q.scale).scale - (l : ℤ) ≤ (originCube d Q.scale).scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le l)
  have hscale : R.scale = Q.scale - (l : ℤ) := by
    have h := scale_eq_sub_of_mem_descendantsAtScale hk hR
    have hred : ((originCube d Q.scale).scale -
        ((originCube d Q.scale).scale - (l : ℤ))).toNat = l := by
      simp [originCube]
    rw [hred] at h
    simpa [originCube] using h
  refine normalizedBlockResponseMax_translateCutoffSample M m (triadicCubeShift Q)
    ?_ a0 omega
  rw [cubeSet_translateCube_descendantTranslationShift Q.index l hscale]
  rfl

end

end Algsuperdiff.Section3.Provider.BadEvents
