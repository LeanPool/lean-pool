/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.AnnealedLimitPassage
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Junctions

/-!
# AnnealedLimitJunction

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The annealed limit passage, wired into Junction 3

`Closure.Junctions.AnnealedSplitEndpoint` (Junction 3, and the passage line)
asserts

```
  P . bfAhom_{n+h} P  <=  principalEnergyAverage + cgamma^10 ,
```

with `P = recurrenceP (sigmaBar M n) e e'`.  Its docstring names three joint
producers: the proved structural split, the lane `gamma10-final` fluctuation
endpoint, and *the annealed identification* `P. bfAhom_m P = lim_K E[P.
bfA_m(cu_K) P]`.

This module supplies the third and, with it, **removes the limit from the
obligation**: it reduces `AnnealedSplitEndpoint` to the same inequality with the
left-hand side replaced by the finite-volume expectation
`E[P . bfA_{n+h}(cu_K) P]` at a *single* cube scale `K`, freely chosen by the
producer.

The reduction is one `le_trans` against
`Closure.blockVecDot_recurrenceP_annealedLimitBlock_le_integral_coarseBlockMatrix`,
whose content is the Loewner monotonicity of the annealed cube matrices (ABK26)
together with `e.homs.defs`.  No `limsup` is formed anywhere records the same
"finite grid, not `limsup`" reading for `e.lower.bound.pre1` (Junction 1), and
the reduction below gives Junction 3 the same shape.

## What is left to the producer

Exactly the finite-volume half of Steps 1--3:

```
  E[ P . bfA_{n+h}(cu_K) P ]  <=  principalEnergyAverage M n h Kc j e e' wD wN
                                    + cgamma^10 ,
```

i.e. `e.lower.bound.basic.split` plus `e.lower.bound.localization.terms`, read
at one grid.  Nothing in this module proves any part of it.

`annealedSplitEndpoint_of_integral_ch02CoarseBlockMatrix_le` states that
obligation with the Chapter 2 coarse matrix on `cubeDomain (cu_K)`, which is
*verbatim* the left-hand side of the proved structural split
`LocalizationRecurrenceMesh.exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded`
(averaged over the sample); the carrier identification is discharged inside
`Closure.AnnealedLimitPassage`.  A producer that integrates the split
realization-wise and then bounds the resulting descendant average by
`principalEnergyAverage + cgamma^10` therefore closes Junction 3 with a single
`exact`.

## References

* ABK26, `l.approximate.recurrence.formula`, Steps 1--3 and Step 6.
* ABK26, `e.homs.defs` and (Loewner monotonicity).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open Filter MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector

noncomputable section

variable {d : ℕ}

/-- **Junction 3 from a single finite grid, at the structural split's carrier.**

: `hfinite` is the caller-supplied finite-volume half of Steps 1--3, stated
with the Chapter 2 coarse matrix on `cubeDomain (cu_K)` at the cutoff's triadic
coefficient family --- verbatim the left-hand side of the proved split
`LocalizationRecurrenceMesh.exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded`,
averaged over the sample.  The carrier identification and the passage to the
annealed limit are both discharged here. -/
theorem annealedSplitEndpoint_of_integral_ch02CoarseBlockMatrix_le (M : ABKModel d)
    (n : ℤ) (h : ℕ) (Kc : ℤ) (j : ℕ) (K : ℤ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    (hfinite :
      ∫ omega : CutoffSample d,
          blockVecDot (recurrenceP (Annealed.sigmaBar M n) e e')
            (blockMatVecMul
              (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d K))
                ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn
                  (originCube d K)))
              (recurrenceP (Annealed.sigmaBar M n) e e'))
          ∂(cutoffSampleLaw M).toMeasure ≤
        principalEnergyAverage M n h Kc j e e' wD wN + M.gamma ^ (10 : ℕ)) :
    AnnealedSplitEndpoint M n h Kc j e e' wD wN :=
  le_trans
    (blockVecDot_recurrenceP_annealedLimitBlock_le_integral_ch02CoarseBlockMatrix M n h
      K e e')
    hfinite

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
