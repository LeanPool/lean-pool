/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationGluingCompetitor
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationSelectionVariation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationSelectionExistence

/-!
# LocalizationSelectionFamily

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the carrier restriction behind the per-cell minimizer selection

Source sentence and display in ABK26:

* the `X_z` display, which defines the cell field as the `argmin` of
  `fint_{z+cu_n} (1/2) X . bfA_m X` over

  ```
  bfAhom_{m-h}^{-1/2} ( e' + grad w_{D,e}^{(K)} ,
                        e  + grad w_{N,e'}^{(K)} + shom_{m-h}^{-1} h e' )
    + (L^2_{pot,0} x Lsolo)(z+cu_n);
  ```

`LocalizationGluingAdmissible.lean` and `LocalizationGluingCompetitor.lean`
prove that sentence *conditionally*, carrying two caller propositions: `hG`
(the background lies in the affine class on `cu_K`) and `hX` (each cell field
lies in the background's affine class on its own cell).  The family
`z |-> X_z` that discharges `hX`, built out of the existence theorem of
`LocalizationSelectionExistence.lean` and the variation of
`LocalizationSelectionVariation.lean`, is produced at the actual carriers in
`LocalizationActualSplit.lean` (`exists_localizationActualCellFields`,
`exists_localizationActualCellSplit` and its competitor composition
`exists_localizationActualCellSplit_blockVecDot_coarseBlockMatrix_le`).

This module supplies the one carrier fact that lets those cell problems be
posed at all.

## What is proved

* `memVectorL2_of_subset` -- the elementary restriction of vector-`L^2`
  membership along an inclusion of carriers.  A field square integrable on the
  localization cube is square integrable on each of its cells, which is what
  the per-cell variational problems need of the background.

## Divergences from the printed statement

These describe the selection lane this module feeds, wherever its statements
are made.

* **The site set.**  As in `LocalizationGluingAdmissible.lean`, the
  manuscript's site set `3^n Z^d cap cu_K` is rendered as the full descendant
  family `descendantsAtDepth Q j`.
* **One direction only.**  The glued field is produced as one admissible
  competitor for `bfA_m(cu_K)`, never as a minimizer of the cube problem.
* **The per-cell coefficient.**  The cell variational problems are posed at a
  *family* `aCell : (R : TriadicCube d) -> CoeffOn (cubeDomain R)`, not at a
  restriction of the cube coefficient.  A caller that wants the manuscript's
  `bfA_m` on every cell instantiates it with CoarseGraining's
  `Book.Ch02.pointwiseCoeffOnRestrict`, whose value differs from the cube
  coefficient only on a null set.
* **The mesh average is absent.**  `avsum_{z in 3^n Z^d cap cu_K}` and the
  tiling identity are a separate lane's item; nothing below uses or asserts
  them.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Vector-`L²` membership restricts along an inclusion of carriers. -/
theorem memVectorL2_of_subset {U V : Set (Vec d)} (hsub : V ⊆ U) {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) : MemVectorL2 V f :=
  hf.mono_measure (Measure.restrict_mono hsub le_rfl)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
