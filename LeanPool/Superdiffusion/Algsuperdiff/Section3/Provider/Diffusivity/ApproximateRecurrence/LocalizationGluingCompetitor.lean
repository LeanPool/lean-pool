/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationGluingAdmissible
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationBasicSplit

/-!
# LocalizationGluingCompetitor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: inserting the glued localization field as a competitor

This module joins the gluing admissibility of
`LocalizationGluingAdmissible.lean` to the cell algebra of
`LocalizationBasicSplit.lean`, producing the second clause of the manuscript's
sentence:

```
... and we may insert it into the minimization problem in
(e.variational.mu.U.P) for bfA_m(cu_K).  We obtain
  P . bfA_m(cu_K) P  <=  avsum_z fint_{z+cu_n} X_z . bfA_m X_z ...
```

## What is proved

* `blockVecDot_coarseBlockMatrix_le_two_mul_doubledMuValue_glued` — the direct
  composition: the glued field is a competitor for `bfA_m(cu_K)`, so
  `P . bfA_m(cu_K) P <= 2 doubledMuValue(cu_K, glued)`.  This is the generic
  conditional form underlying the manuscript's insertion step (with the factor
  `2` of `LocalizationBasicSplit.lean`'s normalization convention); the
  manuscript's own step is performed at its specific minimizers, where `hG`
  and `hX` are derived rather than assumed.

The two ingredients it composes are proved elsewhere:
`LocalizationGluingAdmissible.isDoubledMuAdmissible_gluedDoubledField`, that the
glued field is admissible at `P` on the cube when every cell field is, and
`LocalizationGluingAdmissible.gluedDoubledField_eval_of_mem_openCubeSet`, that
on each open cell the glued field *is* that cell's field --- the pointwise
input the mesh-average step of `e.lower.bound.basic.split` consumes.  The mesh
average itself is not treated here.

## Divergences from the printed statement

* No declaration in this module or in `LocalizationGluingAdmissible.lean`
  asserts the reverse inequality or that the glued field is a minimizer.
* **The factor two.**  As in `LocalizationBasicSplit.lean`, the manuscript's
  `fint_U X . bfA X` is twice CoarseGraining's `doubledMuValue`, whose
  integrand is `1/2 X . bfA X`; the factor is carried explicitly.
* **The mesh average is absent.**  `avsum_{z in 3^n Z^d cap cu_K}` and the
  tiling identity `fint_{cu_K} f = avsum_z fint_{z+cu_n} f` are a separate
  lane's item; nothing below uses or asserts them.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-- **The insertion step, at the first line of `e.lower.bound.basic.split`.**

The glued field `sum_z X_z 1_{z+cu_n}` is an admissible competitor for
`bfA_m(cu_K)`, hence

```
P . bfA_m(cu_K) P  <=  fint_{cu_K} (sum_z X_z 1_{z+cu_n}) . bfA_m (sum_z X_z 1_{z+cu_n}) .
```

Per this direction, and only this direction, is available. -/
theorem blockVecDot_coarseBlockMatrix_le_two_mul_doubledMuValue_glued
    {Q : TriadicCube d} {j : ℕ} (a : CoeffOn (cubeDomain Q)) (P : BlockVec d)
    {G : DoubledField d} {X : TriadicCube d → DoubledField d}
    (hG : IsDoubledMuAdmissible (cubeDomain Q) P G)
    (hX : ∀ R ∈ descendantsAtDepth Q j, IsDoubledTestField (cubeDomain R) (X R - G)) :
    blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix (cubeDomain Q) a) P) ≤
      2 * doubledMuValue (cubeDomain Q) a (gluedDoubledField Q j X) :=
  blockVecDot_coarseBlockMatrix_le_two_mul_doubledMuValue a P
    (isDoubledMuAdmissible_gluedDoubledField hG hX)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
