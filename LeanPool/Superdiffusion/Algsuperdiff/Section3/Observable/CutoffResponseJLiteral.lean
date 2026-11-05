/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.LawCarrier
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.ResponseJ

/-!
# CutoffResponseJLiteral

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Literal cutoff response with an explicit comparator

This module composes the Section 3 normalized response with the genuine
lower-infinite cutoff coefficient.  It deliberately keeps the positive scalar
comparator explicit: the later Section 3.5 observable is the specialization
with the genuinely constructed running diffusivity `sigmaBar_L`, not a new
free diffusivity family.

`cutoffResponseJWithComparator M m L sigma e` has the literal manuscript value
`J(square_m, sigma^(-1/2) e, sigma^(1/2) e; a_L)` on every public cutoff
sample.  CoarseGraining supplies a.e. measurability of this response under the
actual coefficient law.  The separate `...Measurable` definition is its
everywhere measurable modification under the actual cutoff-sample law; its
exact a.e. characterization is recorded below.

## References

* ABK26, (2.4), definition of `J(U,p,q;a)`.
* ABK26, Section 3.5, Proposition `p.homogenization.step`.
-/

namespace Algsuperdiff.Section3.Observable

open MeasureTheory
open HCPolySupport HCPolySupport.Book.Ch04

noncomputable section

/-- The literal Section 3.5 response at cube scale `m`, coefficient-cutoff
scale `L`, positive comparator `sigma`, and direction `e`:
`J(square_m, sigma^(-1/2)e, sigma^(1/2)e; a_L)`. -/
noncomputable def cutoffResponseJWithComparator {d : ℕ} (M : ABKModel d)
    (cubeScale coefficientScale : ℤ) (sigma : PositiveScalar) (e : Vec d) :
    Cutoff.CutoffSample d → ℝ :=
  fun omega => responseJAtScale cubeScale sigma e
    (Cutoff.coefficientCutoff M.nu coefficientScale omega)

/-- Expand the literal cutoff response.  In particular, the cube is at
`cubeScale`, the coefficient is the genuine `a_coefficientScale`, and both
loads use the supplied comparator. -/
@[simp]
theorem cutoffResponseJWithComparator_apply {d : ℕ} (M : ABKModel d)
    (cubeScale coefficientScale : ℤ) (sigma : PositiveScalar) (e : Vec d)
    (omega : Cutoff.CutoffSample d) :
    cutoffResponseJWithComparator M cubeScale coefficientScale sigma e omega =
      ResponseJ (cubeSet (originCube d cubeScale))
        (inverseSqrtLoad sigma e) (sqrtLoad sigma e)
        (Cutoff.coefficientCutoff M.nu coefficientScale omega).toFun :=
  rfl

/-- The literal cutoff response is nonnegative on every public cutoff sample. -/
theorem cutoffResponseJWithComparator_nonneg {d : ℕ} (M : ABKModel d)
    (cubeScale coefficientScale : ℤ) (sigma : PositiveScalar) (e : Vec d)
    (omega : Cutoff.CutoffSample d) :
    0 ≤ cutoffResponseJWithComparator M cubeScale coefficientScale sigma e omega :=
  responseJAtScale_nonneg cubeScale sigma e _

end

end Algsuperdiff.Section3.Observable
