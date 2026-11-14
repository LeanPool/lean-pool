/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffCoarseBlockRepresentative
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffResponseJLiteral

/-!
# CutoffResponseJCommonRepresentative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Scalar cutoff responses from the common coarse-block representative

Section 3.5 takes a maximum over the uncountable Euclidean unit sphere.  A
separately chosen measurable modification for each direction cannot justify a
single almost-sure event for that maximum.  This module instead evaluates the
one measurable representative of the entire coarse block matrix constructed
in `CutoffCoarseBlockRepresentative`.

The scalar response is recovered as twice a doubled block response whose
second scalar-response channel has zero loads.  Since the full-block bridge is
simultaneous in all doubled loads, the final almost-everywhere theorem has its
quantifiers over every positive comparator and every direction *inside* one
event.

## References

* ABK26, (2.4), definition of `J(U,p,q;a)`.
* ABK26, Section 3.5, Proposition `p.homogenization.step`.
-/

namespace Algsuperdiff.Section3.Observable

open MeasureTheory
open HCPolySupport HCPolySupport.Book.Ch04

noncomputable section

/-- The paper-wide bound `2 ≤ d`, already stored in the standing model, supplies
the nonzero-dimension instance required by CoarseGraining's cube-response A. -/
private theorem neZero_of_model {d : ℕ} (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩

/-- The first doubled load which isolates the scalar response with loads
`p,q`. -/
def responseJFirstHalfBlockLoad {d : ℕ} (p q : Vec d) : BlockVec d :=
  ((1 / 2 : ℝ) • p, (-1 / 2 : ℝ) • q)

/-- The second doubled load which isolates the scalar response with loads
`p,q`. -/
def responseJSecondHalfBlockLoad {d : ℕ} (p q : Vec d) : BlockVec d :=
  ((1 / 2 : ℝ) • q, (-1 / 2 : ℝ) • p)

/-- Evaluate the scalar response with arbitrary loads `p,q` from the one
common full coarse-block representative. -/
noncomputable def cutoffResponseJFromCommonCoarseBlock {d : ℕ}
    (M : ABKModel d) (coefficientScale : ℤ) (Q : TriadicCube d)
    (p q : Vec d) : Cutoff.CutoffSample d → ℝ :=
  fun omega =>
    2 * cutoffBlockJFromCoarseFullBlockRepresentative M coefficientScale Q
      (responseJFirstHalfBlockLoad p q) (responseJSecondHalfBlockLoad p q) omega

/-- Fixed-load scalar evaluation of the common coarse-block representative is
measurable. -/
theorem measurable_cutoffResponseJFromCommonCoarseBlock {d : ℕ}
    (M : ABKModel d) (coefficientScale : ℤ) (Q : TriadicCube d)
    (p q : Vec d) :
    Measurable (cutoffResponseJFromCommonCoarseBlock M coefficientScale Q p q) := by
  exact (measurable_cutoffBlockJFromCoarseFullBlockRepresentative
    M coefficientScale Q (responseJFirstHalfBlockLoad p q)
      (responseJSecondHalfBlockLoad p q)).const_mul 2

/-- The Section 3.5 comparator specialization of the scalar evaluation from
the common full coarse-block representative.  Its cube and coefficient scales
remain distinct: the cube is `square_cubeScale`, while the coefficient is the
genuine cutoff `a_coefficientScale`. -/
noncomputable def cutoffResponseJWithComparatorFromCommonCoarseBlock {d : ℕ}
    (M : ABKModel d) (cubeScale coefficientScale : ℤ)
    (sigma : PositiveScalar) (e : Vec d) : Cutoff.CutoffSample d → ℝ :=
  cutoffResponseJFromCommonCoarseBlock M coefficientScale
    (originCube d cubeScale) (inverseSqrtLoad sigma e) (sqrtLoad sigma e)

/-- For a fixed comparator and direction, evaluation of the common coarse
block is measurable. -/
theorem measurable_cutoffResponseJWithComparatorFromCommonCoarseBlock
    {d : ℕ} (M : ABKModel d) (cubeScale coefficientScale : ℤ)
    (sigma : PositiveScalar) (e : Vec d) :
    Measurable
      (cutoffResponseJWithComparatorFromCommonCoarseBlock M cubeScale
        coefficientScale sigma e) :=
  measurable_cutoffResponseJFromCommonCoarseBlock M coefficientScale
    (originCube d cubeScale) (inverseSqrtLoad sigma e) (sqrtLoad sigma e)

/-- One common probability-one event identifies the literal cutoff response
with evaluation of the single full coarse-block representative for every
positive comparator and every direction.  In particular, no intersection of
direction-indexed null sets is used. -/
theorem ae_forall_cutoffResponseJWithComparator_eq_fromCommonCoarseBlock
    {d : ℕ} (M : ABKModel d) (cubeScale coefficientScale : ℤ) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (sigma : PositiveScalar) (e : Vec d),
        cutoffResponseJWithComparator M cubeScale coefficientScale sigma e omega =
          cutoffResponseJWithComparatorFromCommonCoarseBlock M cubeScale
            coefficientScale sigma e omega := by
  let : NeZero d := neZero_of_model M
  filter_upwards
    [ae_forall_blockJObservableCubeSet_eq_cutoffCoarseRepresentative M
      coefficientScale (originCube d cubeScale)] with omega hblock
  intro sigma e
  let a := Cutoff.coefficientCutoff M.nu coefficientScale omega
  let p := inverseSqrtLoad sigma e
  let q := sqrtLoad sigma e
  have hzero := hblock (0 : BlockVec d) (0 : BlockVec d)
  have hzeroFirst :
      0 ≤ restrictionResponseJObservableCubeSet (originCube d cubeScale) 0 0 a :=
    restrictionResponseJObservableCubeSet_nonneg (originCube d cubeScale) 0 0 a
  have hzeroSecond :
      0 ≤ restrictionResponseJObservableCubeSet
        (originCube d cubeScale) 0 0 (adjointReg a) :=
    restrictionResponseJObservableCubeSet_nonneg
      (originCube d cubeScale) 0 0 (adjointReg a)
  have hadjointZero :
      restrictionResponseJObservableCubeSet
        (originCube d cubeScale) 0 0 (adjointReg a) = 0 := by
    have hsum :
        (1 / 2 : ℝ) *
            restrictionResponseJObservableCubeSet (originCube d cubeScale) 0 0 a +
            (1 / 2 : ℝ) *
              restrictionResponseJObservableCubeSet
                (originCube d cubeScale) 0 0 (adjointReg a) = 0 := by
      calc
        (1 / 2 : ℝ) *
            restrictionResponseJObservableCubeSet (originCube d cubeScale) 0 0 a +
              (1 / 2 : ℝ) *
                restrictionResponseJObservableCubeSet
                  (originCube d cubeScale) 0 0 (adjointReg a) =
            blockJObservableCubeSetBlockVec (originCube d cubeScale)
              (0 : BlockVec d) (0 : BlockVec d) a := by
                simp [blockJObservableCubeSetBlockVec]
        _ = cutoffBlockJFromCoarseFullBlockRepresentative M coefficientScale
              (originCube d cubeScale) (0 : BlockVec d) (0 : BlockVec d) omega := hzero
        _ = 0 := by
          simp [cutoffBlockJFromCoarseFullBlockRepresentative,
            blockJQuadraticFullBlockMat, fullBlockQuadraticCh04, fullBlockReflect,
            toFullBlockVec, dotProduct, Matrix.mulVec, blockVecDot, vecDot]
    nlinarith
  have hresponse := hblock (responseJFirstHalfBlockLoad p q)
    (responseJSecondHalfBlockLoad p q)
  have hpDiff : (1 / 2 : ℝ) • p - (-1 / 2 : ℝ) • p = p := by
    ext i
    simp
    ring
  have hqDiff : (1 / 2 : ℝ) • q - (-1 / 2 : ℝ) • q = q := by
    ext i
    simp
    ring
  have hpAdd : (-1 / 2 : ℝ) • p + (1 / 2 : ℝ) • p = 0 := by
    ext i
    simp
    ring
  have hqAdd : (1 / 2 : ℝ) • q + (-1 / 2 : ℝ) • q = 0 := by
    ext i
    simp
    ring
  calc
    cutoffResponseJWithComparator M cubeScale coefficientScale sigma e omega =
        restrictionResponseJObservableCubeSet (originCube d cubeScale) p q a := rfl
    _ = 2 * blockJObservableCubeSetBlockVec (originCube d cubeScale)
          (responseJFirstHalfBlockLoad p q) (responseJSecondHalfBlockLoad p q) a := by
      rw [show blockJObservableCubeSetBlockVec (originCube d cubeScale)
          (responseJFirstHalfBlockLoad p q) (responseJSecondHalfBlockLoad p q) a =
          (1 / 2 : ℝ) *
              restrictionResponseJObservableCubeSet (originCube d cubeScale) p q a +
            (1 / 2 : ℝ) *
              restrictionResponseJObservableCubeSet
                (originCube d cubeScale) 0 0 (adjointReg a) by
        simp only [blockJObservableCubeSetBlockVec, responseJFirstHalfBlockLoad,
          responseJSecondHalfBlockLoad, blockJObservableCubeSet_apply]
        rw [hpDiff, hqDiff, hpAdd, hqAdd]]
      rw [hadjointZero]
      ring
    _ = 2 * cutoffBlockJFromCoarseFullBlockRepresentative M coefficientScale
          (originCube d cubeScale) (responseJFirstHalfBlockLoad p q)
            (responseJSecondHalfBlockLoad p q) omega := by rw [hresponse]
    _ = cutoffResponseJWithComparatorFromCommonCoarseBlock M cubeScale
          coefficientScale sigma e omega := by
      rfl

end

end Algsuperdiff.Section3.Observable
