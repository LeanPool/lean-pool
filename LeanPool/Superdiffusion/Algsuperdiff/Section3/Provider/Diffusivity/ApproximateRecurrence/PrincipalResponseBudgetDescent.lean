/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitch
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.CubeMonotonicity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.OneCube
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.ToLambdasUpper

/-!
# PrincipalResponseBudgetDescent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# Provider: the deterministic leg of the budget of `e.use.also.for.the.upper.bound`

This module supplies the two *deterministic* inequalities of the chain printed
in ABK26, namely the passage

```
  bfJ(cu_n, bfAhom^{-1/2} e, bfAhom^{1/2} e; a)
    <=  mathcalE_{s,infinity,2}(cu_n; a, a_0)^2
    <=  3^{2 s (N - n)} mathcalE_{s,infinity,2}(cu_N; a, a_0)^2 ,
```

for an arbitrary triadic coefficient family `a`, at the isotropic comparator
`a_0 = sigma Id`, on the tower of centered cubes `cu_n subset cu_N`.  The first
step is the first inequality of `e.mathcalE.monotone.ordered`, *squared*; the
second is `e.bound.one.cube.by.mathcalE`, in its per-descendant form, also
squared.

Everything below is pointwise in the coefficient field: no law, no expectation,
no induction state.  The probabilistic half of the budget is the second moment
of `mathcalE`, which is not touched here.

## The probe

What is proved first is that this pair is literally an element of
CoarseGraining's normalized block-response value set
`Ch02.normalizedBlockResponseValueSet` of the comparator
`Observable.isotropicComparatorMatrix sigma`, whose doubled unit witness is
`Sum.elim e_1 e_2`; that is exactly the sense in which `mathcalE` maximizes
over the same probe family.  The manuscript's normalization `|e| = 1` is the
hypothesis `hE : blockVecDot = 1`, which
`...PrincipalResponseSwitch.exists_blockVecDot_self_eq_one` shows is
satisfiable.

## The exponent

The third line of the manuscript's chain carries the factor `3^{t(m-h-n)}` in
front of the *second moment* of `mathcalE`.  Composing the first inequality of
`e.mathcalE.monotone.ordered` (which squares) with
`e.bound.one.cube.by.mathcalE` (stated for `mathcalE` itself) produces `3^{2 t
(m-h-n)}`, not `3^{t(m-h-n)}`.  Under the manuscript's own scale choice both
factors are absolute constants, so nothing downstream moves.

## Main results

* `doubledResponseJ_annealedProbe_mem_normalizedBlockResponseValueSet`: the tex
  probe is a probe of `mathcalE`.
* `doubledResponseJ_annealedProbe_le_sq_homogenizationErrorOnCube`: the first
  inequality of `e.mathcalE.monotone.ordered`, squared, at that probe.
* `homogenizationErrorOnCube_originCube_le_rpow_mul`:
  `e.bound.one.cube.by.mathcalE` on the centered tower.

## References

* ABK26, `e.mathcalE.monotone.ordered`.
* ABK26, `e.bound.one.cube.by.mathcalE`.
* ABK26, `e.use.also.for.the.upper.bound` (statement, proof, and the
  `align*` chain).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.ErrorComparison

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Real-power bookkeeping -/

private theorem rpow_eq_hPow (x y : ℝ) : Real.rpow x y = x ^ y := rfl

private theorem rpow_three_two_mul_eq_sq (a : ℝ) :
    (3 : ℝ) ^ (2 * a) = ((3 : ℝ) ^ a) ^ 2 := by
  rw [sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  ring_nf

/-! ## The tex probe is a probe of `mathcal E` -/

omit [NeZero d] in
/-- **ABK26 against `d.mathcal.E`.**  The pair
`(bfAhom^{-1/2} e, bfAhom^{1/2} e)` at the isotropic comparator `sigma Id`
realizes the doubled response `bfJ` as an element of the normalized
block-response value set whose supremum `mathcalE` maximizes.  The doubled
witness is `Sum.elim e_1 e_2`, whose squared Euclidean norm is the manuscript's
`|e|^2`. -/
theorem doubledResponseJ_annealedProbe_mem_normalizedBlockResponseValueSet
    (Q : TriadicCube d) (F : Ch02.TriadicCoeffFamily d)
    (sigma : Observable.PositiveScalar) {Ev : BlockVec d}
    (hE : blockVecDot Ev Ev = 1) :
    Ch02.doubledResponseJ (Ch02.cubeDomain Q) (F.coeffOn Q)
        (annealedProbePotential sigma Ev) (annealedProbeFlux sigma Ev) ∈
      Ch02.normalizedBlockResponseValueSet Q F
        (Observable.isotropicComparatorMatrix sigma) := by
  have hsig : (0 : ℝ) < (sigma : ℝ) := sigma.2
  refine ⟨Sum.elim Ev.1 Ev.2, ?_, ?_⟩
  · rw [fullBlockVecNormSq_eq_add]
    change vecNormSq Ev.1 + vecNormSq Ev.2 = 1
    simpa [vecNormSq, blockVecDot] using hE
  · show _ = Ch02.doubledResponseJ (Ch02.cubeDomain Q) (F.coeffOn Q) _ _
    rw [show Observable.isotropicComparatorMatrix (d := d) sigma
        = scalarMatrix (d := d) (sigma : ℝ) from rfl,
      ofFullBlockVec_constantFullBlockMatrixInvSqrt_scalarMatrix hsig,
      ofFullBlockVec_constantFullBlockMatrixSqrt_scalarMatrix hsig]
    rfl

/-! ## The first inequality of `e.mathcalE.monotone.ordered`, squared -/

/-- **ABK26, first inequality, squared, at the annealed probe.**  The doubled
response of a cube at the probe `(bfAhom^{-1/2} e, bfAhom^{1/2} e)` is at most
the square of `mathcalE_{s,infinity,2}` of that cube. -/
theorem doubledResponseJ_annealedProbe_le_sq_homogenizationErrorOnCube
    (Q : TriadicCube d) (F : Ch02.TriadicCoeffFamily d)
    (sigma : Observable.PositiveScalar) {Ev : BlockVec d}
    (hE : blockVecDot Ev Ev = 1) {s : ℝ} (hs : 0 < s) :
    Ch02.doubledResponseJ (Ch02.cubeDomain Q) (F.coeffOn Q)
        (annealedProbePotential sigma Ev) (annealedProbeFlux sigma Ev) ≤
      Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
        (Observable.isotropicComparatorMatrix sigma) ^ 2 := by
  have hsig : (0 : ℝ) < (sigma : ℝ) := sigma.2
  have ha0 : Observable.isotropicComparatorMatrix (d := d) sigma
      = scalarMatrix (d := d) (sigma : ℝ) := rfl
  have hmem :=
    doubledResponseJ_annealedProbe_mem_normalizedBlockResponseValueSet Q F sigma hE
  have hbdd : BddAbove (Ch02.normalizedBlockResponseValueSet Q F
      (Observable.isotropicComparatorMatrix sigma)) := by
    rw [ha0]
    exact normalizedBlockResponseValueSet_scalarMatrix_bddAbove Q F hsig
  have hJ := le_csSup hbdd hmem
  have hmax : Ch02.normalizedBlockResponseMax Q F
      (Observable.isotropicComparatorMatrix sigma) ≤
      Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
        (Observable.isotropicComparatorMatrix sigma) ^ 2 := by
    have hnn := Ch02.normalizedBlockResponseMax_nonneg Q F
      (Observable.isotropicComparatorMatrix sigma)
    have hroot :=
      rpow_half_normalizedBlockResponseMax_le_homogenizationErrorOnCube_infinity_finite
        Q F (Observable.isotropicComparatorMatrix sigma) hs (by norm_num : (1 : ℝ) ≤ 2)
    have hsqrt : Real.rpow (Ch02.normalizedBlockResponseMax Q F
        (Observable.isotropicComparatorMatrix sigma)) (1 / 2 : ℝ) =
        Real.sqrt (Ch02.normalizedBlockResponseMax Q F
          (Observable.isotropicComparatorMatrix sigma)) :=
      (Real.sqrt_eq_rpow _).symm
    rw [hsqrt] at hroot
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
    rwa [Real.sq_sqrt hnn] at hsq
  exact le_trans hJ hmax

/-! ## `e.bound.one.cube.by.mathcalE` on the centered tower -/

/-- **ABK26, per-descendant form, on the centered cubes.**
For `n <= N`,
`mathcalE_{s,infinity,2}(cu_n) <= 3^{s(N-n)} mathcalE_{s,infinity,2}(cu_N)`. -/
theorem homogenizationErrorOnCube_originCube_le_rpow_mul
    (F : Ch02.TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ} (hs : 0 < s)
    {N n : ℤ} (hn : n ≤ N) :
    Ch02.HomogenizationErrorOnCube (originCube d n) s .infinity (.finite 2) F a0 ≤
      Real.rpow (3 : ℝ) (s * ((Int.toNat (N - n) : ℕ) : ℝ)) *
        Ch02.HomogenizationErrorOnCube (originCube d N) s .infinity (.finite 2) F a0 := by
  have h := homogenizationErrorOnCube_infinity_finite_le_of_mem_descendantsAtScale
    (Q := originCube d N) (R := originCube d n) (k := n) F a0 hs
    (by norm_num : (1 : ℝ) ≤ 2) (originCube_mem_descendantsAtScale hn)
  have hscale : (originCube d N).scale = N := rfl
  rwa [hscale] at h

/-! ## The deterministic leg -/

/-- **The deterministic leg of the budget of ABK26.**

At the annealed probe of ABK26, on the centered tower `cu_n subset cu_N`,

```
  bfJ(cu_n, bfAhom^{-1/2} e, bfAhom^{1/2} e; a)
    <=  3^{2 s (N-n)} mathcalE_{s,infinity,2}(cu_N; a, sigma Id)^2 .
```

No law and no induction state occur; the remaining half of the manuscript's
chain is the second moment of the right-hand side. -/
theorem doubledResponseJ_annealedProbe_originCube_le
    (F : Ch02.TriadicCoeffFamily d) (sigma : Observable.PositiveScalar)
    {Ev : BlockVec d} (hE : blockVecDot Ev Ev = 1) {s : ℝ} (hs : 0 < s)
    {N n : ℤ} (hn : n ≤ N) :
    Ch02.doubledResponseJ (Ch02.cubeDomain (originCube d n))
        (F.coeffOn (originCube d n))
        (annealedProbePotential sigma Ev) (annealedProbeFlux sigma Ev) ≤
      (3 : ℝ) ^ (2 * s * ((Int.toNat (N - n) : ℕ) : ℝ)) *
        Ch02.HomogenizationErrorOnCube (originCube d N) s .infinity (.finite 2) F
          (Observable.isotropicComparatorMatrix sigma) ^ 2 := by
  have hJ := doubledResponseJ_annealedProbe_le_sq_homogenizationErrorOnCube
    (originCube d n) F sigma hE hs
  have hd := homogenizationErrorOnCube_originCube_le_rpow_mul (N := N) (n := n) F
    (Observable.isotropicComparatorMatrix sigma) hs hn
  rw [rpow_eq_hPow] at hd
  have hnn := homogenizationErrorOnCube_infinity_two_nonneg (originCube d n) F
    (Observable.isotropicComparatorMatrix sigma) hs
  have hsq := pow_le_pow_left₀ hnn hd 2
  rw [mul_pow, ← rpow_three_two_mul_eq_sq, ← mul_assoc] at hsq
  exact le_trans hJ hsq

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
