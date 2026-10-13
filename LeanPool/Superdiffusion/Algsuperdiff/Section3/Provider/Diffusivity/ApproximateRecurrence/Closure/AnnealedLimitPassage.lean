/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.Monotonicity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponsePDef

/-!
# AnnealedLimitPassage

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The annealed limit passage `P . bfAhom_m P = lim_K E[P . bfA_m(cu_K) P]`

Step 6 of `l.approximate.recurrence.formula` opens with the chain

```
  (e'; e) . bfAhom_{m-h}^{-1/2} bfAhom_m bfAhom_{m-h}^{-1/2} (e'; e)
    = P . bfAhom_m P
    = lim_{K -> infty} E[ P . bfA_m(cu_K) P ] .
```

The second equality is what this module supplies, at an **arbitrary** fixed
doubled load `P : BlockVec d` (the probe load `recurrenceP` of `e.recurrence.P.def`
is only one instance, recorded at the end).

## Why the passage is available, and from what

`bfAhom_m` is *defined* in the manuscript, at `e.homs.defs`, as the
infinite-volume limit `lim_{n} E[bfA_m(cu_n)]` of the annealed cube matrices.
In this repository that definition is carried by the unique-choice
characterization `Annealed.sigmaBar_characterization`, read through
`annealedLimitBlock` as
`ApproximateRecurrence.annealedLimitBlock_sigmaBar_characterization`: the
doubled annealed matrices of the genuine coefficient cutoff converge, in the
finite dimensional space `FullBlockMat d`, to `annealedLimitBlock (sigmaBar M
m)`.

The passage is therefore not an analytic input: it is the *continuity of a fixed
doubled quadratic form* on a finite-dimensional matrix space, composed with that
convergence.  Nothing probabilistic is added.

## The bridge chain, link by link

The manuscript writes the finite-volume side as an expectation
`E[P . bfA_m(cu_K) P]`, while the repository's annealed layer carries the
*matrix* `bfAhom_m(cu_K) = E[bfA_m(cu_K)]` (`Ch04.annealedBlockMatrixAtScale`).
The two are identified here in five steps.

1. `blockVecDot_blockMatVecMul_eq_sum` --- the doubled quadratic form is the
   finite bilinear expansion `sum_{alpha,beta} P_alpha A_{alpha beta} P_beta`
   over `BlockCoord d`.  Pure algebra.
2. `tendsto_blockVecDot_blockMatVecMul_of_tendsto_toFullBlockMat` --- entrywise
   convergence of block matrices gives convergence of every fixed doubled
   quadratic form.  Pure topology of `Pi` limits.
3. `blockVecDot_annealedBlockMatrix_eq_integral` --- because the annealed
   matrix is defined entrywise by integration, its doubled quadratic form is
   the expectation of the doubled quadratic form of the coarse matrix.  This is
   the only step with a hypothesis of substance: it needs entrywise
   integrability.  Both halves are CoarseGraining's
   `Ch04.integral_blockVecDot_blockMatVecMul_eq_of_integrable_entries` and
   `Ch04.integrable_blockVecDot_blockMatVecMul_of_integrable_entries`, fed the
   proved
   `Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix`.
4. `integral_coefficientCutoffLaw_eq_integral_cutoffSampleLaw` --- the genuine
   coefficient law is by definition the pushforward of `cutoffSampleLaw M` along
   `coefficientCutoff M.nu m`, so the expectation can be read on the sample
   carrier `CutoffSample d` that the closure junctions integrate over.
5. `coarseBlockMatrix_cubeSet_coefficientCutoff_eq_ch02` --- the annealed layer's coarse
   matrix is built on the `Set`/`RegCoeffField` carrier (`CoarseGraining.coarseBlockMatrix
   (cubeSet Q) a.toFun`), whereas the proved *structural split* of Steps 1--3
   (`LocalizationRecurrenceMesh.exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded`)
   states its left-hand side on the `Domain`/`CoeffOn` carrier (`Ch02.coarseBlockMatrix
   (cubeDomain Q) ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn Q)`).  The two
   carriers are identified by CoarseGraining's
   `Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField`
   together with `Ch02.coarseBlockMatrix_eq_ofAEEq`, exactly as
   `Provider.Base.AnnealedPlateau` already does for the upper-left block.  This link is
   what makes the finite-volume side of the passage *literally* the expectation of the
   split's left-hand side.

## What consumers actually use

Downstream the passage is consumed in its **one-sided, finite-volume** form

* `blockVecDot_annealedLimitBlock_le_annealedBlockMatrixAtScale`, its expectation
  reading
  `blockVecDot_annealedLimitBlock_le_integral_coarseBlockMatrix_cutoffSampleLaw`,
  and that reading at the structural split's carrier,
  `blockVecDot_annealedLimitBlock_le_integral_ch02CoarseBlockMatrix`:

the annealed limit form is below the annealed cube form *at every single
scale*, because the annealed cube matrices are Loewner nonincreasing (ABK26,
proved as
`Provider.Annealed.coefficientCutoffLaw_blockMatLoewnerLE_annealedBlockMatrixAtScale`).
That is what lets a bound proved at one finite grid be transported to the limit
without ever forming a `limsup`.  records the same principle for
`e.lower.bound.pre1`: a `limsup` bound implies nothing at any fixed grid, so
the finite-volume display is the one a junction can consume.

## References

* ABK26, `e.homs.defs.U.pre`, `e.homs.defs`.
* ABK26, `l.approximate.recurrence.formula`, Step 6.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open Filter MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## The doubled quadratic form as a finite bilinear expansion -/

/-- The doubled bilinear form `X . A Y` expanded over the doubled coordinate
type `BlockCoord d = Fin d + Fin d`. -/
theorem blockVecDot_blockMatVecMul_eq_sum (A : BlockMat d) (X Y : BlockVec d) :
    blockVecDot X (blockMatVecMul A Y) =
      ∑ alpha : BlockCoord d, ∑ beta : BlockCoord d,
        toFullBlockVec X alpha * (toFullBlockMat A alpha beta * toFullBlockVec Y beta) := by
  classical
  simp only [Fintype.sum_sum_type, toFullBlockVec, toFullBlockMat, blockVecDot,
    blockMatVecMul, vecDot, matVecMul, Pi.add_apply, Finset.mul_sum, mul_add,
    Finset.sum_add_distrib]
  ring

/-! ## Continuity of a fixed doubled quadratic form -/

/-- **Continuity of the doubled bilinear form.**  If a family of block matrices
converges entrywise, then its doubled bilinear form at any *fixed* pair of
doubled vectors converges to the form of the limit.  Conditional helper: the
convergence hypothesis is supplied by the caller. -/
theorem tendsto_blockVecDot_blockMatVecMul_of_tendsto_toFullBlockMat
    {iota : Type*} {l : Filter iota} {f : iota → BlockMat d} {L : BlockMat d}
    (X Y : BlockVec d)
    (hf : Tendsto (fun k => toFullBlockMat (f k)) l (nhds (toFullBlockMat L))) :
    Tendsto (fun k => blockVecDot X (blockMatVecMul (f k) Y)) l
      (nhds (blockVecDot X (blockMatVecMul L Y))) := by
  classical
  simp only [blockVecDot_blockMatVecMul_eq_sum]
  refine tendsto_finsetSum _ fun alpha _ => tendsto_finsetSum _ fun beta _ => ?_
  exact Filter.Tendsto.const_mul _
    (Filter.Tendsto.mul_const _ (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hf alpha) beta))

/-! ## The passage at the annealed cube matrices -/

/-- **`e.homs.defs` at a fixed doubled load.**  The doubled quadratic forms of the
annealed cube matrices of the genuine coefficient cutoff converge to the
doubled quadratic form of `annealedLimitBlock (sigmaBar M m)`.  Unconditional. -/
theorem tendsto_blockVecDot_annealedBlockMatrixAtScale (M : ABKModel d) (m : ℤ)
    (X : BlockVec d) :
    Tendsto
      (fun K : ℕ =>
        blockVecDot X
          (blockMatVecMul
            (Ch04.annealedBlockMatrixAtScale (coefficientCutoffLaw M m) (K : ℤ)) X))
      atTop
      (nhds
        (blockVecDot X
          (blockMatVecMul (annealedLimitBlock (Annealed.sigmaBar M m)) X))) :=
  tendsto_blockVecDot_blockMatVecMul_of_tendsto_toFullBlockMat X X
    (annealedLimitBlock_sigmaBar_characterization M m).1

/-- **The one-sided finite-volume form of the passage.**  By ABK26 the annealed
cube matrices are Loewner nonincreasing in the scale, so the infinite-volume
doubled form sits below the annealed doubled form at *every* single cube scale.
Unconditional. -/
theorem blockVecDot_annealedLimitBlock_le_annealedBlockMatrixAtScale
    (M : ABKModel d) (m : ℤ) (K : ℤ) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (annealedLimitBlock (Annealed.sigmaBar M m)) X) ≤
      blockVecDot X
        (blockMatVecMul
          (Ch04.annealedBlockMatrixAtScale (coefficientCutoffLaw M m) K) X) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  refine le_of_tendsto (tendsto_blockVecDot_annealedBlockMatrixAtScale M m X) ?_
  filter_upwards [eventually_ge_atTop K.toNat] with k hk
  have hKk : K ≤ (k : ℤ) := le_trans (Int.self_le_toNat K) (by exact_mod_cast hk)
  have hmono :=
    Provider.Annealed.coefficientCutoffLaw_blockMatLoewnerLE_annealedBlockMatrixAtScale
      M m hKk X
  linarith [hmono]

/-! ## The annealed matrix's quadratic form as an expectation -/

/-- The doubled quadratic form of the coarse cube matrix is integrable for the
genuine coefficient cutoff law.  Unconditional: the entrywise integrability is
the proved cutoff moment layer. -/
theorem integrable_blockVecDot_coarseBlockMatrix (M : ABKModel d) (m : ℤ)
    (Q : TriadicCube d) (X Y : BlockVec d) :
    Integrable
      (fun a : RegCoeffField d =>
        blockVecDot X (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a.toFun) Y))
      (coefficientCutoffLaw M m) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  exact Ch04.integrable_blockVecDot_blockMatVecMul_of_integrable_entries
    (fun alpha beta =>
      Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
        M m Q alpha beta) X Y

/-- **`e.homs.defs.U.pre` at a fixed doubled load.**  Since the annealed matrix
`bfAhom_m(U) = E[bfA_m(U)]` is defined entrywise by integration, its doubled
bilinear form is the expectation of the coarse doubled bilinear form.
Unconditional. -/
theorem blockVecDot_annealedBlockMatrix_eq_integral (M : ABKModel d) (m : ℤ)
    (Q : TriadicCube d) (X Y : BlockVec d) :
    blockVecDot X
        (blockMatVecMul
          (Ch04.annealedBlockMatrix (coefficientCutoffLaw M m) (cubeSet Q)) Y) =
      ∫ a : RegCoeffField d,
        blockVecDot X (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a.toFun) Y)
        ∂(coefficientCutoffLaw M m) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  exact (Ch04.integral_blockVecDot_blockMatVecMul_eq_of_integrable_entries
    (fun alpha beta =>
      Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
        M m Q alpha beta) X Y).symm

/-- The genuine coefficient cutoff law is by construction the pushforward of the
canonical sample law along `coefficientCutoff`, so its expectations are
expectations over `CutoffSample d`.  Conditional helper: a.e. strong
measurability is supplied by the caller. -/
theorem integral_coefficientCutoffLaw_eq_integral_cutoffSampleLaw (M : ABKModel d)
    (m : ℤ) {g : RegCoeffField d → ℝ}
    (hg : AEStronglyMeasurable g (coefficientCutoffLaw M m)) :
    ∫ a : RegCoeffField d, g a ∂(coefficientCutoffLaw M m) =
      ∫ omega : CutoffSample d, g (coefficientCutoff M.nu m omega)
        ∂(cutoffSampleLaw M).toMeasure :=
  integral_map (measurable_coefficientCutoff M.nu m).aemeasurable hg

/-- The doubled quadratic form of the annealed cube matrix, read on the sample
carrier `CutoffSample d` that the closure junctions integrate over.
Unconditional. -/
theorem blockVecDot_annealedBlockMatrixAtScale_eq_integral_cutoffSampleLaw
    (M : ABKModel d) (m : ℤ) (K : ℤ) (X Y : BlockVec d) :
    blockVecDot X
        (blockMatVecMul
          (Ch04.annealedBlockMatrixAtScale (coefficientCutoffLaw M m) K) Y) =
      ∫ omega : CutoffSample d,
        blockVecDot X
          (blockMatVecMul
            (coarseBlockMatrix (cubeSet (originCube d K))
              (coefficientCutoff M.nu m omega).toFun) Y)
        ∂(cutoffSampleLaw M).toMeasure := by
  rw [Ch04.annealedBlockMatrixAtScale,
    blockVecDot_annealedBlockMatrix_eq_integral M m (originCube d K) X Y]
  exact integral_coefficientCutoffLaw_eq_integral_cutoffSampleLaw M m
    (integrable_blockVecDot_coarseBlockMatrix M m (originCube d K) X Y).aestronglyMeasurable

/-! ## The passage -/

/-- **The consumable one-sided form.**  The infinite-volume doubled quadratic
form is below the finite-volume expectation at *every* cube scale `K`.  This is
the form in which the passage is used by the closure junctions: a bound proved
at one finite grid transports to the annealed limit with no `limsup`.
Unconditional. -/
theorem blockVecDot_annealedLimitBlock_le_integral_coarseBlockMatrix_cutoffSampleLaw
    (M : ABKModel d) (m : ℤ) (K : ℤ) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (annealedLimitBlock (Annealed.sigmaBar M m)) X) ≤
      ∫ omega : CutoffSample d,
        blockVecDot X
          (blockMatVecMul
            (coarseBlockMatrix (cubeSet (originCube d K))
              (coefficientCutoff M.nu m omega).toFun) X)
        ∂(cutoffSampleLaw M).toMeasure := by
  rw [← blockVecDot_annealedBlockMatrixAtScale_eq_integral_cutoffSampleLaw M m K X X]
  exact blockVecDot_annealedLimitBlock_le_annealedBlockMatrixAtScale M m K X

/-! ## The same, at the `Ch02` carrier of the proved structural split

The proved split of Steps 1--3 states its left-hand side with
`Ch02.coarseBlockMatrix` on `Ch02.cubeDomain`, at the triadic coefficient
family of the cutoff, rather than with the annealed layer's cube-set coarse
matrix.  The two agree. -/

/-- The annealed layer's coarse cube matrix of the genuine cutoff coincides with
the Chapter 2 coarse matrix at the cutoff's triadic coefficient family --- the
carrier in which the proved structural split of Steps 1--3 is stated.
Unconditional. -/
theorem coarseBlockMatrix_cubeSet_coefficientCutoff_eq_ch02 (M : ABKModel d) (m : ℤ)
    (omega : CutoffSample d) (Q : TriadicCube d) :
    coarseBlockMatrix (cubeSet Q) (coefficientCutoff M.nu m omega).toFun =
      Ch02.coarseBlockMatrix (Ch02.cubeDomain Q)
        ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn Q) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  have haeeq : Ch02.CoeffOn.AEEq
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
          (coefficientCutoff M.nu m omega)
          (coefficientCutoff_aeLocallyUniformlyEllipticField M m omega)).coeffOn Q)
      ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn Q) :=
    Filter.EventuallyEq.rfl
  rw [Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_chapterCoarse
      (coefficientCutoff_aeLocallyUniformlyEllipticField M m omega) Q,
    Ch02.coarseBlockMatrix_eq_ofAEEq haeeq]

/-- **The consumable one-sided form at the split's carrier.**  The infinite-volume
doubled quadratic form is below the expectation of the Chapter 2 coarse doubled
form on `cu_K` at every cube scale `K`.  Unconditional. -/
theorem blockVecDot_annealedLimitBlock_le_integral_ch02CoarseBlockMatrix
    (M : ABKModel d) (m : ℤ) (K : ℤ) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (annealedLimitBlock (Annealed.sigmaBar M m)) X) ≤
      ∫ omega : CutoffSample d,
        blockVecDot X
          (blockMatVecMul
            (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d K))
              ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn
                (originCube d K))) X)
        ∂(cutoffSampleLaw M).toMeasure := by
  have hcarrier : ∀ omega : CutoffSample d,
      blockVecDot X
          (blockMatVecMul
            (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d K))
              ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn
                (originCube d K))) X) =
        blockVecDot X
          (blockMatVecMul
            (coarseBlockMatrix (cubeSet (originCube d K))
              (coefficientCutoff M.nu m omega).toFun) X) := by
    intro omega
    rw [coarseBlockMatrix_cubeSet_coefficientCutoff_eq_ch02 M m omega (originCube d K)]
  simp only [hcarrier]
  exact blockVecDot_annealedLimitBlock_le_integral_coarseBlockMatrix_cutoffSampleLaw
    M m K X

/-- The passage at the probe load `P` and at the split's carrier: the exact
expectation of the left-hand side of
`LocalizationRecurrenceMesh.exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded`
dominates the closure junction's annealed side.  Unconditional. -/
theorem blockVecDot_recurrenceP_annealedLimitBlock_le_integral_ch02CoarseBlockMatrix
    (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℤ) (e e' : Vec d) :
    blockVecDot (recurrenceP (Annealed.sigmaBar M n) e e')
        (blockMatVecMul (annealedLimitBlock (Annealed.sigmaBar M (n + (h : ℤ))))
          (recurrenceP (Annealed.sigmaBar M n) e e')) ≤
      ∫ omega : CutoffSample d,
        blockVecDot (recurrenceP (Annealed.sigmaBar M n) e e')
          (blockMatVecMul
            (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d K))
              ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn
                (originCube d K)))
            (recurrenceP (Annealed.sigmaBar M n) e e'))
        ∂(cutoffSampleLaw M).toMeasure :=
  blockVecDot_annealedLimitBlock_le_integral_ch02CoarseBlockMatrix M (n + (h : ℤ)) K
    (recurrenceP (Annealed.sigmaBar M n) e e')

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
