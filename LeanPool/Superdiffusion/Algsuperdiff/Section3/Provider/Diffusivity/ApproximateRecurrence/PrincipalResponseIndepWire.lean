/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchActualPerCube
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.Monotonicity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4Bounds

/-!
# PrincipalResponseIndepWire

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
NOTE: this module is an ordinary Provider helper / conditional A.  The binder
inventories below are informal descriptions only.

# The annealed carrier, identified at the actual cutoff carrier

Sources in ABK26:

* The sentence "Therefore, by independence of `bfA_{m-h}` and
  `G_{-(h)_{z+cu_n}} P_z` (the latter is a function of `k_m - k_{m-h}`),
  increasing `M` in `\eqref{e.cgamma.constraints}` if necessary,";
* `e.lower.bound.principal.one.pre` (label; display), whose right-hand side
  prints `avsum_{z in 3^n Zd cap cu_K} E[ G_{-(h)_{z+cu_n}} P_z.
  bfAhom_{m-h}(z+cu_n) G_{-(h)_{z+cu_n}} P_z ]`, i.e. the annealed matrix is
  read at the *mesoscale* cube `z + cu_n`.

## What this module supplies, and what it does not

Concretely, `ApproximateRecurrence.PrincipalResponseLegsIndep`
`integral_blockQuadratic_shellSplit_eq` consumes five inputs -- `hBmeas`,
`hWmeas`, `hB`, `hW`, `hBbar`.  Only `hBbar` is supplied *in this module*, and
it is supplied at the carriers the display actually uses.  The other four are
not open at the display's own matrix and load either; each has a named supplier
strictly downstream of this file:

* `hBmeas` -- `ApproximateRecurrence.PrincipalResponseLowerShellMeas`
  `exists_measurable_representative_switchCubeMatrix`;
* `hWmeas` -- `ApproximateRecurrence.PrincipalResponseLoadMeas`
  `measurable_shellIndexSigma_gaugedPrincipalLoadShell`;
* `hB` -- `ApproximateRecurrence.PrincipalResponseLoadMeas`
  `integrable_blockMatEntry_of_representative`;
* `hW` -- `ApproximateRecurrence.PrincipalResponseIndepAssembly`
  `exists_gamma0_integrable_toFullBlockVec_gaugedPrincipalLoadShell_mul`, under
  the parameter gates of `e.nablaw.in.L.eight`.

None of those four statements is available to, or used by, anything in this
module; they are recorded here so that this module's inventory is not read as a
claim about the repository.

`hBmeas` is no longer open at this matrix, and is no longer merely a binder
awaiting a witness: the direct successor of this module,
`ApproximateRecurrence.PrincipalResponseLowerShellMeas`, supplies it through
`exists_measurable_representative_switchCubeMatrix`, which produces a function
on `Cutoff.ShellSeq d` that is entrywise
`Cutoff.lowerShellLocalCompletion M lowScale U`-measurable and agrees with
`switchCubeMatrix` almost everywhere under `Cutoff.cutoffSampleLaw M`; the
direct consumer there,
`integral_blockQuadratic_shellSplit_eq_of_representative`, is the factorization
at an arbitrary such representative.  That is a statement of the successor
module, not of this one; nothing below changes.

The two carriers this module bridges are:

* `Book.Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n`
  integrates over `RegCoeffField d` against a *pushforward* of
  `Cutoff.cutoffSampleLaw M` along `Cutoff.coefficientCutoff M.nu L`;
* the display's own matrix is an integral over `Cutoff.CutoffSample d` against
  `(Cutoff.cutoffSampleLaw M).toMeasure`.

`blockMatEntry_annealedBlockMatrixAtScale_eq_integral_switchCubeMatrix`
composes the pushforward with real-translation stationarity to identify the
two.  No single proved lemma performs this bridge; the four steps used are

1. the two coarse block matrices agree pointwise in the sample -- CoarseGraining's
   `Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField`
   together with `Ch02.coarseBlockMatrix_eq_ofAEEq` and the proved
   `Cutoff.coefficientCutoff_canonicalFamily_aeeq`;
2. the pushforward, `Cutoff.coefficientCutoffLaw_eq_map` and
   `MeasureTheory.integral_map`, with the integrand's a.e.-strong measurability
   taken from the proved
   `Provider.Annealed.aestronglyMeasurable_blockMatEntry_coarseBlockMatrix_cubeSet`;
3. real-translation stationarity,
   `Provider.Annealed.integral_blockMatEntry_coarseBlockMatrix_cubeSet_eq_originCube_of_mem_descendantsAtScale`,
   which moves `z + cu_n` to `cu_n` at every integer scale, positive or negative;
4. the annealed entry as the origin-cube expectation, definitionally.

## The scale the bridge forces

Step 3 transfers a descendant of `cu_K` at scale `Q.scale - j` to the origin
cube at that same scale.  The bridge therefore holds at `n = (originCube d
K).scale - j` and at no other `n`: the annealed matrix of
`e.lower.bound.principal.one.pre` is the one at the manuscript's mesoscale, as
prints it.  Consumers that carry `n` as a free integer must instantiate it
there.

## What this module does NOT supply

It does **not** produce the independence replacement `hindep`, and it does not
re-state any consumer with `hindep` removed.  `hindep` remains a binder of
`ApproximateRecurrence.PrincipalResponseBudgetWire`
`exists_gamma0_descendantsAverage_integral_principalGoodEventEnergy_le_annealedCube_of_centeringConst`
and of its predecessors, untouched by anything below.  The four inputs that are
*not* supplied in this module are, precisely:

* `hBmeas`, the statement that `bfA_{m-h}` is measurable for the completed
  lower-shell field.  Nothing in *this* module concludes
  `Measurable[Cutoff.lowerShellLocalCompletion M L U] f` for any `f`; the only
  lemmas with that conclusion available at this point of the import order are
  the two generic a.e.-representative transfers of `Cutoff.Locality`.  Strictly
  downstream of this file,
  `ApproximateRecurrence.PrincipalResponseLowerShellMeas`
  `exists_measurable_representative_switchCubeMatrix` produces a function on
  `Cutoff.ShellSeq d` with that conclusion entrywise, agreeing with
  `switchCubeMatrix` almost everywhere under `Cutoff.cutoffSampleLaw M`, and
  its direct consumer
  `integral_blockQuadratic_shellSplit_eq_of_representative` carries the pair as
  binders.  Neither statement is available to, or used by, anything in this
  module.
* `hWmeas`, the parenthetical "the latter is a function of `k_m - k_{m-h}`", at
  the display's own load.  It is supplied strictly downstream of this file by
  `ApproximateRecurrence.PrincipalResponseLoadMeas`
  `measurable_shellIndexSigma_gaugedPrincipalLoadShell`, which is
  `Measurable[Cutoff.shellIndexSigma (Set.Ioc n m)]` for the gauged load
  `G_{-(h)_{z+cu_n}} P_z` under the geometric membership and the two
  weak-solution binders of `e.def.w`, with no measurability, continuity or
  selection property assumed of the corrector families.  Its component legs
  there -- the measurability of `freshShellCubeAverage`, of the two cube
  averages of `e.Pz.def`, and of `principalPz` itself -- exist but are
  `private` to that module, so only the composite gauged-load statement is
  available to consumers, and it is the only form in which this file's `hWmeas`
  can be discharged.
* `hB`, the entrywise integrability of the coarse matrix, supplied at any
  representative by `ApproximateRecurrence.PrincipalResponseLoadMeas`
  `integrable_blockMatEntry_of_representative`.
* `hW`, the second-moment integrability of the gauged load, supplied under the
  parameter gates of `e.nablaw.in.L.eight` by
  `ApproximateRecurrence.PrincipalResponseIndepAssembly`
  `exists_gamma0_integrable_toFullBlockVec_gaugedPrincipalLoadShell_mul`.

The mixed independence
`Cutoff.indep_lowerShellLocalCompletion_shellIndexSigma_Ioc` is still not
transported from `(Cutoff.ShellSeq d, M.P.toMeasure)` to `(Cutoff.CutoffSample
d, Cutoff.cutoffSampleLaw M)`, and no such transport is used downstream: the
factorization is performed at the shell carrier, and only the resulting
*integrals* are moved to the cutoff-sample carrier, along
`Cutoff.map_cutoffSampleLaw_val`.  The one proved independence transport,
`Cutoff.indep_cutoffSampleLocalSigma_of_indep_completion`, remains
completion-against-completion at a single index.

## Main results

* `coarseBlockMatrix_cubeSet_coefficientCutoff_eq`
* `switchCubeQuad_eq_blockVecDot_gaugedSwitchLoad`
* `integral_blockMatEntry_switchCubeMatrix_eq`
* `blockMatEntry_annealedBlockMatrixAtScale_eq_integral_switchCubeMatrix`

## References

* ABK26, (the sentence quoted above); `e.lower.bound.principal.one.pre` (label;
  display).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The two factors of `switchCubeQuad` -/

/-- Unconditional: `bfA_{m-h}(z + cu_n)` at the actual cutoff carrier, i.e. the
coarse block matrix that `PrincipalResponseSwitchActualPerCube.switchCubeQuad`
conjugates. -/
def switchCubeMatrix (M : ABKModel d) (lowScale : ℤ) (R : TriadicCube d)
    (omega : CutoffSample d) : BlockMat d :=
  Ch02.coarseBlockMatrix (Ch02.cubeDomain R)
    ((coefficientCutoffTriadicCoeffFamily M lowScale omega).coeffOn R)

/-- Unconditional: `G_{-(h)_{z+cu_n}} P_z`, the gauged load that
`PrincipalResponseSwitchActualPerCube.switchCubeQuad` tests the matrix against,
at the manuscript's own centering constant `freshShellCubeAverage`. -/
def gaugedSwitchLoad (R : TriadicCube d) (omega : CutoffSample d)
    (lowScale highScale : ℤ) (X : BlockVec d) : BlockVec d :=
  blockMatVecMul
    (blockGauge (-freshShellCubeAverage R omega.1 lowScale highScale)) X

/-- Unconditional: `switchCubeQuad` *is* the doubled quadratic form of
`switchCubeMatrix` at `gaugedSwitchLoad`.

It is a definitional unfolding and carries no hypothesis. -/
theorem switchCubeQuad_eq_blockVecDot_gaugedSwitchLoad (M : ABKModel d)
    (lowScale highScale : ℤ) (R : TriadicCube d) (X : BlockVec d)
    (omega : CutoffSample d) :
    switchCubeQuad M lowScale highScale R X omega =
      blockVecDot (gaugedSwitchLoad R omega lowScale highScale X)
        (blockMatVecMul (switchCubeMatrix M lowScale R omega)
          (gaugedSwitchLoad R omega lowScale highScale X)) :=
  rfl

/-! ## The two coarse block matrices -/

/-- Unconditional: on every genuine cutoff sample the ambient coarse block
matrix of the cutoff field on `cubeSet R` is the Chapter 2 coarse block matrix
of the cutoff coefficient family on `cubeDomain R`.

This is CoarseGraining's `Ch04` identification transported across the
a.e.-equality of the canonical Chapter 2 family with the literal cutoff family. -/
theorem coarseBlockMatrix_cubeSet_coefficientCutoff_eq [NeZero d] (M : ABKModel d)
    (lowScale : ℤ) (omega : CutoffSample d) (R : TriadicCube d) :
    HCPolySupport.coarseBlockMatrix (cubeSet R)
        (coefficientCutoff M.nu lowScale omega).toFun =
      switchCubeMatrix M lowScale R omega := by
  rw [switchCubeMatrix,
    Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_chapterCoarse
      (coefficientCutoff_aelocallyUniformlyElliptic M lowScale omega) R]
  exact Ch02.coarseBlockMatrix_eq_ofAEEq
    (coefficientCutoff_canonicalFamily_aeeq M lowScale omega R)

/-! ## The pushforward -/

/-- Unconditional: the cutoff-sample expectation of a coarse block entry is the
`RegCoeffField` expectation against the actual coefficient-cutoff law.

This is the pushforward half of the carrier bridge: `coefficientCutoffLaw M L`
is by definition the image of `cutoffSampleLaw M` under
`coefficientCutoff M.nu L`. -/
theorem integral_blockMatEntry_switchCubeMatrix_eq [NeZero d] (M : ABKModel d)
    (lowScale : ℤ) (R : TriadicCube d) (alpha beta : BlockCoord d) :
    (∫ omega : CutoffSample d,
        blockMatEntry (switchCubeMatrix M lowScale R omega) alpha beta
        ∂(cutoffSampleLaw M).toMeasure) =
      ∫ a, blockMatEntry
        (HCPolySupport.coarseBlockMatrix (cubeSet R) a.toFun) alpha beta
        ∂(coefficientCutoffLaw M lowScale) := by
  simp only [← coarseBlockMatrix_cubeSet_coefficientCutoff_eq M lowScale _ R]
  rw [coefficientCutoffLaw_eq_map M lowScale,
    MeasureTheory.integral_map (measurable_coefficientCutoff M.nu lowScale).aemeasurable
      (by
        rw [← coefficientCutoffLaw_eq_map M lowScale]
        exact Provider.Annealed.aestronglyMeasurable_blockMatEntry_coarseBlockMatrix_cubeSet
          (coefficientCutoffLaw_lawCarrier M lowScale) R alpha beta)]

/-! ## The bridge -/

/-- **The annealed carrier, at the actual carriers.**

For every cube `R` of the depth-`j` grid below `cu_K`, every entry of the
annealed matrix `bfAhom_{m-h}` read at the mesoscale `(originCube d K).scale - j`
is the expectation, on the genuine cutoff-sample carrier, of the corresponding
entry of the very matrix `switchCubeQuad` conjugates.

This is the `hBbar` input of
`ApproximateRecurrence.PrincipalResponseLegsIndep`
`integral_blockQuadratic_shellSplit_eq`, restated at
`(Cutoff.CutoffSample d, Cutoff.cutoffSampleLaw M)` instead of at
`(Cutoff.ShellSeq d, M.P.toMeasure)`.

The scale is forced: real-translation stationarity moves a descendant of `cu_K`
to the origin cube at the *same* scale, so the identity holds at `n =
(originCube d K).scale - j`, which is the scale
`e.lower.bound.principal.one.pre` (label) prints.

: this statement holds only under the propositions supplied by its binders --
here just the geometric membership `hR`.  It is a provider A, not a
source-facing frozen declaration.  It does not produce the independence
replacement `hindep`, which remains a binder of every consumer that carries it;
see the module docstring for the four inputs's factorization that are *not*
supplied here. -/
theorem blockMatEntry_annealedBlockMatrixAtScale_eq_integral_switchCubeMatrix
    [NeZero d] (M : ABKModel d) (lowScale : ℤ) {K : ℤ} {j : ℕ}
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d K) j)
    (alpha beta : BlockCoord d) :
    blockMatEntry
        (Ch04.annealedBlockMatrixAtScale (coefficientCutoffLaw M lowScale)
          (((originCube d K).scale : ℤ) - (j : ℤ))) alpha beta =
      ∫ omega : CutoffSample d,
        blockMatEntry (switchCubeMatrix M lowScale R omega) alpha beta
        ∂(cutoffSampleLaw M).toMeasure := by
  have hnk : ((originCube d K).scale : ℤ) - (j : ℤ) ≤ ((originCube d K).scale : ℤ) := by
    omega
  have hRscale : R ∈ descendantsAtScale (originCube d K)
      (((originCube d K).scale : ℤ) - (j : ℤ)) := by
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d K) hnk]
    have hj : (((originCube d K).scale : ℤ) -
        (((originCube d K).scale : ℤ) - (j : ℤ))).toNat = j := by omega
    rwa [hj]
  rw [integral_blockMatEntry_switchCubeMatrix_eq M lowScale R alpha beta]
  calc
    blockMatEntry
        (Ch04.annealedBlockMatrixAtScale (coefficientCutoffLaw M lowScale)
          (((originCube d K).scale : ℤ) - (j : ℤ))) alpha beta
      = ∫ a, blockMatEntry
          (HCPolySupport.coarseBlockMatrix
            (cubeSet (originCube d (((originCube d K).scale : ℤ) - (j : ℤ))))
            a.toFun) alpha beta
          ∂(coefficientCutoffLaw M lowScale) := by
        cases alpha <;> cases beta <;> rfl
    _ = ∫ a, blockMatEntry
          (HCPolySupport.coarseBlockMatrix (cubeSet R) a.toFun) alpha beta
          ∂(coefficientCutoffLaw M lowScale) :=
        (Provider.Annealed.integral_blockMatEntry_coarseBlockMatrix_cubeSet_eq_originCube_of_mem_descendantsAtScale
          (coefficientCutoffLaw_lawCarrier M lowScale)
          (Provider.Annealed.coefficientCutoffLaw_isStationaryRealR M lowScale)
          hnk hRscale alpha beta).symm

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
