/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.TranslationCovariance
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.Lambda.Characterization
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.Dilation
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Public

/-!
# LambdaCovariance

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Translation and dilation covariance of the multiscale lower ellipticity

The frozen Section 2.4 sensitivity gates are stated at the *unit cube*, against
`Algsuperdiff.Frozen.Section24.unitCubeLambda s q a` with
`a : CoeffOn (cubeDomain (originCube d 0))`; ABK26's good local event
`e.good.local.events` is stated at the off-centre cube
`z + square_m`, against `lambda_{s,q}(z + square_m; a_n)`.  This module supplies
the identification between the two,

```
lambda_{s,q}(z + square_m; a_n(omega))
   =  unitCubeLambda s q ( a_n(omega) rescaled by y |-> z + 3^m y ) ,
```

i.e. the *scale-and-translation covariance* of the multiscale lower ellipticity
for the actual coefficient cutoff.

## Proof route

Nothing analytic is reproved; the identity is the composition of a translation
and a dilation, each of which is an existing CoarseGraining interface.

* **Translation.**  CoarseGraining's
  `Ch02.lambdaSq_translateCube_of_coarseSigmaStarInvMatrixNorm` reduces the
  whole descendant tree of `z + square_m` to the *one-cube* covariance of
  `Ch02.coarseSigmaStarInvMatrixNorm`.  That one-cube covariance is obtained
  exactly as in `TranslationCovariance.lean`: the proved CoarseGraining bridge
`coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField`
  rewrites the Chapter 2 coarse block matrix as the raw `coarseBlockMatrix
  (cubeSet Q) a`, CoarseGraining's
  `coarseBlockMatrix_translateSet_eq_translateCoeffField` is its covariance
  under a real translation of the domain, and
  `Cutoff.coefficientCutoff_translateCutoffSample` moves the translation from
  the coefficient field to the sample.  The triadic geometry is the proved
  `cubeSet_translateCube_descendantTranslationShift`.
* **Dilation.**  CoarseGraining's `Ch02.TriadicCoeffFamily.dilate` and
  `Ch02.TriadicCoeffFamily.isDilation_dilate` give, through
  `Ch02.lambdaSq_dilate`, the scale normalization `lambda_{s,q}(square_0;
  dilate (-m) F) = lambda_{s,q}(square_m; F)`, since `dilateCube (-m)
  (originCube d m) = originCube d 0`.
* **Unit cube.**  The frozen `unitCubeLambda` is characterized by
  `Algsuperdiff.Section24.UnitCubeMultiscale.Lambda.characterization`; the
  witness family is the dilated family itself, so the side condition is
  reflexivity.

## The rescaled coefficient object

`unitRescaledCutoffCoeff M Q n omega` is the coefficient object on the unit cube
obtained from `a_n` by the manuscript's rescaling `y |-> z + 3^m y`, represented by
`dilate (-m)` applied to the family of the sample translated by
`z = triadicCubeShift Q`.  Its coefficient field is described almost everywhere
by `unitRescaledCutoffCoeff_toCoeffField_ae_eq`:

```
(unitRescaledCutoffCoeff M Q n omega).toCoeffField y  =  a_n(omega)(3^m y + z)
```

for almost every `y` in the open unit cube.

## Main results

* `coarseSigmaStarInvMatrixNorm_cutoff_translateCutoffSample`: the one-cube
  covariance.
* `lambdaSq_cutoff_translateCutoffSample`: the multiscale translation
  covariance.
* `lambdaSq_originCube_dilate`: the scale normalization.
* `unitCubeLambda_unitRescaledCutoffCoeff`: the full identification.
* `unitRescaledCutoffCoeff_toCoeffField_ae_eq`: the pointwise a.e. description
  of the rescaled coefficient field.

## References

* ABK26 (the definitions (2.22)--(2.23) and the sentence extending them to
  translates `y + square_m`).
* ABK26, `e.good.local.events`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## One-cube translation covariance of `|sigma_*^{-1}|` -/

/-- One-cube translation covariance of the coarse block matrix for the actual
coefficient cutoff: if the half-open realization of `T` is the translate by `v`
of that of `R`, then the Chapter 2 coarse block matrix of the cutoff at `T`
equals the one at `R` for the translated sample. -/
theorem coarseBlockMatrix_cutoff_translateCutoffSample [NeZero d] (M : ABKModel d)
    (m : ℤ) (v : Vec d) {R T : TriadicCube d}
    (hset : cubeSet T = translateSet v (cubeSet R)) (omega : CutoffSample d) :
    Ch02.coarseBlockMatrix (Ch02.cubeDomain T)
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
            (coefficientCutoff M.nu m omega)
            (coefficientCutoff_aeLocallyUniformlyEllipticField M m omega)).coeffOn
          T) =
      Ch02.coarseBlockMatrix (Ch02.cubeDomain R)
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
            (coefficientCutoff M.nu m (translateCutoffSample v omega))
            (coefficientCutoff_aeLocallyUniformlyEllipticField M m
              (translateCutoffSample v omega))).coeffOn R) := by
  rw [←
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_chapterCoarse
      (coefficientCutoff_aeLocallyUniformlyEllipticField M m omega) T,
    ←
      Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_chapterCoarse
      (coefficientCutoff_aeLocallyUniformlyEllipticField M m
        (translateCutoffSample v omega)) R,
    hset, coarseBlockMatrix_translateSet_eq_translateCoeffField,
    coefficientCutoff_translateCutoffSample]
  rfl

/-- One-cube translation covariance of `|sigma_*^{-1}(Q; a)|` for the actual
coefficient cutoff. -/
theorem coarseSigmaStarInvMatrixNorm_cutoff_translateCutoffSample [NeZero d]
    (M : ABKModel d) (m : ℤ) (v : Vec d) {R T : TriadicCube d}
    (hset : cubeSet T = translateSet v (cubeSet R)) (omega : CutoffSample d) :
    Ch02.coarseSigmaStarInvMatrixNorm T
        (coefficientCutoffTriadicCoeffFamily M m omega) =
      Ch02.coarseSigmaStarInvMatrixNorm R
        (coefficientCutoffTriadicCoeffFamily M m
          (translateCutoffSample v omega)) := by
  have hleft : Ch02.TriadicCoeffFamily.AEEq
      (coefficientCutoffTriadicCoeffFamily M m omega)
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (coefficientCutoff M.nu m omega)
        (coefficientCutoff_aeLocallyUniformlyEllipticField M m omega)) :=
    fun _ => Filter.EventuallyEq.rfl
  have hright : Ch02.TriadicCoeffFamily.AEEq
      (coefficientCutoffTriadicCoeffFamily M m (translateCutoffSample v omega))
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (coefficientCutoff M.nu m (translateCutoffSample v omega))
        (coefficientCutoff_aeLocallyUniformlyEllipticField M m
          (translateCutoffSample v omega))) :=
    fun _ => Filter.EventuallyEq.rfl
  rw [Ch02.coarseSigmaStarInvMatrixNorm_eq_ofAEEq hleft T,
    Ch02.coarseSigmaStarInvMatrixNorm_eq_ofAEEq hright R]
  have hmat := coarseBlockMatrix_cutoff_translateCutoffSample M m v hset omega
  have hlower := congrArg (fun A : BlockMat d => Ch02.matrixNorm A.lowerRight) hmat
  simpa [Ch02.coarseSigmaStarInvMatrixNorm] using hlower

/-! ## Translation covariance of the multiscale lower ellipticity -/

/-- **Deterministic translation covariance of `lambda_{s,q}`.**  For the actual
coefficient cutoff, the multiscale lower ellipticity on an arbitrary triadic
cube `Q` equals the one on the centered cube of the same scale, evaluated at the
sample translated by the base point `triadicCubeShift Q` of `Q`. -/
theorem lambdaSq_cutoff_translateCutoffSample [NeZero d] (M : ABKModel d)
    (m : ℤ) (Q : TriadicCube d) (s : ℝ) (q : Ch02.MultiscaleExponent)
    (omega : CutoffSample d) :
    Ch02.lambdaSq Q s q (coefficientCutoffTriadicCoeffFamily M m omega) =
      Ch02.lambdaSq (originCube d Q.scale) s q
        (coefficientCutoffTriadicCoeffFamily M m
          (translateCutoffSample (triadicCubeShift Q) omega)) := by
  have hQ : translateCube Q.index (originCube d Q.scale) = Q := by
    cases Q with
    | mk scale index => simp [translateCube, originCube]
  have hrw : Ch02.lambdaSq Q s q (coefficientCutoffTriadicCoeffFamily M m omega) =
      Ch02.lambdaSq (translateCube Q.index (originCube d Q.scale)) s q
        (coefficientCutoffTriadicCoeffFamily M m omega) := by
    rw [hQ]
  rw [hrw]
  refine Ch02.lambdaSq_translateCube_of_coarseSigmaStarInvMatrixNorm _ _ Q.index
    (originCube d Q.scale) s q ?_
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
  refine coarseSigmaStarInvMatrixNorm_cutoff_translateCutoffSample M m
    (triadicCubeShift Q) ?_ omega
  rw [cubeSet_translateCube_descendantTranslationShift Q.index l hscale]
  rfl

/-! ## Dilation to the unit cube -/

/-- `dilateCube (-m)` normalizes the centered scale-`m` cube to the unit cube. -/
theorem dilateCube_neg_originCube (m : ℤ) :
    Ch02.dilateCube (-m) (originCube d m) = originCube d 0 := by
  simp [Ch02.dilateCube, originCube]

/-- **Scale normalization of `lambda_{s,q}`.**  The multiscale lower ellipticity
of a family on the centered scale-`m` cube is that of its `3^{-m}`-dilation on
the unit cube. -/
theorem lambdaSq_originCube_dilate (F : Ch02.TriadicCoeffFamily d) (m : ℤ)
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    Ch02.lambdaSq (originCube d 0) s q (Ch02.TriadicCoeffFamily.dilate (-m) F) =
      Ch02.lambdaSq (originCube d m) s q F := by
  have h := Ch02.lambdaSq_dilate
    (Ch02.TriadicCoeffFamily.isDilation_dilate (-m) F) (originCube d m) s q
  rwa [dilateCube_neg_originCube m] at h

/-! ## The rescaled unit-cube coefficient object -/

/-- The coefficient cutoff `a_n`, rescaled from the cube `Q = z + square_m` to
the unit cube by the manuscript's map `y |-> z + 3^m y`, as a Section 2.4
unit-cube coefficient object. -/
def unitRescaledCutoffCoeff (M : ABKModel d) (Q : TriadicCube d)
    (cutoffScale : ℤ) (omega : CutoffSample d) :
    Ch02.CoeffOn (Ch02.cubeDomain (originCube d 0)) :=
  (Ch02.TriadicCoeffFamily.dilate (-Q.scale)
    (coefficientCutoffTriadicCoeffFamily M cutoffScale
      (translateCutoffSample (triadicCubeShift Q) omega))).coeffOn
    (originCube d 0)

/-- **The lambda-transfer identity.**  The multiscale lower ellipticity of the
cutoff `a_n` on the cube `Q = z + square_m` is the frozen unit-cube gauge
`unitCubeLambda` of the rescaled coefficient object. -/
theorem unitCubeLambda_unitRescaledCutoffCoeff [NeZero d] (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ)
    (q : Ch02.MultiscaleExponent) (omega : CutoffSample d) :
    Algsuperdiff.Frozen.Section24.unitCubeLambda s q
        (unitRescaledCutoffCoeff M Q cutoffScale omega) =
      Ch02.lambdaSq Q s q
        (coefficientCutoffTriadicCoeffFamily M cutoffScale omega) := by
  rw [unitRescaledCutoffCoeff,
    Algsuperdiff.Section24.UnitCubeMultiscale.Lambda.characterization s q _ _
      (Ch02.CoeffOn.AEEq.refl _),
    lambdaSq_originCube_dilate]
  exact (lambdaSq_cutoff_translateCutoffSample M cutoffScale Q s q omega).symm

/-! ## The rescaled coefficient field -/

/-- The coefficient field of the rescaled unit-cube object is, almost everywhere
on the open unit cube, the manuscript's rescaling `y |-> a_n(z + 3^m y)` of the
literal cutoff field. -/
theorem unitRescaledCutoffCoeff_toCoeffField_ae_eq (M : ABKModel d)
    (Q : TriadicCube d) (cutoffScale : ℤ) (omega : CutoffSample d) :
    (unitRescaledCutoffCoeff M Q cutoffScale omega).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (originCube d 0))]
      fun y : Vec d =>
        coefficientCutoff M.nu cutoffScale omega
          (((3 : ℝ) ^ Q.scale) • y + triadicCubeShift Q) := by
  have hdil :=
    (Ch02.TriadicCoeffFamily.isDilation_dilate (-Q.scale)
        (coefficientCutoffTriadicCoeffFamily M cutoffScale
          (translateCutoffSample (triadicCubeShift Q) omega))
        (originCube d Q.scale)).coeff_ae_eq
  rw [dilateCube_neg_originCube Q.scale] at hdil
  refine Filter.EventuallyEq.trans hdil ?_
  filter_upwards with y
  have hvec : Ch02.undilateVec (-Q.scale) y = ((3 : ℝ) ^ Q.scale) • y := by
    simp [Ch02.undilateVec, Ch02.triadicDilationFactor]
  have hcut := congrArg (fun a : RegCoeffField d => a (((3 : ℝ) ^ Q.scale) • y))
    (coefficientCutoff_translateCutoffSample M.nu cutoffScale (triadicCubeShift Q)
      omega)
  simpa [Ch02.dilateCoeffField, hvec, coefficientCutoffTriadicCoeffFamily]
    using hcut

end

end Algsuperdiff.Section3.Provider.BadEvents
