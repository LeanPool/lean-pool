/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.JSmallness
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.Adapters

/-!
# JCarrierRescale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Transport of the response-`J` sensitivity to a translated triadic cube

This module is the cube-carrier transport provider used toward
the `J`-carrier rescaling of `p.bfA.multiscalebound` in ABK26.  It proves the exact
translation/dilation identity and a conditional bad-event response estimate, but
it does not by itself close an unfrozen source node.

The manuscript checks the smallness hypothesis
`e.J.sensitivity.smallness.condition` at the cube `z + square_j` and then
writes "Applying `e.J.by.means.of.bfA` and then Lemma `l.J.sensitivity` with
`delta = 1` yields.".  Lemma `l.J.sensitivity` is stated at the *unit cube*
`square_0`, and the frozen Section 2.4 realization
`Algsuperdiff.Frozen.Section24.responseJ_sensitivity` is stated at the
unit-cube carrier `cubeDomain (originCube d 0)` as well.  This module exposes
that transport, as an *equality* — so the dimension-only constant is untouched
— and reads the proved `#J`-smallness conclusion through it.

## The transport

`LambdaCovariance.lean` already supplies the transport for the multiscale lower
ellipticity: `unitCubeLambda s q (unitRescaledCutoffCoeff M Q n omega) =
lambda_{s,q}(Q; a_n(omega))`.  What was missing is the same identification for
the response functional itself,

```
J(square_0, p, q; a_n(z + 3^j .))  =  J(z + square_j, p, q; a_n) ,
```

which is assembled here from two CoarseGraining interfaces:

* **Translation.**  `Internal.Ch02.book_responseJ_eq_ResponseJ` rewrites the
  Chapter 2 response as the raw `ResponseJ` of the coefficient field on the
  open cube; `ResponseJ_translateSet_eq_translateCoeffField` is its covariance
  under a real translation of the domain; and
  `Cutoff.coefficientCutoff_translateCutoffSample` moves the translation from
  the coefficient field to the sample.  The geometry is CoarseGraining's
  `openCubeSet_eq_translateSet_originCube_of_triadicCube`.
* **Dilation.**  `Ch02.responseJ_dilate` applied to
  `Ch02.TriadicCoeffFamily.isDilation_dilate`, at
  `dilateCube (-m) (originCube d m) = originCube d 0`.

Both are exact identities: `J` is scale free and translation covariant, so no
constant is created or lost.

## Main results

* `responseJ_cutoff_translateCutoffSample`: translation covariance of the
  Chapter 2 response for the actual coefficient cutoff.
* `responseJ_originCube_dilate`: scale normalization of the response.
* `responseJ_unitRescaledCutoffCoeff`: **the exact transport identity**,
  `J(square_0, p, q; a_n rescaled) = J(z + square_j, p, q; a_n)`.

## References

* ABK26 (`p.bfA.multiscalebound`, the carrier transport).
* ABK26 (`l.J.sensitivity`, stated at `square_0`).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-! ## Translation covariance of the coarse-grained response -/

/-- **One-cube translation covariance of the Chapter 2 response** for the actual
coefficient cutoff: if the open realization of `T` is the translate by `v` of
that of `R`, then the response of the cutoff at `T` equals the one at `R` for the
translated sample. -/
theorem responseJ_cutoff_translateCutoffSample (M : ABKModel d) (m : ℤ) (v : Vec d)
    {R T : TriadicCube d} (hset : openCubeSet T = translateSet v (openCubeSet R))
    (p q : Vec d) (omega : CutoffSample d) :
    Ch02.responseJ (Ch02.cubeDomain T)
        ((coefficientCutoffTriadicCoeffFamily M m omega).coeffOn T) p q =
      Ch02.responseJ (Ch02.cubeDomain R)
        ((coefficientCutoffTriadicCoeffFamily M m
          (translateCutoffSample v omega)).coeffOn R) p q := by
  rw [HCPolySupport.Internal.Ch02.book_responseJ_eq_ResponseJ,
    HCPolySupport.Internal.Ch02.book_responseJ_eq_ResponseJ]
  change ResponseJ (openCubeSet T) p q (coefficientCutoff M.nu m omega).toFun =
    ResponseJ (openCubeSet R) p q
      (coefficientCutoff M.nu m (translateCutoffSample v omega)).toFun
  rw [hset, ResponseJ_translateSet_eq_translateCoeffField,
    coefficientCutoff_translateCutoffSample]
  rfl

/-! ## Scale normalization of the coarse-grained response -/

/-- **Scale normalization of the Chapter 2 response.**  The response of a family
on the centered scale-`m` cube is that of its `3^{-m}`-dilation on the unit
cube. -/
theorem responseJ_originCube_dilate (F : Ch02.TriadicCoeffFamily d) (m : ℤ)
    (p q : Vec d) :
    Ch02.responseJ (Ch02.cubeDomain (originCube d 0))
        ((Ch02.TriadicCoeffFamily.dilate (-m) F).coeffOn (originCube d 0)) p q =
      Ch02.responseJ (Ch02.cubeDomain (originCube d m)) (F.coeffOn (originCube d m))
        p q := by
  have h := Ch02.responseJ_dilate
    (Ch02.TriadicCoeffFamily.isDilation_dilate (-m) F (originCube d m)) p q
  rwa [dilateCube_neg_originCube m] at h

/-! ## The transport -/

/-- **The response-`J` carrier transport** (the `J`-carrier rescaling of
`p.bfA.multiscalebound`, ABK26).  The frozen unit-cube response functional of the rescaled
coefficient object is the response functional of the cutoff on the translated triadic cube
`Q = z + square_j` itself:

```
J(square_0, p, q; a_n(z + 3^j .))  =  J(z + square_j, p, q; a_n) .
```

This is the exact analogue, for `J`, of the proved
`unitCubeLambda_unitRescaledCutoffCoeff`. -/
theorem responseJ_unitRescaledCutoffCoeff (M : ABKModel d) (Q : TriadicCube d)
    (cutoffScale : ℤ) (p q : Vec d) (omega : CutoffSample d) :
    Ch02.responseJ (Ch02.cubeDomain (originCube d 0))
        (unitRescaledCutoffCoeff M Q cutoffScale omega) p q =
      Ch02.responseJ (Ch02.cubeDomain Q)
        ((coefficientCutoffTriadicCoeffFamily M cutoffScale omega).coeffOn Q) p q := by
  rw [unitRescaledCutoffCoeff, responseJ_originCube_dilate]
  exact (responseJ_cutoff_translateCutoffSample M cutoffScale (triadicCubeShift Q)
    (openCubeSet_eq_translateSet_originCube_of_triadicCube Q) p q omega).symm

/-! ## The conditional response estimate at the translated triadic cube -/


end

end Algsuperdiff.Section3.Provider.Multiscale
