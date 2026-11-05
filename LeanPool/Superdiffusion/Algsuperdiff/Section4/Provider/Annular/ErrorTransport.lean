/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaCovariance
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.Translate
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Events

/-!
# ErrorTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `(2,2)` error transport

ABK26, Section 4.1 reads the homogenization-error functional `𝓔_{s,p,q}` on
the **translated** cube `z + □_n`, and then feeds it to the Section 2.4
sensitivity machinery, which is stated only on the **unit** cube.  The bridge
between the two is the manuscript's unremarked change of variables `y ↦ z +
3^n y`.

`Section3.Provider.BadEvents.unitRescaledCutoffCoeff` performs exactly that
change of variables on the coefficient cutoff: the sample is translated by the
base point `z = triadicCubeShift Q` of the cube, and the resulting triadic
family is dilated by `3^{-Q.scale}` onto the unit cube.  It is the object at
which the frozen Section 2.4 lower-ellipticity gate is already read
(`unitCubeLambda_unitRescaledCutoffCoeff`).  This module supplies the same
identification for the **error** functional.

## What is proved

* `unitCubeHomogenizationError_dilatedFamily` — the reusable core: for *any*
  triadic coefficient family `F`, *any* exponent pair and *any* comparator
  matrix, the frozen unit-cube error of the root of `dilate (-m) F` is the
  literal manuscript error on `□_m` of `F` itself.  This is the statement a
  flux-corrected rescaling layer will consume verbatim once a flux-corrected
  triadic family exists; nothing in it mentions the cutoff.
* `unitCubeHomogenizationError_unitRescaledCutoffCoeff` — its instance at the
  proved rescaling layer, i.e. the transport at the plain cutoff family
  `Cutoff.coefficientCutoffTriadicCoeffFamily`.
* `unitCubeHomogenizationError_unitRescaledCutoffCoeff_eq_cutoffRaw22` — the
  literal-observable leg at `(2,2)`.
* `unitCubeHomogenizationError22_unitRescaledCutoffCoeff_eq_annularErrorAtom` —
  the `𝒢₂` normalization (cutoff level `n − 2`, comparator `σ_{n−2} Id`) at a
  lattice cube `⟨n, v⟩`: the unit-cube error at the rescaled coefficient object
  is literally `Support.annularErrorAtom M n t` evaluated at the sample
  translated by `Support.triadicLatticePoint n v`.  This is the
  translated-sample rendering used throughout.

## Exact, not almost-everywhere

Every identity above is an **exact pointwise equality of reals**: no null set,
no representative choice, no normalization constant.  The reason is structural.
The frozen characterization
`Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError_characterization` is
quantified over *every* compatible family; at the root of a dilated family the
compatible family is that dilated family itself, so its a.e. side condition is
discharged by `CoeffOn.A.refl`.  CoarseGraining's
`Book.Ch02.HomogenizationErrorOnCube_dilate` is an equality with factor `1`,
and the `(2,2)` characterization of `Support.cutoffHomogenizationErrorRaw22`
proves on the very same `HomogenizationErrorOnCube` expression, so the two ends
meet with no residual scaling.

The single a.e. statement in this file is
`unitCubeHomogenizationError22_unitRescaledCutoffCoeff_ae_eq_annularErrorObservable`,
and its null set comes from elsewhere: it is the composition of the exact
identity with `Support.annularErrorAtom_ae_eq_annularErrorObservable`, where a
*measurable modification* is selected, as everywhere in the `𝒢₂` lane.
Transporting that a.e. identity along the translation is legitimate because
every real translation preserves the cutoff-sample law
(`GoodEvents.measurePreserving_translateCutoffSample`).

## Route

```
unitCubeHomogenizationError t p q (unitRescaledCutoffCoeff M Q L ω) a₀
   = 𝓔(□₀; dilate (−Q.scale) (a_L at ω translated by z), a₀)     [frozen char.]
   = 𝓔(□_{Q.scale}; a_L at ω translated by z, a₀)  [CoarseGraining ..._dilate]
   = annularErrorAtom M Q.scale t (translate z ω)  [(2,2) char., backwards]
```

## What the manuscript says, and does not say

`d.mathcal.E` extends the error functional to translated cubes in exactly one
sentence -- *"We extend these definitions to translations `y + □_m` of `□_m` in
the obvious way"* -- and says nothing at all about the behaviour of `𝓔` under a
dilation.  The only explicit rescale-and-translate passage in the manuscript (
inside the proof of `l.lambda.sensitivity`) is written for `λ_{s,q}`, not for
`𝓔`.

The rescaling this module supplies is therefore the step ABK26 performs
*silently*.  What is proved here is the *error* half of that step, and it is
proved as an exact equality, so no constant and no inequality direction is
introduced.

* -- the "obvious way" extension is a theorem, and is a.e.-tolerant.  The
  rendering used here is the proved Support convention (translate the *sample*,
  never the cube), so no off-grid cube object is
  introduced and the a.e. tolerance is not consumed.
* -- the `q = ∞` branches should sum to `l ≤ n`, not `l ≤ m`.  Invisible here:
  every statement in this module is at `n = m` (`HomogenizationErrorOnCube`
  fixes `n := Q.scale`).
* Every comparator below is `isotropicComparatorMatrix σ` with `σ` a
  `PositiveScalar`, which is that locus (and is `scalarMatrix (σ : ℝ)` on the
  nose).
* -- all concern constants, exponents, annulus multiplicity or the truncation
  level *inside* the estimates, not the definition of the functional or its
  behaviour under the change of variables.  None bears on an equality of two
  readings of the same functional.

## References

* ABK26, `d.mathcal.E`, (2.28), (the translation sentence);
  `d.good.event.for.lambda`'s `𝒢₂` clause; `e.ugly.estimate.for.J.pre`;
  `e.ugly.estimate.for.J`.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-! ## The base point of a triadic cube, at a lattice index -/

/-- The translation vector carrying `□_k` onto the cube `⟨k, v⟩` is the
Section 4 lattice point `3^k v`.  This is the index-level spelling of
`Homogenization.triadicCubeShift`, and it is what lets the transport below be
read at the lattice enumerations of `Support.latticeAnnulusSet`. -/
theorem triadicCubeShift_mk (k : ℤ) (v : Fin d → ℤ) :
    triadicCubeShift (⟨k, v⟩ : TriadicCube d) = Support.triadicLatticePoint k v := by
  funext i
  simp only [triadicCubeShift, cubeScaleFactor, Support.triadicLatticePoint]
  ring

/-! ## The reusable dilation glue -/

/-- **The scale normalization of the homogenization error.**  For an arbitrary
triadic coefficient family `F`, the frozen unit-cube error functional read at
the root restriction of the `3^{-m}`-dilated family is exactly the literal
manuscript error `𝓔_{s,p,q}(□_m; F, a₀)`.

Nothing here is specific to the coefficient cutoff, to the exponents, or to an
isotropic comparator; this is the statement any *other* rescaling layer (for
instance a flux-corrected one) consumes unchanged, once it exhibits its
coefficient object as the root of a dilated triadic family. -/
theorem unitCubeHomogenizationError_dilatedFamily
    (F : TriadicCoeffFamily d) (m : ℤ) (s : ℝ) (p q : Ch02.MultiscaleExponent)
    (a0 : Mat d) :
    Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError s p q
        ((TriadicCoeffFamily.dilate (-m) F).coeffOn (originCube d 0)) a0 =
      HomogenizationErrorOnCube (originCube d m) s p q F a0 := by
  rw [Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError_characterization
    s p q _ a0 _ (CoeffOn.AEEq.refl _)]
  have hdil := HomogenizationErrorOnCube_dilate
    (TriadicCoeffFamily.isDilation_dilate (-m) F) (originCube d m) s p q a0
  rw [dilateCube_neg_originCube] at hdil
  exact hdil

/-! ## The transport at the proved rescaling layer -/

/-- **The error transport.**  The frozen unit-cube homogenization error, read
at the rescaled coefficient object `unitRescaledCutoffCoeff M Q L ω`, is the
literal manuscript error functional on the *centered* cube of the same scale as
`Q`, evaluated at the sample translated by the base point of `Q`.

This holds at every exponent pair, every comparator matrix, every cube and
every cutoff level; the `𝒢₂` atom below is one instance. -/
theorem unitCubeHomogenizationError_unitRescaledCutoffCoeff
    (M : ABKModel d) (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ)
    (p q : Ch02.MultiscaleExponent) (a0 : Mat d) (omega : Cutoff.CutoffSample d) :
    Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError s p q
        (unitRescaledCutoffCoeff M Q cutoffScale omega) a0 =
      HomogenizationErrorOnCube (originCube d Q.scale) s p q
        (Cutoff.coefficientCutoffTriadicCoeffFamily M cutoffScale
          (Cutoff.translateCutoffSample (triadicCubeShift Q) omega)) a0 := by
  rw [unitRescaledCutoffCoeff]
  exact unitCubeHomogenizationError_dilatedFamily
    (Cutoff.coefficientCutoffTriadicCoeffFamily M cutoffScale
      (Cutoff.translateCutoffSample (triadicCubeShift Q) omega))
    Q.scale s p q a0

/-- The `(2,2)` leg, proved at the Section 4 literal observable
`Support.cutoffHomogenizationErrorRaw22`. -/
theorem unitCubeHomogenizationError_unitRescaledCutoffCoeff_eq_cutoffRaw22
    (M : ABKModel d) (Q : TriadicCube d) (cutoffScale : ℤ) (s : ℝ)
    (sigma : PositiveScalar) (omega : Cutoff.CutoffSample d) :
    Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError s (.finite 2) (.finite 2)
        (unitRescaledCutoffCoeff M Q cutoffScale omega)
        (isotropicComparatorMatrix sigma) =
      Support.cutoffHomogenizationErrorRaw22 M cutoffScale Q.scale s sigma
        (Cutoff.translateCutoffSample (triadicCubeShift Q) omega) := by
  rw [Support.cutoffHomogenizationErrorRaw22_characterization]
  exact unitCubeHomogenizationError_unitRescaledCutoffCoeff M Q cutoffScale s
    (.finite 2) (.finite 2) (isotropicComparatorMatrix sigma) omega

/-! ## The `𝒢₂` annular atom -/

/-- **The `(2,2)` error transport at the `𝒢₂` normalization, cube form.**  The
frozen unit-cube error, read at the coefficient cutoff of level `Q.scale − 2`
rescaled from `Q` onto the unit cube and compared against `σ_{Q.scale−2} Id`,
is exactly the `𝒢₂` atom of `Support.ErrorAtoms` at the sample translated by
the base point of `Q`.

Both sides are the *literal* manuscript quantity, and the equality is exact. -/
theorem unitCubeHomogenizationError22_unitRescaledCutoffCoeff_eq_annularErrorAtom_cube
     (M : ABKModel d) (Q : TriadicCube d) (t : ℝ)
    (omega : Cutoff.CutoffSample d) :
    Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError t (.finite 2) (.finite 2)
        (unitRescaledCutoffCoeff M Q (Q.scale - 2) omega)
        (isotropicComparatorMatrix (Annealed.sigmaBar M (Q.scale - 2))) =
      Support.annularErrorAtom M Q.scale t
        (Cutoff.translateCutoffSample (triadicCubeShift Q) omega) :=
  unitCubeHomogenizationError_unitRescaledCutoffCoeff_eq_cutoffRaw22 M Q
    (Q.scale - 2) t (Annealed.sigmaBar M (Q.scale - 2)) omega

/-- **The `(2,2)` error transport at the `𝒢₂` normalization, lattice form.**
The same identity at the cube `⟨n, v⟩ = 3^n v + □_n` of the Section 4 lattice
enumerations, so that the translation is the lattice point
`Support.triadicLatticePoint n v` in the exact spelling of the good events and
of the frozen annular decomposition. -/
theorem unitCubeHomogenizationError22_unitRescaledCutoffCoeff_eq_annularErrorAtom
     (M : ABKModel d) (n : ℤ) (v : Fin d → ℤ) (t : ℝ)
    (omega : Cutoff.CutoffSample d) :
    Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError t (.finite 2) (.finite 2)
        (unitRescaledCutoffCoeff M (⟨n, v⟩ : TriadicCube d) (n - 2) omega)
        (isotropicComparatorMatrix (Annealed.sigmaBar M (n - 2))) =
      Support.annularErrorAtom M n t
        (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega) := by
  rw [← triadicCubeShift_mk n v]
  exact unitCubeHomogenizationError22_unitRescaledCutoffCoeff_eq_annularErrorAtom_cube
    M (⟨n, v⟩ : TriadicCube d) t omega

/-! ## The measurable-observable corollary (the only a.e. statement here) -/

/-- This is the exact identity above composed with
`Support.annularErrorAtom_ae_eq_annularErrorObservable`, whose null set is the
representative-choice set of the `𝒢₂` lane; the composition is legitimate
because every real translation preserves the cutoff-sample law.  Consumers that
need measurability use this form; consumers that stay at the literal manuscript
quantity use the exact form above. -/
theorem unitCubeHomogenizationError22_unitRescaledCutoffCoeff_ae_eq_annularErrorObservable
     (M : ABKModel d) (n : ℤ) (v : Fin d → ℤ) (t : {t : ℝ // 0 < t}) :
    (fun omega : Cutoff.CutoffSample d =>
        Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError (t : ℝ)
          (.finite 2) (.finite 2)
          (unitRescaledCutoffCoeff M (⟨n, v⟩ : TriadicCube d) (n - 2) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M (n - 2))))
      =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      fun omega : Cutoff.CutoffSample d =>
        Support.annularErrorObservable M n t
          (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega) := by
  have hcomp :=
    (GoodEvents.measurePreserving_translateCutoffSample M
        (Support.triadicLatticePoint n v)).quasiMeasurePreserving.ae_eq_comp
      (Support.annularErrorAtom_ae_eq_annularErrorObservable M n t)
  have hpt : (fun omega : Cutoff.CutoffSample d =>
      Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError (t : ℝ)
        (.finite 2) (.finite 2)
        (unitRescaledCutoffCoeff M (⟨n, v⟩ : TriadicCube d) (n - 2) omega)
        (isotropicComparatorMatrix (Annealed.sigmaBar M (n - 2)))) =
      fun omega : Cutoff.CutoffSample d =>
        Support.annularErrorAtom M n (t : ℝ)
          (Cutoff.translateCutoffSample (Support.triadicLatticePoint n v) omega) :=
    funext fun omega =>
      unitCubeHomogenizationError22_unitRescaledCutoffCoeff_eq_annularErrorAtom
        M n v (t : ℝ) omega
  rw [hpt]
  exact hcomp

end

end Algsuperdiff.Section4.Provider.Annular
