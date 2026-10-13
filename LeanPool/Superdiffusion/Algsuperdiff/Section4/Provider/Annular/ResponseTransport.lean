/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchActualShell
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.JCarrierRescale
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.SubConstFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ErrorAtoms

/-!
# ResponseTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The response transport: `J(z+□_n; ã_{L,m})` at the unit-cube perturbation

ABK26, Section 4.1, Step 2 of `p.mathcalE.annular.decomp` writes

> we apply Lemma `l.J.sensitivity.no.conditions` with `μ := σ_m σ_{n−2}^{-1}`,
> `σ₀ := σ_{n−2}` and `h := k_L − (k_L − k_m)_{□_m} − k_{n−2}` **to each cube
> `z + □_n`**

and obtains a bound whose left-hand side is `J(z+□_n, σ_m^{-1/2}e,
σ_m^{1/2}e; ã_{L,m})` with `ã_{L,m} = a_L − (k_L − k_m)_{□_m}`.  The cited
lemma is stated on the **unit** cube `□₀` only, so the single word "apply"
compresses a translation and a dilation.  (Its *error* half is
`ErrorTransport.lean`; the `λ` half was already proved as
`unitCubeLambda_unitRescaledCutoffCoeff`.)

## The identity

For every triadic cube `Q = z + □_j`, every `L` above the cutoff level, and
every antisymmetric constant `C`,

```
J(Q, p, q; a_L − C)
   =  J(□₀, p, q; a_{lowScale}(z + 3^j ·) + 1 · (h − C)) ,
```

where the perturbation on the right is the frozen `W^{2,∞}` carrier
`Provider.Diffusivity.ApproximateRecurrence.centeredShellUnitCube`, i.e. the
manuscript's centered fresh shell rescaled onto the unit cube.  Both sides are
the *same* number; no constant and no inequality direction is introduced.

## Route

Three proved steps and one new one.

1. **Translation** (new here).  `Internal.Ch02.book_responseJ_eq_ResponseJ` is
   stated at a fully general `(U : Domain d)` and `(a : CoeffOn U)`, so it
   rewrites the Chapter 2 response of the `ã_{L,m}` object as the raw
   `ResponseJ` of its representative;
   `ResponseJ_translateSet_eq_translateCoeffField` is the covariance under a
   real translation of the domain; and
   `Cutoff.coefficientCutoff_translateCutoffSample` moves the translation from
   the field to the sample.  The subtracted constant is translation-inert, so
   the route is exactly that of the proved
   `Provider.Multiscale.responseJ_cutoff_translateCutoffSample`.
2. **Dilation** (proved, family-general).
   `Provider.Multiscale.responseJ_originCube_dilate` is stated for an arbitrary
   `TriadicCoeffFamily`, so it applies to `subConstCutoffTriadicCoeffFamily`
   with no change.
3. **The shell link** (new here).  `CoeffOn.dilate` stores an *internal*
   `pointwiseCoeffField` representative, not the literal rescaled field, so the
   dilated `ã_{L,m}` object and the perturbed object are compared through their
   a.e. descriptions: `unitRescaledSubConstCoeff_toCoeffField_ae_eq` says the
   first is a.e. the rescaled cutoff field minus `C`, and
   `ApproximateRecurrence.centeredShellUnitCube_shift` says the second is
   *pointwise* exactly that.  `Ch02.responseJ_eq_ofAEEq` closes the comparison.

The a.e. description is obtained by running the two dilation identities — the
one for `subConstCutoffTriadicCoeffFamily` and the one for
`Cutoff.coefficientCutoffTriadicCoeffFamily` — against each other: the
representative-level pullback `dilateCoeffField` is a precomposition, so
subtracting a constant commutes with it definitionally.

## Almost-everywhere, and why

Unlike the error transport of `ErrorTransport.lean`, this identity is proved
through a genuine a.e. comparison of two coefficient objects.  No null set
survives into the conclusion.

## References

* ABK26, (`ã_{L,m}`), (`e.ugly.estimate.for.J.pre`), (`e.ugly.estimate.for.J`),
  (`l.J.sensitivity.no.conditions`, stated on `□₀`).
-/

namespace Algsuperdiff.Section4.Provider.Annular

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

variable {d : ℕ}

/-! ## Translation covariance at the constant-shifted cutoff -/

/-- **One-cube translation covariance of the Chapter 2 response for
`ã_{L,m} = a_L − C`.**  If the open realization of `T` is the translate by `v`
of that of `R`, then the response of `a_L − C` at `T` equals the one at `R` for
the translated sample.  The subtracted constant is translation-inert, so it
simply rides along.

This is the exact analogue, at the constant-shifted field, of the proved
`Provider.Multiscale.responseJ_cutoff_translateCutoffSample`. -/
theorem responseJ_subConstCutoff_translateCutoffSample (M : ABKModel d) (L : ℤ)
    (C : Mat d) (hC : matTranspose C = -C) (v : Vec d) {R T : TriadicCube d}
    (hset : openCubeSet T = translateSet v (openCubeSet R)) (p q : Vec d)
    (omega : Cutoff.CutoffSample d) :
    responseJ (cubeDomain T)
        ((subConstCutoffTriadicCoeffFamily M L C hC omega).coeffOn T) p q =
      responseJ (cubeDomain R)
        ((subConstCutoffTriadicCoeffFamily M L C hC
          (Cutoff.translateCutoffSample v omega)).coeffOn R) p q := by
  rw [HCPolySupport.Internal.Ch02.book_responseJ_eq_ResponseJ,
    HCPolySupport.Internal.Ch02.book_responseJ_eq_ResponseJ]
  show ResponseJ (openCubeSet T) p q (subConstCutoffField M L C omega) =
    ResponseJ (openCubeSet R) p q
      (subConstCutoffField M L C (Cutoff.translateCutoffSample v omega))
  rw [hset, ResponseJ_translateSet_eq_translateCoeffField]
  refine congrArg (fun a : CoeffField d => ResponseJ (openCubeSet R) p q a) ?_
  funext x
  show Cutoff.coefficientCutoff M.nu L omega (fun i => x i + v i) - C =
    Cutoff.coefficientCutoff M.nu L (Cutoff.translateCutoffSample v omega) x - C
  rw [Cutoff.coefficientCutoff_translateCutoffSample]
  rfl

/-! ## The rescaled unit-cube object of `ã_{L,m}` -/

/-- The constant-shifted cutoff `a_L − C`, rescaled from the cube `Q = z + □_j` to
the unit cube by the manuscript's map `y ↦ z + 3^j y`, as a unit-cube
coefficient object.  This is the `ã_{L,m}` sibling of the proved
`Provider.BadEvents.unitRescaledCutoffCoeff`. -/
def unitRescaledSubConstCoeff (M : ABKModel d) (Q : TriadicCube d) (L : ℤ)
    (C : Mat d) (hC : matTranspose C = -C) (omega : Cutoff.CutoffSample d) :
    CoeffOn (cubeDomain (originCube d 0)) :=
  (TriadicCoeffFamily.dilate (-Q.scale)
    (subConstCutoffTriadicCoeffFamily M L C hC
      (Cutoff.translateCutoffSample (triadicCubeShift Q) omega))).coeffOn
    (originCube d 0)

/-- **The response transport, unrescaled form.**  The response of the rescaled
`ã_{L,m}` object on the unit cube is the response of `ã_{L,m}` on the cube `Q`
itself. -/
theorem responseJ_unitRescaledSubConstCoeff (M : ABKModel d) (Q : TriadicCube d)
    (L : ℤ) (C : Mat d) (hC : matTranspose C = -C) (p q : Vec d)
    (omega : Cutoff.CutoffSample d) :
    responseJ (cubeDomain (originCube d 0))
        (unitRescaledSubConstCoeff M Q L C hC omega) p q =
      responseJ (cubeDomain Q)
        ((subConstCutoffTriadicCoeffFamily M L C hC omega).coeffOn Q) p q := by
  rw [unitRescaledSubConstCoeff,
    Provider.Multiscale.responseJ_originCube_dilate]
  exact (responseJ_subConstCutoff_translateCutoffSample M L C hC
    (triadicCubeShift Q)
    (openCubeSet_eq_translateSet_originCube_of_triadicCube Q) p q omega).symm

/-! ## The a.e. description of the rescaled field -/

/-- The coefficient field of the rescaled `ã_{L,m}` object is, almost everywhere
on the open unit cube, the rescaled cutoff field minus the constant.

The proof runs the two dilation identities against each other: the
representative-level pullback `dilateCoeffField` is a precomposition, so
subtracting a constant commutes with it definitionally.  No literal description
of either side is needed. -/
theorem unitRescaledSubConstCoeff_toCoeffField_ae_eq (M : ABKModel d)
    (Q : TriadicCube d) (L : ℤ) (C : Mat d) (hC : matTranspose C = -C)
    (omega : Cutoff.CutoffSample d) :
    (unitRescaledSubConstCoeff M Q L C hC omega).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (originCube d 0))]
      fun y : Vec d =>
        (unitRescaledCutoffCoeff M Q L omega).toCoeffField y - C := by
  have hsub := (TriadicCoeffFamily.isDilation_dilate (-Q.scale)
      (subConstCutoffTriadicCoeffFamily M L C hC
        (Cutoff.translateCutoffSample (triadicCubeShift Q) omega))
      (originCube d Q.scale)).coeff_ae_eq
  have hcut := (TriadicCoeffFamily.isDilation_dilate (-Q.scale)
      (Cutoff.coefficientCutoffTriadicCoeffFamily M L
        (Cutoff.translateCutoffSample (triadicCubeShift Q) omega))
      (originCube d Q.scale)).coeff_ae_eq
  rw [dilateCube_neg_originCube Q.scale] at hsub hcut
  filter_upwards [hsub, hcut] with y hy hy'
  rw [unitRescaledSubConstCoeff, unitRescaledCutoffCoeff]
  rw [hy, hy']
  rfl

/-! ## The shell link -/

/-- **The dilated `ã_{L,m}` object is the frozen perturbed object.**  The
rescaled `a_L − C` coefficient object and the frozen `perturbCoeffOn` of the
rescaled `a_{lowScale}` by the manuscript's centered fresh shell at `t = 1`
agree almost everywhere on the open unit cube.

`ApproximateRecurrence.centeredShellUnitCube_shift` supplies the *pointwise*
identity for the right-hand side; the only a.e. step is the internal
representative that `CoeffOn.dilate` selects on the left. -/
theorem unitRescaledSubConstCoeff_aeEq_perturbCoeffOn (M : ABKModel d)
    (Q : TriadicCube d) {lowScale L : ℤ} (hle : lowScale ≤ L) (C : Mat d)
    (hC : matTranspose C = -C) (omega : Cutoff.CutoffSample d) :
    CoeffOn.AEEq (unitRescaledSubConstCoeff M Q L C hC omega)
      (perturbCoeffOn (cubeDomain (originCube d 0))
        (unitRescaledCutoffCoeff M Q lowScale omega)
        (centeredShellUnitCube M Q hle omega C hC).toLInfSkewMatrixFieldOn 1) := by
  filter_upwards [unitRescaledSubConstCoeff_toCoeffField_ae_eq M Q L C hC omega]
    with y hy
  rw [hy, centeredShellUnitCube_shift M Q hle omega C hC y]

/-! ## The transport -/

/-- **The response transport of `ã_{L,m}`** (the response half of ABK26's silent
rescaling).

The Chapter 2 response of the manuscript's `ã_{L,m} = a_L − C` on an arbitrary
triadic cube `Q = z + □_j` is *exactly* the unit-cube response of the frozen
perturbed object that the Section 2.4 sensitivity anchor consumes: the rescaled
cutoff `a_{lowScale}(z + 3^j ·)` perturbed at `t = 1` by the manuscript's
centered fresh shell.

This is the identification the manuscript performs silently when it applies the
unit-cube lemma `l.J.sensitivity.no.conditions` "to each cube `z + □_n`".  It is
an equality, so no constant is created and no inequality direction is fixed. -/
theorem responseJ_subConstCutoff_cube_eq_perturbCoeffOn (M : ABKModel d)
    (Q : TriadicCube d) {lowScale L : ℤ} (hle : lowScale ≤ L) (C : Mat d)
    (hC : matTranspose C = -C) (p q : Vec d) (omega : Cutoff.CutoffSample d) :
    responseJ (cubeDomain Q)
        ((subConstCutoffTriadicCoeffFamily M L C hC omega).coeffOn Q) p q =
      responseJ (cubeDomain (originCube d 0))
        (perturbCoeffOn (cubeDomain (originCube d 0))
          (unitRescaledCutoffCoeff M Q lowScale omega)
          (centeredShellUnitCube M Q hle omega C hC).toLInfSkewMatrixFieldOn 1)
        p q := by
  rw [← responseJ_unitRescaledSubConstCoeff M Q L C hC p q omega]
  exact responseJ_eq_ofAEEq
    (unitRescaledSubConstCoeff_aeEq_perturbCoeffOn M Q hle C hC omega) p q

/-- **The response transport at the Section 4 lattice enumerations.**  The same
identity at the cube `⟨n, v⟩ = 3^n v + □_n` and at the `𝒢₂` cutoff level
`n − 2`, i.e. in the exact spelling in which the ugly chain reads it. -/
theorem responseJ_subConstCutoff_lattice_eq_perturbCoeffOn (M : ABKModel d)
    (n : ℤ) (v : Fin d → ℤ) {L : ℤ} (hle : n - 2 ≤ L) (C : Mat d)
    (hC : matTranspose C = -C) (p q : Vec d) (omega : Cutoff.CutoffSample d) :
    responseJ (cubeDomain (⟨n, v⟩ : TriadicCube d))
        ((subConstCutoffTriadicCoeffFamily M L C hC omega).coeffOn
          (⟨n, v⟩ : TriadicCube d)) p q =
      responseJ (cubeDomain (originCube d 0))
        (perturbCoeffOn (cubeDomain (originCube d 0))
          (unitRescaledCutoffCoeff M (⟨n, v⟩ : TriadicCube d) (n - 2) omega)
          (centeredShellUnitCube M (⟨n, v⟩ : TriadicCube d) hle omega C hC).toLInfSkewMatrixFieldOn
          1)
        p q :=
  responseJ_subConstCutoff_cube_eq_perturbCoeffOn M (⟨n, v⟩ : TriadicCube d) hle
    C hC p q omega

/-! ## The manuscript's own constant -/

/-- The manuscript's averaged flux increment `(k_L − k_m)_{□_m}` is
antisymmetric as a matrix, in the `matTranspose` spelling the constructions
above require.  This is the entrywise `Support.fluxIncrementAverage_skew`. -/
theorem matTranspose_fluxIncrementAverage (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    matTranspose (Support.fluxIncrementAverage M L m Q omega) =
      -Support.fluxIncrementAverage M L m Q omega := by
  ext i j
  show Support.fluxIncrementAverage M L m Q omega j i =
    -Support.fluxIncrementAverage M L m Q omega i j
  exact Support.fluxIncrementAverage_skew M L m Q omega i j

/-- **The response transport at the manuscript's own `ã_{L,m}`.**  The constant is
`(k_L − k_m)_{□_m}`, whose antisymmetry is the proved
`Support.fluxIncrementAverage_skew`, and the cube is the lattice cube `⟨n, v⟩`.

This is the left-hand side of `e.ugly.estimate.for.J.pre` read at the unit-cube
object that the frozen sensitivity anchor consumes. -/
theorem responseJ_fluxCorrectedConst_lattice_eq_perturbCoeffOn (M : ABKModel d)
    (n : ℤ) (v : Fin d → ℤ) {L : ℤ} (hle : n - 2 ≤ L) (m : ℤ) (p q : Vec d)
    (omega : Cutoff.CutoffSample d) :
    responseJ (cubeDomain (⟨n, v⟩ : TriadicCube d))
        ((subConstCutoffTriadicCoeffFamily M L
          (Support.fluxIncrementAverage M L m (originCube d m) omega)
          (matTranspose_fluxIncrementAverage M L m (originCube d m) omega)
          omega).coeffOn (⟨n, v⟩ : TriadicCube d)) p q =
      responseJ (cubeDomain (originCube d 0))
        (perturbCoeffOn (cubeDomain (originCube d 0))
          (unitRescaledCutoffCoeff M (⟨n, v⟩ : TriadicCube d) (n - 2) omega)
          (centeredShellUnitCube M (⟨n, v⟩ : TriadicCube d) hle omega
            (Support.fluxIncrementAverage M L m (originCube d m) omega)
            (matTranspose_fluxIncrementAverage M L m (originCube d m)
              omega)).toLInfSkewMatrixFieldOn 1)
        p q :=
  responseJ_subConstCutoff_lattice_eq_perturbCoeffOn M n v hle
    (Support.fluxIncrementAverage M L m (originCube d m) omega)
    (matTranspose_fluxIncrementAverage M L m (originCube d m) omega) p q omega

end

end Algsuperdiff.Section4.Provider.Annular
