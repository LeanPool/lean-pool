/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationPerCube

/-!
# GammaTenAssemblySide

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The analytic side conditions of the per-cube fluctuation bound

ABK26, Step 2 of `l.approximate.recurrence.formula`, at the carrier of
`e.lower.bound.localization.terms`.

## The gap this module fills

`LocalizationFluctuationPerCube.perCube_localizationFluctuation_le` is stated
with eight *analytic side conditions* --- the six `L^2` memberships `hwDmem`,
`hwNmem`, `hY1`, `hY2`, `h, `h at the **normalized cube measure**, and the two
spatial integrabilities `hInt1`, `hInt2` of the gauged pairing integrands ---
which its own docstring records as "conditional A obligations of this module,
discharged by the caller at its carrier".  This module discharges all eight,
once and for all, at the carriers a consumer of Step 2 reads them at.

Nothing here is a source display: every statement below is a transport between
two spellings of `L^2` on one triadic cube, an application of the block
ellipticity bound of `Section24.Sensitivity.Provider.Path.Densities`, or a
Cauchy--Schwarz.

## What is proved

* `memLp_two_normalizedCubeMeasure_of_memVectorL2` --- the transport, and the
  exact converse of CoarseGraining's
  `memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure`: the normalized cube
  measure is a *finite* scalar multiple of `volume.restrict (cubeSet R)`, and
  the cube boundary is Lebesgue null, so the three spellings `MemVectorL2
  (openCubeSet R)`, `MemVectorL2 (cubeSet R)` and `MemLp _ 2
  (normalizedCubeMeasure R)` agree.  Every membership below is produced in the
  `MemVectorL2` spelling and pushed through it.
* `memLp_two_gradH10_normalizedCubeMeasure_of_subset` --- `hwDmem`, from
  CoarseGraining's `H1Function.grad_memVectorL2` restricted to the cell.
* `memLp_two_neumannFluxField_normalizedCubeMeasure` --- `hwNmem`; the stream
  forcing is continuous, hence in every `L^p` of a bounded cube.
* `memLp_two_localizationFz_fst` / `..._snd` --- `h, `h, from the proved
  `LocalizationActualBackground.memVectorL2_localizationFz_{potential,flux}`.
* `memLp_two_blockMatVecMul_blockMatrixField_fst` / `..._snd` --- `hY1`, `hY2`.
  This is the `CoeffOn.Lam`-boundedness step: `bfA(a)` has a.e. bounded blocks
  because `a` is uniformly elliptic (`lam <= . <= Lam`), so it maps vector
  `L^2` to vector `L^2`.  The work is CoarseGraining-side and was already
  carried out in
  `Section24.Sensitivity.Provider.Path.Densities.memVectorL2_blockMatrixField_{fst,snd}`;
  what is added here is only the transport of the carrier.
* `memVectorL2_potential_of_isDoubledResponseField` / `..._flux` --- the two
  `L^2` legs of a response field, i.e. the projections of
  `IsDoubledResponseField = IsDoubledAmbientField ∧ (Euler--Lagrange)`
  (`Homogenization.Book.Ch02.DoubledResponse`).  These are what a caller has
  about the field `tilde S_z` that the split produces.
* `memVectorL2_cubeFluctuationVec` and `integrableOn_gaugedPairing_fst` /
  `..._snd` --- `hInt1`, `hInt2`: the gauged block image is `L^2`, the gauged
  fluctuation of `bfF_z` is `L^2` (a constant is subtracted from an `L^2` field
  on a finite-measure set), and Cauchy--Schwarz pairs them.

The eight are consumed together, in the order and shape
`perCube_localizationFluctuation_le` reads them, by
`Closure.GammaTenAssemblyCell`.

## Binders

The geometry `hsub : openCubeSet R ⊆ openCubeSet Q` (which is what makes the
correctors of the localization cube `Q` readable on the cell `R`) and, for the
two `hY` statements and the two integrabilities, the two `L^2` legs of the
response field.  No estimate, no smallness, no moment and no measurability in
the sample occurs: everything below is spatial, at one fixed sample point.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2, `e.Pz.def`, `e.Fz.def`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section24.Sensitivity.Provider.Path
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The two carrier transports -/

/-- **The transport of item 1: vector `L^2` on the cell becomes `L^2` of the
normalized cube measure.**

This is the converse of CoarseGraining's
`memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure`. -/
theorem memLp_two_normalizedCubeMeasure_of_memVectorL2 (R : TriadicCube d)
    {f : Vec d → Vec d} (hf : MemVectorL2 (openCubeSet R) f) :
    MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
  have hcube : MemLp f (2 : ℝ≥0∞) (cubeMeasure R) := by
    simpa [cubeMeasure, MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R] using hf
  simpa [normalizedCubeMeasure] using hcube.smul_measure ENNReal.ofReal_ne_top

/-! ## The two `L^2` legs of a response field -/

/-- The potential leg of a doubled response field is vector `L^2`: it is the
first projection of `IsDoubledAmbientField`. -/
theorem memVectorL2_potential_of_isDoubledResponseField {U : Domain d} {a : CoeffOn U}
    {T : DoubledField d} (hT : IsDoubledResponseField U a T) :
    MemVectorL2 (U : Set (Vec d)) T.potential := hT.1.1.1

/-- The flux leg of a doubled response field is vector `L^2`. -/
theorem memVectorL2_flux_of_isDoubledResponseField {U : Domain d} {a : CoeffOn U}
    {T : DoubledField d} (hT : IsDoubledResponseField U a T) :
    MemVectorL2 (U : Set (Vec d)) T.flux := hT.1.2.1

/-! ## `hwDmem` and `hwNmem` -/

/-- **`hwDmem`.**  The gradient of an `H^1_0(cu_K)` corrector is `L^2` of the
normalized measure of every cell of `cu_K`. -/
theorem memLp_two_gradH10_normalizedCubeMeasure_of_subset {Q : TriadicCube d}
    (R : TriadicCube d)
    (hsub : openCubeSet R ⊆ openCubeSet Q) (wD : H10Function (openCubeSet Q)) :
    MemLp wD.toH1Function.grad (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
  memLp_two_normalizedCubeMeasure_of_memVectorL2 R
    (memVectorL2_of_subset hsub wD.toH1Function.grad_memVectorL2)

/-- **`hwNmem`.**  The flux leg field `grad w_N + shom^{-1} h e'` of `e.Pz.def`
is `L^2` of the normalized measure of every cell: the gradient by
`H1Function.grad_memVectorL2`, the stream forcing because it is continuous. -/
theorem memLp_two_neumannFluxField_normalizedCubeMeasure (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d) (hsub : openCubeSet R ⊆ openCubeSet Q)
    (wN : H1MeanZeroFunction (openCubeSet Q)) :
    MemLp (neumannFluxField sigma omega lowScale highScale e' wN) (2 : ℝ≥0∞)
      (normalizedCubeMeasure R) := by
  refine memLp_two_normalizedCubeMeasure_of_memVectorL2 R ?_
  have hgrad : MemVectorL2 (openCubeSet R) wN.toH1Function.grad :=
    memVectorL2_of_subset hsub wN.toH1Function.grad_memVectorL2
  have hforcing : MemVectorL2 (openCubeSet R)
      (Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e') :=
    Corrector.memVectorL2_openCubeSet_of_continuous R
      (Corrector.continuous_streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e')
  exact hgrad.add hforcing

/-! ## `h and `h -/

/-- **`hF1`.**  The potential leg of `bfF_z` is `L^2` of the normalized measure of the
cell. -/
theorem memLp_two_localizationFz_fst (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d) (hsub : openCubeSet R ⊆ openCubeSet Q)
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q)) :
    MemLp (fun x => ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x).1)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
  memLp_two_normalizedCubeMeasure_of_memVectorL2 R
    (memVectorL2_localizationFz_potential sigma omega lowScale highScale e' R R hsub wD wN)

/-- **`hF2`.**  The flux leg of `bfF_z` is `L^2` of the normalized measure of the
cell. -/
theorem memLp_two_localizationFz_snd (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d) (hsub : openCubeSet R ⊆ openCubeSet Q)
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q)) :
    MemLp (fun x => ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x).2)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
  memLp_two_normalizedCubeMeasure_of_memVectorL2 R
    (memVectorL2_localizationFz_flux sigma omega lowScale highScale e' R R hsub wD wN)

/-! ## `hY1` and `hY2`: the `CoeffOn.Lam`-boundedness step -/

/-- **`hY1`.**  The potential component of `bfA(a) T` is `L^2` of the normalized
cube measure whenever both legs of `T` are vector `L^2`.

The content is the uniform ellipticity of `a` (`lam <= . <= Lam`), which bounds
the four blocks of `blockMatrixField a` a.e.; that step is CoarseGraining-side,
proved as
`Section24.Sensitivity.Provider.Path.memVectorL2_blockMatrixField_fst`. -/
theorem memLp_two_blockMatVecMul_blockMatrixField_fst (R : TriadicCube d)
    (a : CoeffOn (cubeDomain R)) {T : DoubledField d}
    (hpot : MemVectorL2 (openCubeSet R) T.potential)
    (hflux : MemVectorL2 (openCubeSet R) T.flux) :
    MemLp (fun x => (blockMatVecMul (blockMatrixField a x) (T.eval x)).1) (2 : ℝ≥0∞)
      (normalizedCubeMeasure R) :=
  memLp_two_normalizedCubeMeasure_of_memVectorL2 R
    (memVectorL2_blockMatrixField_fst a hpot hflux)

/-- **`hY2`.**  The flux component of `bfA(a) T` is `L^2` of the normalized cube
measure whenever both legs of `T` are vector `L^2`. -/
theorem memLp_two_blockMatVecMul_blockMatrixField_snd (R : TriadicCube d)
    (a : CoeffOn (cubeDomain R)) {T : DoubledField d}
    (hpot : MemVectorL2 (openCubeSet R) T.potential)
    (hflux : MemVectorL2 (openCubeSet R) T.flux) :
    MemLp (fun x => (blockMatVecMul (blockMatrixField a x) (T.eval x)).2) (2 : ℝ≥0∞)
      (normalizedCubeMeasure R) :=
  memLp_two_normalizedCubeMeasure_of_memVectorL2 R
    (memVectorL2_blockMatrixField_snd a hpot hflux)

/-! ## `hInt1` and `hInt2`: Cauchy--Schwarz of two `L^2` fields -/

/-- The cube fluctuation of a vector-`L^2` field is vector `L^2`: a constant is
subtracted, and the cell has finite measure. -/
theorem memVectorL2_cubeFluctuationVec (R : TriadicCube d) {u : Vec d → Vec d}
    (hu : MemVectorL2 (openCubeSet R) u) :
    MemVectorL2 (openCubeSet R) (cubeFluctuationVec R u) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    Corrector.isFiniteMeasure_volumeMeasureOn_openCubeSet R
  have hconst : MemVectorL2 (openCubeSet R) (fun _ : Vec d => cubeAverageVec R u) :=
    memVectorL2_const _
  simpa [cubeFluctuationVec] using! hu.sub hconst

/-- **`hInt1`.**  The potential-leg gauged pairing integrand is integrable on the
cell: both factors are vector `L^2` there. -/
theorem integrableOn_gaugedPairing_fst (R : TriadicCube d) (sig0 : ℝ)
    (a : CoeffOn (cubeDomain R)) {T F : DoubledField d}
    (hpot : MemVectorL2 (openCubeSet R) T.potential)
    (hflux : MemVectorL2 (openCubeSet R) T.flux)
    (hFpot : MemVectorL2 (openCubeSet R) F.potential) :
    IntegrableOn
      (fun x =>
        vecDot ((blockGaugeDown sig0 (blockMatVecMul (blockMatrixField a x) (T.eval x))).1)
          (cubeFluctuationVec R (fun y => (blockGaugeUp sig0 (F.eval y)).1) x))
      (cubeSet R) volume := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    Corrector.isFiniteMeasure_volumeMeasureOn_openCubeSet R
  have hY : MemVectorL2 (openCubeSet R)
      (fun x => (blockMatVecMul (blockMatrixField a x) (T.eval x)).1) :=
    memVectorL2_blockMatrixField_fst a hpot hflux
  have hgaugeY : MemVectorL2 (openCubeSet R)
      (fun x => (blockGaugeDown sig0 (blockMatVecMul (blockMatrixField a x) (T.eval x))).1) := by
    simpa [blockGaugeDown] using! hY.const_smul (Real.sqrt sig0)⁻¹
  have hgaugeF : MemVectorL2 (openCubeSet R)
      (fun y => (blockGaugeUp sig0 (F.eval y)).1) := by
    simpa [blockGaugeUp] using! hFpot.const_smul (Real.sqrt sig0)
  exact integrableOn_cubeSet_iff_integrableOn_openCubeSet.2
    (integrableOn_vecDot_of_memVectorL2 hgaugeY
      (memVectorL2_cubeFluctuationVec R hgaugeF))

/-- **`hInt2`.**  The flux-leg gauged pairing integrand is integrable on the cell. -/
theorem integrableOn_gaugedPairing_snd (R : TriadicCube d) (sig0 : ℝ)
    (a : CoeffOn (cubeDomain R)) {T F : DoubledField d}
    (hpot : MemVectorL2 (openCubeSet R) T.potential)
    (hflux : MemVectorL2 (openCubeSet R) T.flux)
    (hFflux : MemVectorL2 (openCubeSet R) F.flux) :
    IntegrableOn
      (fun x =>
        vecDot ((blockGaugeDown sig0 (blockMatVecMul (blockMatrixField a x) (T.eval x))).2)
          (cubeFluctuationVec R (fun y => (blockGaugeUp sig0 (F.eval y)).2) x))
      (cubeSet R) volume := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    Corrector.isFiniteMeasure_volumeMeasureOn_openCubeSet R
  have hY : MemVectorL2 (openCubeSet R)
      (fun x => (blockMatVecMul (blockMatrixField a x) (T.eval x)).2) :=
    memVectorL2_blockMatrixField_snd a hpot hflux
  have hgaugeY : MemVectorL2 (openCubeSet R)
      (fun x => (blockGaugeDown sig0 (blockMatVecMul (blockMatrixField a x) (T.eval x))).2) := by
    simpa [blockGaugeDown] using! hY.const_smul (Real.sqrt sig0)
  have hgaugeF : MemVectorL2 (openCubeSet R)
      (fun y => (blockGaugeUp sig0 (F.eval y)).2) := by
    simpa [blockGaugeUp] using! hFflux.const_smul (Real.sqrt sig0)⁻¹
  exact integrableOn_cubeSet_iff_integrableOn_openCubeSet.2
    (integrableOn_vecDot_of_memVectorL2 hgaugeY
      (memVectorL2_cubeFluctuationVec R hgaugeF))

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
