/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.DoubledPairingGauge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationActualBackground

/-!
# LocalizationFluctuationOrthogonality

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Euler--Lagrange identity of Step 2 at the genuine localization carriers

Source displays in ABK26:

* `e.Fz.def`, the background field `bfF_z`;
* the `tilde S_z` display;
  ```
  fint_{z+cu_n} tilde S_z . bfA_m tilde S_z = fint_{z+cu_n} bfF_z . bfA_m tilde S_z .
  ```

## What this module does

`two_mul_doubledMuValue_eq_volumeAverage_of_isDoubledMuMinimizerField`
proves the identity for an abstract ambient slope field `F`.  This module
**instantiates it at the manuscript's own data**: the localization cell
`R = z + cu_n`, the background `localizationFz` of `e.Fz.def`, and the ambient
premise discharged by
`LocalizationActualBackground.isDoubledAmbientField_localizationFz`.  Existence
of the `argmin` at the same carriers is instantiated alongside, so the identity
is never asserted about a field that has not been produced.

What mean-zeroness *is* used for -- the duality step, where `bfF_z` enters the
pairing through its cube fluctuation -- is prepared by
`localizationFz_potential_eq_smul_cubeFluctuationVec` and its flux companion,
which record that both legs of `e.Fz.def` are literal cube fluctuations on the
very cell `R` that indexes them.

## Binders

`sigma`, `omega`, `lowScale`, `highScale`, `e'`, `Q`, `R`, `wD`, `wN` are the
manuscript's own data; `hwN` is the defining property of `w_{N,e'}^{(K)}`;
`hsub : openCubeSet R subseteq openCubeSet Q` is the descendant geometry of the
mesoscopic tiling, discharged at the call sites.  The two mean-zero statements
carry, in addition, the cube integrability of the corrector gradient and of the
Neumann flux field on the cell; these are conditional A obligations of this
module, not premises of the pinned source statement.  No smallness or moment
proposition occurs.

## Scope

No anchor, frozen theorem or external input is consumed, and there is no
`sorry`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2; `e.Fz.def`; the `tilde S_z`
  display.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3.Observable
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## `bfF_z` is a cube fluctuation on its own cell -/

/-- **The potential leg of `e.Fz.def` is a scaled cube fluctuation.**  This is
the structural form of the manuscript's "`bfF_z` has mean zero in `z + cu_n`":
the subtracted constant is the average over the very cell that indexes the
field. -/
theorem localizationFz_potential_eq_smul_cubeFluctuationVec (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d)
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q)) :
    (localizationFz sigma omega lowScale highScale e' R wD wN).potential =
      (Real.sqrt (sigma : ℝ))⁻¹ • cubeFluctuationVec R wD.toH1Function.grad := by
  rw [localizationFz_potential]
  funext x
  rfl

/-- **The flux leg of `e.Fz.def` is a scaled cube fluctuation.** -/
theorem localizationFz_flux_eq_smul_cubeFluctuationVec (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d)
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q)) :
    (localizationFz sigma omega lowScale highScale e' R wD wN).flux =
      Real.sqrt (sigma : ℝ) •
        cubeFluctuationVec R (neumannFluxField sigma omega lowScale highScale e' wN) := by
  rw [localizationFz_flux]
  funext x
  rfl

/-- **The cell mean-zeroness of `e.Fz.def`, potential leg.**  `bfF_z` has zero
average on `z + cu_n`.  This is the property the manuscript quotes it is *not*
what proves, but it is exactly what the duality step needs, since the upstream
duality theorem pairs against a cube fluctuation.

: on the cube integrability `hwD` of the corrector gradient, which is what
makes the subtracted average finite. -/
theorem cubeAverageVec_localizationFz_potential (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d)
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q))
    (hwD : MemLp wD.toH1Function.grad (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    cubeAverageVec R (localizationFz sigma omega lowScale highScale e' R wD wN).potential =
      0 := by
  rw [localizationFz_potential_eq_smul_cubeFluctuationVec]
  change cubeAverageVec R
    (fun x => (Real.sqrt (sigma : ℝ))⁻¹ • cubeFluctuationVec R wD.toH1Function.grad x) = 0
  rw [CoarseEllipticity.cubeAverageVec_const_smul,
    CoarseEllipticity.cubeAverageVec_cubeFluctuationVec R _ hwD, smul_zero]

/-- **The cell mean-zeroness of `e.Fz.def`, flux leg.** -/
theorem cubeAverageVec_localizationFz_flux (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d)
    (wD : H10Function (openCubeSet Q)) (wN : H1MeanZeroFunction (openCubeSet Q))
    (hwN : MemLp (neumannFluxField sigma omega lowScale highScale e' wN) (2 : ℝ≥0∞)
      (normalizedCubeMeasure R)) :
    cubeAverageVec R (localizationFz sigma omega lowScale highScale e' R wD wN).flux = 0 := by
  rw [localizationFz_flux_eq_smul_cubeFluctuationVec]
  change cubeAverageVec R
    (fun x => Real.sqrt (sigma : ℝ) •
      cubeFluctuationVec R (neumannFluxField sigma omega lowScale highScale e' wN) x) = 0
  rw [CoarseEllipticity.cubeAverageVec_const_smul,
    CoarseEllipticity.cubeAverageVec_cubeFluctuationVec R _ hwN, smul_zero]

/-! ## at the genuine carriers -/

/-- **The Euler--Lagrange identity, at the manuscript's own data.**  For a
minimizer `T = tilde S_z` of the doubled energy over `bfF_z + (L^2_{pot,0} x
Lsolo)(R)`,

```
fint_R tilde S_z . bfA_m tilde S_z = fint_R bfF_z . bfA_m tilde S_z ,
```

in the factor-`2` normalization of `LocalizationBasicSplit.lean`
(`fint X . bfA X = 2 * doubledMuValue`).

The ambient premise is discharged by `isDoubledAmbientField_localizationFz`;
mean-zeroness of `bfF_z` is used nowhere. -/
theorem two_mul_doubledMuValue_eq_volumeAverage_localizationFz (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d) (hsub : openCubeSet R ⊆ openCubeSet Q)
    (wD : H10Function (openCubeSet Q)) {wN : H1MeanZeroFunction (openCubeSet Q)}
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) wN
      (fun x => -Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x))
    {a : CoeffOn (cubeDomain R)} {T : DoubledField d}
    (hT : IsDoubledMuMinimizerField (cubeDomain R) a
      (localizationFz sigma omega lowScale highScale e' R wD wN) T) :
    2 * doubledMuValue (cubeDomain R) a T =
      volumeAverage ((cubeDomain R : Domain d) : Set (Vec d))
        (doubledBlockPairingIntegrand (cubeDomain R) a
          (localizationFz sigma omega lowScale highScale e' R wD wN) T) :=
  two_mul_doubledMuValue_eq_volumeAverage_of_isDoubledMuMinimizerField
    (isDoubledAmbientField_localizationFz sigma omega lowScale highScale e' R hsub wD hwN) hT

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
