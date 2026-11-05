/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.DoubledPairingCross
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationOrthogonality

/-!
# LocalizationFluctuationDuality

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The duality leg of Step 2 at the genuine localization carriers

Source display in ABK26: the first display of Step 2 of
`l.approximate.recurrence.formula`,

```
fint_{z+cu_n} tilde S_z . bfA_m tilde S_z
  = fint_{z+cu_n} bfF_z . bfA_m tilde S_z
  <= [ bfAhom^{1/2} bfF_z ]_{H^1} [ bfAhom^{-1/2} bfA_m tilde S_z ]_{H^{-1}} .
```

## What this module does

It composes, at the manuscript's own carriers,

* the gauge-conjugated duality bound of
  `CoarseEllipticity.abs_cubeAverage_blockVecDot_le_besovDualityConst` (the
  inequality's companion),

obtaining `hquad` of
`Variational.PerCubeFluctuationArithmetic.perCube_fluct_le` at the localization
cell:

```
2 * doubledMuValue (cubeDomain R) a T  <=  besovDualityConst R s * (Bu * Bg) .
```

The `volumeAverage (openCubeSet R)` of the Chapter-2 pairing and the
`cubeAverage R` of the Besov layer are identified by
`volumeAverage_openCubeSet_eq_cubeAverage`; the cube boundary is Lebesgue null.

The mean-zeroness premises of the duality are discharged internally from
`cubeAverageVec_localizationFz_{potential,flux}`, i.e. from the structure of
`e.Fz.def` itself.

## Binders

`hsub` is the descendant geometry; `hwN` is the defining property of
`w_{N,e'}^{(K)}`; `hT` names `tilde S_z`.  The remaining hypotheses -- the
exponent window `hs`, the gauge positivity `hsig0`, the four `L^2` memberships,
the two cube integrabilities of the corrector fields, the two integrabilities
of the gauged pairing integrands, the sign of `Bg` and the four seminorm
envelopes -- are conditional A obligations of this module, discharged by the
caller at its carrier.  They are not premises of the pinned source statement.

## Scope

No anchor, frozen theorem or external input is consumed, and there is no
`sorry`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The two averages agree -/

/-- The Chapter-2 domain average over the open cube is the Besov layer's cube
average: the cube boundary is Lebesgue null. -/
theorem volumeAverage_openCubeSet_eq_cubeAverage (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (openCubeSet Q) f = cubeAverage Q f := by
  simp [cubeAverage, volumeAverage, volume_openCubeSet_eq_volume_cubeSet,
    volume_cubeSet_toReal, setIntegral_cubeSet_eq_setIntegral_openCubeSet]

/-! ## The duality leg -/

/-- ** at the genuine localization carriers.**

```
fint_R tilde S_z . bfA_m tilde S_z  <=  besovDualityConst R s * ( Bu * Bg )
```

with `Bu` any envelope of the finite-depth negative `q = 2` Besov seminorms of
`bfAhom^{-1/2} bfA_m tilde S_z` and `Bg` any envelope of the finite-depth
positive ones of `bfAhom^{1/2} bfF_z`.

This is the `hquad` leg of
`Variational.PerCubeFluctuationArithmetic.perCube_fluct_le`, with `E` the
Chapter-2 `doubledMuValue` of `tilde S_z` and the manuscript's generic `C`
pinned.

as described in the module docstring. -/
theorem two_mul_doubledMuValue_le_besovDualityConst_localizationFz (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d) (hsub : openCubeSet R ⊆ openCubeSet Q)
    (wD : H10Function (openCubeSet Q)) {wN : H1MeanZeroFunction (openCubeSet Q)}
    (hwN : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) wN
      (fun x => -Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x))
    {a : CoeffOn (cubeDomain R)} {T : DoubledField d}
    (hT : IsDoubledMuMinimizerField (cubeDomain R) a
      (localizationFz sigma omega lowScale highScale e' R wD wN) T)
    {s sig0 Bu Bg : ℝ} (hs : 0 < s) (hsig0 : 0 < sig0) (hBg : 0 ≤ Bg)
    (hwDmem : MemLp wD.toH1Function.grad (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hwNmem : MemLp (neumannFluxField sigma omega lowScale highScale e' wN) (2 : ℝ≥0∞)
      (normalizedCubeMeasure R))
    (hY1 : MemLp
      (fun x => (blockMatVecMul (blockMatrixField a x) (T.eval x)).1)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hY2 : MemLp
      (fun x => (blockMatVecMul (blockMatrixField a x) (T.eval x)).2)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hF1 : MemLp
      (fun x => ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x).1)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hF2 : MemLp
      (fun x => ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x).2)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hInt1 : IntegrableOn
      (fun x =>
        vecDot ((blockGaugeDown sig0 (blockMatVecMul (blockMatrixField a x) (T.eval x))).1)
          (cubeFluctuationVec R
            (fun y => (blockGaugeUp sig0
              ((localizationFz sigma omega lowScale highScale e' R wD wN).eval y)).1) x))
      (cubeSet R) volume)
    (hInt2 : IntegrableOn
      (fun x =>
        vecDot ((blockGaugeDown sig0 (blockMatVecMul (blockMatrixField a x) (T.eval x))).2)
          (cubeFluctuationVec R
            (fun y => (blockGaugeUp sig0
              ((localizationFz sigma omega lowScale highScale e' R wD wN).eval y)).2) x))
      (cubeSet R) volume)
    (hneg1 : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo R s N
      (fun x => (blockGaugeDown sig0 (blockMatVecMul (blockMatrixField a x) (T.eval x))).1) ≤ Bu)
    (hneg2 : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo R s N
      (fun x => (blockGaugeDown sig0 (blockMatVecMul (blockMatrixField a x) (T.eval x))).2) ≤ Bu)
    (hpos1 : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo R s N
      (fun x => (blockGaugeUp sig0
        ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x)).1) ≤ Bg)
    (hpos2 : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo R s N
      (fun x => (blockGaugeUp sig0
        ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x)).2) ≤ Bg) :
    2 * doubledMuValue (cubeDomain R) a T ≤ besovDualityConst R s * (Bu * Bg) := by
  have hzero1 : cubeAverageVec R
      (fun x => ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x).1) = 0 :=
    cubeAverageVec_localizationFz_potential sigma omega lowScale highScale e' R wD wN hwDmem
  have hzero2 : cubeAverageVec R
      (fun x => ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x).2) = 0 :=
    cubeAverageVec_localizationFz_flux sigma omega lowScale highScale e' R wD wN hwNmem
  have hdual := abs_cubeAverage_blockVecDot_le_besovDualityConst R s sig0
    (fun x => (localizationFz sigma omega lowScale highScale e' R wD wN).eval x)
    (fun x => blockMatVecMul (blockMatrixField a x) (T.eval x))
    hs hsig0 hY1 hY2 hF1 hF2 hBg hzero1 hzero2 hInt1 hInt2 hneg1 hneg2 hpos1 hpos2
  have hident := two_mul_doubledMuValue_eq_volumeAverage_localizationFz sigma omega
    lowScale highScale e' R hsub wD hwN hT
  have hpair : volumeAverage ((cubeDomain R : Domain d) : Set (Vec d))
      (doubledBlockPairingIntegrand (cubeDomain R) a
        (localizationFz sigma omega lowScale highScale e' R wD wN) T) =
      cubeAverage R (fun x =>
        blockVecDot ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x)
          (blockMatVecMul (blockMatrixField a x) (T.eval x))) :=
    volumeAverage_openCubeSet_eq_cubeAverage R _
  rw [hident, hpair]
  exact (le_abs_self _).trans hdual

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
