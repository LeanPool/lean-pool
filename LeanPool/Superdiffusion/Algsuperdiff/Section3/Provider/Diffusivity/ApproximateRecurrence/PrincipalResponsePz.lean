/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponsePDef
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellL8
public import LeanPool.HighContrastHomogenization.Support.Multiscale.CubeAverage
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CoerciveH1

/-!
# PrincipalResponsePz

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the localized loads `P_z = (p_z; q_z)` and `F_z`

Source displays in ABK26:

* `e.Pz.def` (label; display):

  ```
  P_z = (p_z; q_z)
    := bfAhom_{m-h}^{-1/2} ( e' + (grad w_{D,e}^{(K)})_{z+cu_n};
  e  + (grad w_{N,e'}^{(K)}
                                    + shom_{m-h}^{-1} h e')_{z+cu_n} ) ,
  ```

* `e.Fz.def` (label; display):

  ```
  F_z := bfAhom_{m-h}^{-1/2}
           ( grad w_{D,e}^{(K)} - (grad w_{D,e}^{(K)})_{z+cu_n};
  grad w_{N,e'}^{(K)} + shom_{m-h}^{-1} h e'
               - (grad w_{N,e'}^{(K)} + shom_{m-h}^{-1} h e')_{z+cu_n} ) ,
  ```

  where `h = k_m - k_{m-h}` is the fresh shell and `(.)_{z+cu_n}` is the
  average over the localization cube.

`F_z` is a field on `R^d`; `P_z` is the constant vector obtained from the same
two fields by averaging them first, so that the affine background is `P_z +
F_z`.  That identity is `principalPz_add_principalFz` below.

## Carriers, and what is and is not a hypothesis

* The normalization scale and the forcing scale are the *same* scale `m - h` in
  the source, so a single `sigma : PositiveScalar` supplies both here; a caller
  cannot accidentally mismatch them.
* The fresh shell is `Cutoff.finiteShellIncrement omega lowScale highScale`,
  entering through the repository's already-proved
  `Provider.Diffusivity.Corrector.streamForcing`, i.e. the forcing of
  `e.def.w`.  In `l.approximate.recurrence.formula` the two scales are
  `lowScale = m - h` and `highScale = m`.
* The localization cube of the source is `z + cu_n` with `n = m - h - 16 ceil
  |log_3 gamma|` (`e.recurrence.params`, display, label).  It enters below only
  as a free `TriadicCube` argument `R`.  No literal buffer constant occurs in
  this module.
* The two correctors enter as the arguments `wD` and `wN` of `e.def.w`'s
  carriers, exactly as in the already-proved `FreshShellL8`, `FreshShellCZ`,
  `FreshShellExistence` and `FreshShellUniqueness`, which quantify over
  solutions rather than selecting one.  Consequently `principalPz` and
  `principalFz` are *functions of the correctors*: they are the manuscript's
  `P_z` and `F_z` exactly when `wD` and `wN` are solutions of `e.def.w`, whose
  existence and gradient-uniqueness are those two modules.  No solution
  property is smuggled in as a hypothesis, and only the two gradient fields
  matter: `Closure.JunctionDischargePrincipalSwitch.principalPz_congr_ae`
  records that almost everywhere equal corrector gradients give the same load.

## Main results

* `neumannFluxField`, `principalPz`, `principalFz`
* `principalPz_fst`, `principalPz_snd` (the components `p_z` and `q_z`)
* `principalPz_add_principalFz`
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## The flux leg field -/

/-- **The flux leg field of `e.Pz.def` and `e.Fz.def`:** `grad w_N + shom^{-1}
(k_high - k_low) e'`.

The additive term is the repository's `streamForcing`, i.e. the forcing of the
Neumann problem `e.def.w` (label, Neumann leg), at the reciprocal of the same
positive scalar that normalizes the load. -/
def neumannFluxField (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e' : Vec d) {Q : TriadicCube d}
    (wN : H1MeanZeroFunction (openCubeSet Q)) : Vec d → Vec d :=
  fun x => wN.toH1Function.grad x +
    Corrector.streamForcing ((sigma : ℝ))⁻¹ omega lowScale highScale e' x

/-! ## `P_z` -/

/-- **`e.Pz.def`.**  The localized principal load

```
P_z = bfAhom^{-1/2} ( e' + (grad w_D)_R; e + (grad w_N + shom^{-1} h e')_R ) ,
```

with `R` the localization cube.  Its two components `(P_z).1` and `(P_z).2` are
the manuscript's `p_z` and `q_z`; their closed forms are `principalPz_fst` and
`principalPz_snd`. -/
def principalPz (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e e' : Vec d) {Q : TriadicCube d}
    (R : TriadicCube d) (wD : H10Function (openCubeSet Q))
    (wN : H1MeanZeroFunction (openCubeSet Q)) : BlockVec d :=
  principalLoad sigma
    (e' + cubeAverageVec R (fun x => wD.toH1Function.grad x),
      e + cubeAverageVec R (neumannFluxField sigma omega lowScale highScale e' wN))

/-- **`p_z`, the potential component of `e.Pz.def`.** -/
theorem principalPz_fst (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e e' : Vec d) {Q : TriadicCube d}
    (R : TriadicCube d) (wD : H10Function (openCubeSet Q))
    (wN : H1MeanZeroFunction (openCubeSet Q)) :
    (principalPz sigma omega lowScale highScale e e' R wD wN).1 =
      inverseSqrtLoad sigma
        (e' + cubeAverageVec R (fun x => wD.toH1Function.grad x)) := by
  rw [principalPz, principalLoad_fst]

/-- **`q_z`, the flux component of `e.Pz.def`.** -/
theorem principalPz_snd (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e e' : Vec d) {Q : TriadicCube d}
    (R : TriadicCube d) (wD : H10Function (openCubeSet Q))
    (wN : H1MeanZeroFunction (openCubeSet Q)) :
    (principalPz sigma omega lowScale highScale e e' R wD wN).2 =
      sqrtLoad sigma
        (e + cubeAverageVec R
          (neumannFluxField sigma omega lowScale highScale e' wN)) := by
  rw [principalPz, principalLoad_snd]

/-! ## `F_z` -/

/-- **`e.Fz.def`.**  The mean-zero fluctuation field

```
F_z(x) = bfAhom^{-1/2} ( grad w_D(x) - (grad w_D)_R;
  (grad w_N + shom^{-1} h e')(x)
                           - (grad w_N + shom^{-1} h e')_R ) .
```

Unlike `P_z` it does not involve `e`, exactly as printed. -/
def principalFz (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e' : Vec d) {Q : TriadicCube d}
    (R : TriadicCube d) (wD : H10Function (openCubeSet Q))
    (wN : H1MeanZeroFunction (openCubeSet Q)) : Vec d → BlockVec d :=
  fun x =>
    principalLoad sigma
      (wD.toH1Function.grad x - cubeAverageVec R (fun y => wD.toH1Function.grad y),
        neumannFluxField sigma omega lowScale highScale e' wN x -
          cubeAverageVec R
            (neumannFluxField sigma omega lowScale highScale e' wN))

/-- The potential component of `F_z`. -/
theorem principalFz_fst (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e' : Vec d) {Q : TriadicCube d}
    (R : TriadicCube d) (wD : H10Function (openCubeSet Q))
    (wN : H1MeanZeroFunction (openCubeSet Q)) (x : Vec d) :
    (principalFz sigma omega lowScale highScale e' R wD wN x).1 =
      inverseSqrtLoad sigma
        (wD.toH1Function.grad x -
          cubeAverageVec R (fun y => wD.toH1Function.grad y)) := by
  rw [principalFz, principalLoad_fst]

/-- The flux component of `F_z`. -/
theorem principalFz_snd (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e' : Vec d) {Q : TriadicCube d}
    (R : TriadicCube d) (wD : H10Function (openCubeSet Q))
    (wN : H1MeanZeroFunction (openCubeSet Q)) (x : Vec d) :
    (principalFz sigma omega lowScale highScale e' R wD wN x).2 =
      sqrtLoad sigma
        (neumannFluxField sigma omega lowScale highScale e' wN x -
          cubeAverageVec R
            (neumannFluxField sigma omega lowScale highScale e' wN)) := by
  rw [principalFz, principalLoad_snd]

/-! ## The affine background -/

/-- **.**  `P_z + F_z` is the normalized *unaveraged* slope pair, i.e. the affine
background inside which the source's `X_z` is minimized.  This is the identity
behind the split `X_z = S_z + tilde S_z` recorded at tex -/
theorem principalPz_add_principalFz (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e e' : Vec d)
    {Q : TriadicCube d} (R : TriadicCube d) (wD : H10Function (openCubeSet Q))
    (wN : H1MeanZeroFunction (openCubeSet Q)) (x : Vec d) :
    principalPz sigma omega lowScale highScale e e' R wD wN +
        principalFz sigma omega lowScale highScale e' R wD wN x =
      principalLoad sigma
        (e' + wD.toH1Function.grad x,
          e + neumannFluxField sigma omega lowScale highScale e' wN x) := by
  rw [principalPz, principalFz, ← principalLoad_add]
  congr 1
  refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add] <;> abel

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
