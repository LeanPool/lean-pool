/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponsePz
public import LeanPool.HighContrastHomogenization.Support.Besov.Localization
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.Basic

/-!
# PrincipalResponseLegsBudgetEllipticity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: sub-step (ii) of the principal response, the ellipticity budget

Source display, immediately preceding the independence sentence:

```
avsum_{z in 3^n Zd cap cu_K}
  E[ shom_{m-h} |p_z|^2 + shom_{m-h}^{-1} |q_z|^2 ] <= C ,
```

quoted from `e.nablaw.in.L.eight` (label).  Here `(p_z; q_z) = P_z` is the
localized load of `e.Pz.def` (label), carried in this repository by
`principalPz` with components `principalPz_fst` and `principalPz_snd`.

## What this module proves

Because `P_z` is by definition `bfAhom_{m-h}^{-1/2}` applied to the raw averaged
slope pair, the two normalizations cancel exactly against the two weights
`shom_{m-h}` and `shom_{m-h}^{-1}` of the display.  The integrand is therefore an
*unnormalized* quantity:

* `ellipticityBudget_eq` -- the exact collapse

  ```
  shom |p_z|^2 + shom^{-1}|q_z|^2
    = |e' + (grad w_D)_R|^2 + |e + (grad w_N + shom^{-1} h e')_R|^2 ,
  ```

  an unconditional identity, with `R` the localization cube.

The per-cube Jensen step, the grid average over the triadic subcubes of `cu_K`
at the localization scale, and the passage to expectations all belong to the
consuming lane.  Carried out there, this identity gives the manuscript's
left-hand side bounded by
`2(|e|^2 + |e'|^2) + 2 E[ ‖grad w_D‖^2_{L^2(cu_K)} ] +
 2 E[ ‖grad w_N + shom^{-1} h e'‖^2_{L^2(cu_K)} ]`,
which is what `e.nablaw.in.L.eight` is quoted for.

## The grid rendering

The source averages over the lattice `3^n Zd cap cu_K`, i.e. over the cubes `z
+ cu_n` tiling `cu_K`.  Those cubes are exactly the triadic descendants of
`cu_K` at depth `K - n`, and the repository's `descendantsAverage` is the
corresponding average; this is the standard rendering used throughout
`Provider/BadEvents` and elsewhere in this tree.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Observable
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The collapse of the two normalizations -/

private theorem vecNormSq_inverseSqrtLoad_eq (sigma : PositiveScalar) (x : Vec d) :
    vecNormSq (inverseSqrtLoad sigma x) = (sigma : ℝ)⁻¹ * vecNormSq x := by
  rw [inverseSqrtLoad, vecNormSq_smul, ← Real.sqrt_inv,
    Real.sq_sqrt (inv_pos.2 sigma.2).le]

private theorem vecNormSq_sqrtLoad_eq (sigma : PositiveScalar) (x : Vec d) :
    vecNormSq (sqrtLoad sigma x) = (sigma : ℝ) * vecNormSq x := by
  rw [sqrtLoad, vecNormSq_smul, Real.sq_sqrt sigma.2.le]

/-- **The integrand, collapsed.**  The weights `shom_{m-h}` and `shom_{m-h}^{-1}`
cancel the two legs of the normalization `bfAhom_{m-h}^{-1/2}` in `e.Pz.def`
exactly, leaving the squared lengths of the *raw* averaged slope pair. -/
theorem ellipticityBudget_eq (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e e' : Vec d) {Q : TriadicCube d}
    (R : TriadicCube d) (wD : H10Function (openCubeSet Q))
    (wN : H1MeanZeroFunction (openCubeSet Q)) :
    (sigma : ℝ) *
        vecNormSq
          (principalPz sigma omega lowScale highScale e e' R wD wN).1 +
        (sigma : ℝ)⁻¹ *
          vecNormSq
            (principalPz sigma omega lowScale highScale e e' R wD wN).2 =
      vecNormSq (e' + cubeAverageVec R (fun x => wD.toH1Function.grad x)) +
        vecNormSq
          (e + cubeAverageVec R
            (neumannFluxField sigma omega lowScale highScale e' wN)) := by
  have hne : (sigma : ℝ) ≠ 0 := ne_of_gt sigma.2
  rw [principalPz_fst, principalPz_snd, vecNormSq_inverseSqrtLoad_eq,
    vecNormSq_sqrtLoad_eq, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hne,
    inv_mul_cancel₀ hne, one_mul, one_mul]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
