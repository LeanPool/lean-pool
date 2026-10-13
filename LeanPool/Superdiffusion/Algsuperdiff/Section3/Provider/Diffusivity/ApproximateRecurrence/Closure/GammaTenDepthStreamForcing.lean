/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationDisplay
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationTail
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationApproxForcing
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.StreamForcingDeriv

/-!
# GammaTenDepthStreamForcing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The oscillation cell of the fresh-shell forcing itself

ABK26, `e.nablaw.oscillations`, `e.def.w`.

## Why this is needed

The Neumann leg of `bfF_z` is not the Neumann corrector's gradient: by
`PrincipalResponsePz.neumannFluxField` it is

```
  neumannFluxField sigma omega lo hi e' wN
    = wN.grad + streamForcing sigma^{-1} omega lo hi e' ,
```

and the proved oscillation display of `LocalizationOscillationDisplay` bounds
the oscillation of the **gradient** only.  The second summand is a
deterministic `C^1` field, so its oscillation on a cube of scale `n` is
controlled by the cube side `3^n` times the sup of its differential --- and
that differential is exactly the shell-derivative gauge `shellDerivNormSum` in
which the display's own forcing term is already written.

## What is proved

* `openCubeAtScale_subset_of_le` --- concentric open cubes are monotone in the
  scale.
* `meshOscillationCell_streamForcing_le` --- **the bound**: for `n <= lowScale`,

  ```
    meshOscillationCell n (streamForcing sigmaInv omega lo hi e') R
      <=  3^n * (sigmaInv * d * |e'|_2 *
            shellDerivNormSum lo hi (triadicCubeShift R) omega) .
  ```

  The dimensional factor is `d`, not `sqrt d`: one `sqrt d` is the
  sup-to-Euclidean conversion on the *input* of the coordinate differential
  (`StreamForcingDeriv.norm_fderiv_streamForcing_coord_le`) and the second is the
  coordinate-sum of the mean-square deviation
  (`OscillationApproxForcing.sqrt_meanSquareOscillationVecOn_le_of_norm_fderiv_le`).
  Neither is absorbed.

## Binders

`0 <= sigmaInv` and the scale gate `n <= lowScale`, which is what makes the
shell-derivative gauge --- read on `z + cu_{lowScale}` --- a majorant on the
oscillation cube `z + cu_n`.  No model, no probability, no corrector and no
smallness gate occurs; the statement is deterministic pointwise calculus about
the forcing.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `e.nablaw.oscillations`, `e.def.w`, `e.W.1.inf.bound`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector

noncomputable section

variable {d : ℕ}

/-- Concentric open cubes are monotone in the scale.  Unconditional. -/
theorem openCubeAtScale_subset_of_le (z : Vec d) {n ell : ℤ} (h : n ≤ ell) :
    openCubeAtScale z n ⊆ openCubeAtScale z ell := by
  intro y hy i
  have hy' : |y i - z i| < Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) / 2 := hy i
  have h3 : Real.rpow (3 : ℝ) ((n : ℤ) : ℝ) ≤ Real.rpow (3 : ℝ) ((ell : ℤ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast h)
  show |y i - z i| < Real.rpow (3 : ℝ) ((ell : ℤ) : ℝ) / 2
  linarith

/-- **The oscillation cell of the fresh-shell forcing.**

On the cube `z + cu_n` based at the cell's own site `z = triadicCubeShift R`, the
normalized `L^2` oscillation of `streamForcing sigmaInv omega lo hi e'` is at
most the cube side `3^n` times `sigmaInv * d * |e'|_2` times the summed
first-derivative shell gauges of `e.W.1.inf.bound` read at base point `z`.

only on `0 <= sigmaInv` and on `n <= lowScale`, which puts the oscillation cube
inside the cube on which the gauge is read. -/
theorem meshOscillationCell_streamForcing_le {sigmaInv : ℝ} (hsigma : 0 ≤ sigmaInv)
    (omega : ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d) (n : ℤ)
    (hn : n ≤ lowScale) (R : TriadicCube d) :
    meshOscillationCell n
        (streamForcing sigmaInv omega lowScale highScale e') R ≤
      (3 : ℝ) ^ n * (sigmaInv * (d : ℝ) * Book.Ch02.vecNorm e' *
        shellDerivNormSum lowScale highScale (triadicCubeShift R) omega) := by
  classical
  set z : Vec d := triadicCubeShift R with hz
  set G : ℝ := shellDerivNormSum lowScale highScale z omega with hG
  have hG0 : 0 ≤ G := shellDerivNormSum_nonneg _ _ _ _
  set M : ℝ := sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e' * G with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (mul_nonneg (mul_nonneg hsigma (Real.sqrt_nonneg _))
      (Book.Ch02.vecNorm_nonneg e')) hG0
  have hdiff : ∀ i : Fin d,
      Differentiable ℝ fun y =>
        streamForcing sigmaInv omega lowScale highScale e' y i := fun i =>
    differentiable_streamForcing_coord sigmaInv omega lowScale highScale e' i
  have hbound : ∀ x ∈ openCubeAtScale z n, ∀ i : Fin d,
      ‖fderiv ℝ (fun y =>
        streamForcing sigmaInv omega lowScale highScale e' y i) x‖ ≤ M := by
    intro x hx i
    have hxl : x ∈ openCubeAtScale z lowScale := openCubeAtScale_subset_of_le z hn hx
    have hgauge :
        ShellField.matrixDerivativeNorm
          (∑ k ∈ Finset.Ioc lowScale highScale, ShellField.deriv (omega k) x) ≤ G :=
      matrixDerivativeNorm_sum_deriv_le_sum_localCubeDerivNorm_translate
        lowScale (Finset.Ioc lowScale highScale) z omega hxl
    have hhead : (0 : ℝ) ≤ sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e' :=
      mul_nonneg (mul_nonneg hsigma (Real.sqrt_nonneg _)) (Book.Ch02.vecNorm_nonneg e')
    refine (norm_fderiv_streamForcing_coord_le sigmaInv omega lowScale highScale e'
      i x).trans ?_
    rw [abs_of_nonneg hsigma, hM]
    exact mul_le_mul_of_nonneg_left hgauge hhead
  have hatom := sqrt_meanSquareOscillationVecOn_le_of_norm_fderiv_le hM0 hdiff z n hbound
  have hsqd : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hhalf : Real.sqrt (d : ℝ) * M = sigmaInv * (d : ℝ) * Book.Ch02.vecNorm e' * G := by
    rw [hM]
    calc Real.sqrt (d : ℝ) * (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e' * G)
        = (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) *
            (sigmaInv * Book.Ch02.vecNorm e' * G) := by ring
      _ = (d : ℝ) * (sigmaInv * Book.Ch02.vecNorm e' * G) := by rw [hsqd]
      _ = sigmaInv * (d : ℝ) * Book.Ch02.vecNorm e' * G := by ring
  have hrw : Real.sqrt (d : ℝ) * M * (3 : ℝ) ^ n =
      (3 : ℝ) ^ n * (sigmaInv * (d : ℝ) * Book.Ch02.vecNorm e' * G) := by
    rw [hhalf]; ring
  rw [meshOscillationCell, ← hz, ← hrw]
  exact hatom

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
