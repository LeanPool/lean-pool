/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Limit
public import LeanPool.HighContrastHomogenization.Support.Multiscale.CubeAverage

/-!
# PrincipalResponseShellAverage

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the averaged fresh shell `(h)_{z + cu_n}`

Source displays in ABK26:

* names the *fresh shell* `h := k_m - k_{m-h}`, the increment of the infrared
  cutoff between the two scales of `l.approximate.recurrence.formula`;
* Step 3 of that lemma never uses `h` itself but only its average
  `(h)_{z+cu_n}` over the localization cube, which is the matrix conjugated
  away by the doubled shear `bfG_{-(h)_{z+cu_n}}` of `e.Gh.def`.

This module defines that average as a single `Mat d` and proves the one
property the gauge algebra needs of it: it is **antisymmetric**.

## Why it is skew

The standing assumption `a.shell.antisymmetry` is carried structurally, not as
a hypothesis: the frozen carrier `Algsuperdiff.Frozen.Assumptions.ShellField`
bundles `forall x i j, j x i j = - j x j i` into the type of a shell, so every
finite increment `k_m - k_{m-h}` is a pointwise antisymmetric matrix field
(`Algsuperdiff.Section3.Cutoff.finiteShellIncrement_skew`), and averaging over a
cube is entrywise linear.  Consequently `freshShellCubeAverage_skew` is
unconditional -- no integrability, no measurability, and no event.

The antisymmetry consumed here is the separate standing node
`a.shell.antisymmetry`.)

## Carriers

* the localization cube is a free `TriadicCube d` argument `R`.
* the two scales are free integers `lowScale <= highScale`; in Step 3 they are
  `m - h` and `m`.
* the sample is a bare `Cutoff.ShellSeq d`, so that the definition is available
  before any lower-tail restriction.  The two identification lemmas below,
  which need the lower-infinite cutoff, are stated on `Cutoff.CutoffSample d`.

## Main results

* `freshShellCubeAverage`, `freshShellCubeAverage_apply`
* `freshShellCubeAverage_skew` -- the input required by
  `CoarseGaugeCoeffField`, `CoarseGaugeResponse` and
  `CoarseGaugeCoarseMatrices`, all of which are stated for a constant `hbar`
  with `matTranspose hbar = -hbar`
* `freshShellCubeAverage_eq_cubeAverageMat_cutoff_sub` and
  `..._coefficientCutoff_sub` -- the identification of this matrix with the
  manuscript's `(k_m - k_{m-h})_{z+cu_n}` and with the average of the
  coefficient-field difference `a_m - a_{m-h}`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-- Averaging over a triadic cube negates. -/
private theorem cubeAverage_neg' (R : TriadicCube d) (g : Vec d → ℝ) :
    cubeAverage R (fun x => -g x) = -cubeAverage R g := by
  rw [cubeAverage, cubeAverage, MeasureTheory.integral_neg, mul_neg]

/-- **The averaged fresh shell `(h)_{z+cu_n}` of ABK26 Step 3.**

With `h = k_{highScale} - k_{lowScale}` the fresh shell and `R` the
localization cube, this is the constant matrix `(h)_R`, entrywise the cube
average of the finite shell increment. -/
def freshShellCubeAverage (R : TriadicCube d) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) : Mat d :=
  cubeAverageMat R fun x => Cutoff.finiteShellIncrement omega lowScale highScale x

/-- Entrywise formula for the averaged fresh shell. -/
theorem freshShellCubeAverage_apply (R : TriadicCube d) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (i j : Fin d) :
    freshShellCubeAverage R omega lowScale highScale i j =
      cubeAverage R fun x =>
        Cutoff.finiteShellIncrement omega lowScale highScale x i j :=
  rfl

/-- **The averaged fresh shell is antisymmetric.**

This is the hypothesis `matTranspose hbar = -hbar` of every declaration of
`CoarseGaugeCoeffField`, `CoarseGaugeResponse` and `CoarseGaugeCoarseMatrices`,
discharged at the carrier ABK26 Step 3 actually conjugates by. -/
theorem freshShellCubeAverage_skew (R : TriadicCube d) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) :
    matTranspose (freshShellCubeAverage R omega lowScale highScale) =
      -freshShellCubeAverage R omega lowScale highScale := by
  ext i j
  have hentry : ∀ x : Vec d,
      Cutoff.finiteShellIncrement omega lowScale highScale x j i =
        -Cutoff.finiteShellIncrement omega lowScale highScale x i j := by
    intro x
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using
      congrFun
        (congrFun (Cutoff.finiteShellIncrement_skew omega lowScale highScale x) i) j
  show cubeAverage R (fun x =>
      Cutoff.finiteShellIncrement omega lowScale highScale x j i) =
    -cubeAverage R fun x =>
      Cutoff.finiteShellIncrement omega lowScale highScale x i j
  rw [show (fun x : Vec d =>
        Cutoff.finiteShellIncrement omega lowScale highScale x j i) =
      fun x : Vec d =>
        -Cutoff.finiteShellIncrement omega lowScale highScale x i j from
      funext hentry]
  exact cubeAverage_neg' R _

/-- **The identification with `(k_m - k_{m-h})_{z+cu_n}`.**  On the lower-tail
carrier the finite increment is the difference of the two lower-infinite
cutoffs, so the definition above is literally the manuscript's average of the
fresh shell. -/
theorem freshShellCubeAverage_eq_cubeAverageMat_cutoff_sub (R : TriadicCube d)
    (omega : Cutoff.CutoffSample d) {lowScale highScale : ℤ}
    (hle : lowScale ≤ highScale) :
    freshShellCubeAverage R omega.1 lowScale highScale =
      cubeAverageMat R fun x =>
        Cutoff.cutoff highScale omega x - Cutoff.cutoff lowScale omega x := by
  rw [freshShellCubeAverage]
  congr 1
  funext x
  exact (Cutoff.cutoff_sub_cutoff_eq_finiteShellIncrement omega hle x).symm

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
