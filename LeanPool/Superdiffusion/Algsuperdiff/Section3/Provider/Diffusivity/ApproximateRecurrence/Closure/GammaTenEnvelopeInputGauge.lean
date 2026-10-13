/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenCloserMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationOrthogonality

/-!
# GammaTenEnvelopeInputGauge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Besov tower of the gauged `bfF_z` is a constant multiple of the raw one

ABK26, Step 2 of `l.approximate.recurrence.formula`, `e.Fz.def`.

## What this module does

`Closure.GammaTenCloserAssembly.ClosureBesovEnvelopeInput` is stated at the two
legs of the **gauged** field `bfA_0^{1/2} bfF_z`, i.e. at

```
  x |->  ( blockGaugeUp sigma_0 ( (localizationFz shom_n omega n (n+h) e' R wD wN).eval x ) ).1
  x |->  ( blockGaugeUp sigma_0 ( (localizationFz shom_n omega n (n+h) e' R wD wN).eval x ) ).2 .
```

`LocalizationFluctuationOrthogonality` identifies the two legs of `bfF_z` as
scaled **cube fluctuations** of the two raw fields --- the Dirichlet corrector
gradient and the Neumann flux field.  Since the gauge is a scalar, each gauged
leg is a *constant* multiple of a cube fluctuation, and the finite-depth positive
`q = 2` Besov seminorm is

* absolutely homogeneous in a scalar multiple, and
* unchanged by subtracting a constant --- which is what `cubeFluctuationVec R`
  does --- by CoarseGraining's
  `cubeBesovPositiveVectorPartialSeminormTwo_sub_const`.

Consequently the entire Besov tower of each gauged leg is a fixed scalar times
the tower of the corresponding **raw** field, and the oscillation input of Step 2
never has to be read at the gauged field at all: it suffices to control the
oscillation of `grad w_D` and of `neumannFluxField`, which is exactly what
`LocalizationOscillationDisplay`'s free-buffer display does.

## What is proved

* `cubeLpNorm_const_smul_vec`, `cubeFluctuationVec_const_smul` --- homogeneity of
  the two building blocks.
* `cubeBesovPositiveVectorDepthAverage_const_smul`,
  `cubeBesovPositiveVectorPartialSeminormTwo_const_smul` --- homogeneity of the
  depth average (degree `2`) and of the seminorm (degree `1`).
* `cubeBesovPositiveVectorPartialSeminormTwo_cubeFluctuationVec` --- the tower
  does not see the cube fluctuation.
* `cubeBesovPositiveVectorPartialSeminormTwo_gauged_localizationFz_potential` and
  `..._flux` --- **the two identities**: the tower of each gauged leg equals the
  scalar `|sqrt sigma_0 . sqrt shom_n^{-1}|`, resp.
  `|sqrt sigma_0^{-1} . sqrt shom_n|`, times the tower of the raw field.

## Binders

Only the `L^2` membership of the raw field on the descendants of the cell, the
standing integrability that makes the subtracted cube average finite.  No
smallness gate, no moment, no measurability and no sample-space proposition
occurs.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `e.Fz.def`, Step 2 of `l.approximate.recurrence.formula`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Homogeneity of the tower -/

theorem cubeLpNorm_const_smul_vec (Q : TriadicCube d) (p : ℝ≥0∞) (c : ℝ)
    (v : Vec d → Vec d) :
    cubeLpNorm Q p (fun x => c • v x) = |c| * cubeLpNorm Q p v := by
  unfold cubeLpNorm
  have hfun : (fun x => c • v x) = c • v := rfl
  rw [hfun, MeasureTheory.eLpNorm_const_smul]
  simp [ENNReal.toReal_mul, Real.norm_eq_abs]

theorem cubeFluctuationVec_const_smul (Q : TriadicCube d) (c : ℝ) (u : Vec d → Vec d) :
    cubeFluctuationVec Q (fun x => c • u x) = fun x => c • cubeFluctuationVec Q u x := by
  funext x
  show (fun y => c • u y) x - cubeAverageVec Q (fun y => c • u y) =
    c • (u x - cubeAverageVec Q u)
  rw [cubeAverageVec_const_smul, smul_sub]

theorem cubeBesovPositiveVectorDepthAverage_const_smul (Q : TriadicCube d) (c : ℝ)
    (u : Vec d → Vec d) (j : ℕ) :
    cubeBesovPositiveVectorDepthAverage Q (fun x => c • u x) j =
      c ^ (2 : ℕ) * cubeBesovPositiveVectorDepthAverage Q u j := by
  unfold cubeBesovPositiveVectorDepthAverage
  rw [← descendantsAverage_mul_left]
  refine congrArg (descendantsAverage Q j) (funext fun R => ?_)
  rw [cubeFluctuationVec_const_smul, cubeLpNorm_const_smul_vec, mul_pow, sq_abs]

theorem cubeBesovPositiveVectorPartialSeminormTwo_const_smul (Q : TriadicCube d) (s : ℝ)
    (N : ℕ) (c : ℝ) (u : Vec d → Vec d) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => c • u x) =
      |c| * cubeBesovPositiveVectorPartialSeminormTwo Q s N u := by
  unfold cubeBesovPositiveVectorPartialSeminormTwo
  have hterm : ∀ j : ℕ,
      (cubeBesovPositiveVectorDepthSeminorm Q s (fun x => c • u x) j) ^ 2 =
        c ^ (2 : ℕ) * (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2 := by
    intro j
    rw [sq_cubeBesovPositiveVectorDepthSeminorm, sq_cubeBesovPositiveVectorDepthSeminorm,
      cubeBesovPositiveVectorDepthAverage_const_smul]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum,
    Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]

/-- **The tower does not see the cube fluctuation.**

on the `L^2` membership of the field on the descendants of `Q`, the standing
integrability that makes the subtracted cube average finite. -/
theorem cubeBesovPositiveVectorPartialSeminormTwo_cubeFluctuationVec (Q : TriadicCube d)
    (s : ℝ) (N : ℕ) (u : Vec d → Vec d)
    (hmem : ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
      MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (cubeFluctuationVec Q u) =
      cubeBesovPositiveVectorPartialSeminormTwo Q s N u := by
  have hfun : cubeFluctuationVec Q u = fun x => u x - cubeAverageVec Q u := rfl
  rw [hfun]
  exact cubeBesovPositiveVectorPartialSeminormTwo_sub_const Q s N u (cubeAverageVec Q u) hmem

/-! ## The two gauged legs -/

/-- **The potential leg of the gauged `bfF_z`, at the Besov tower.**  Its tower on
`R` is the scalar `|sqrt sigma_0 . (sqrt shom)^{-1}|` times the tower of the raw
Dirichlet corrector gradient.

on the `L^2` membership `hmem` of the raw gradient. -/
theorem cubeBesovPositiveVectorPartialSeminormTwo_gauged_localizationFz_potential
    (sig0 : ℝ) (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e' : Vec d) {Qc : TriadicCube d} (R : TriadicCube d)
    (wD : H10Function (openCubeSet Qc)) (wN : H1MeanZeroFunction (openCubeSet Qc))
    (s : ℝ) (N : ℕ)
    (hmem : ∀ j ∈ Finset.range (N + 1), ∀ S ∈ descendantsAtDepth R j,
      MemLp wD.toH1Function.grad (2 : ℝ≥0∞) (normalizedCubeMeasure S)) :
    cubeBesovPositiveVectorPartialSeminormTwo R s N
        (fun x => (blockGaugeUp sig0
          ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x)).1) =
      |Real.sqrt sig0 * (Real.sqrt (sigma : ℝ))⁻¹| *
        cubeBesovPositiveVectorPartialSeminormTwo R s N wD.toH1Function.grad := by
  have hleg : (fun x => (blockGaugeUp sig0
      ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x)).1) =
      fun x => (Real.sqrt sig0 * (Real.sqrt (sigma : ℝ))⁻¹) •
        cubeFluctuationVec R wD.toH1Function.grad x := by
    funext x
    have hpot := congrFun
      (localizationFz_potential_eq_smul_cubeFluctuationVec sigma omega lowScale highScale e'
        R wD wN) x
    show Real.sqrt sig0 •
      (localizationFz sigma omega lowScale highScale e' R wD wN).potential x = _
    rw [hpot]
    show Real.sqrt sig0 • ((Real.sqrt (sigma : ℝ))⁻¹ •
      cubeFluctuationVec R wD.toH1Function.grad x) = _
    rw [smul_smul]
  rw [hleg, cubeBesovPositiveVectorPartialSeminormTwo_const_smul,
    cubeBesovPositiveVectorPartialSeminormTwo_cubeFluctuationVec R s N _ hmem]

/-- **The flux leg of the gauged `bfF_z`, at the Besov tower.**  Its tower on `R`
is the scalar `|(sqrt sigma_0)^{-1} . sqrt shom|` times the tower of the raw
Neumann flux field.

on the `L^2` membership `hmem` of the raw flux field. -/
theorem cubeBesovPositiveVectorPartialSeminormTwo_gauged_localizationFz_flux
    (sig0 : ℝ) (sigma : PositiveScalar) (omega : Cutoff.ShellSeq d)
    (lowScale highScale : ℤ) (e' : Vec d) {Qc : TriadicCube d} (R : TriadicCube d)
    (wD : H10Function (openCubeSet Qc)) (wN : H1MeanZeroFunction (openCubeSet Qc))
    (s : ℝ) (N : ℕ)
    (hmem : ∀ j ∈ Finset.range (N + 1), ∀ S ∈ descendantsAtDepth R j,
      MemLp (neumannFluxField sigma omega lowScale highScale e' wN) (2 : ℝ≥0∞)
        (normalizedCubeMeasure S)) :
    cubeBesovPositiveVectorPartialSeminormTwo R s N
        (fun x => (blockGaugeUp sig0
          ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x)).2) =
      |(Real.sqrt sig0)⁻¹ * Real.sqrt (sigma : ℝ)| *
        cubeBesovPositiveVectorPartialSeminormTwo R s N
          (neumannFluxField sigma omega lowScale highScale e' wN) := by
  have hleg : (fun x => (blockGaugeUp sig0
      ((localizationFz sigma omega lowScale highScale e' R wD wN).eval x)).2) =
      fun x => ((Real.sqrt sig0)⁻¹ * Real.sqrt (sigma : ℝ)) •
        cubeFluctuationVec R (neumannFluxField sigma omega lowScale highScale e' wN) x := by
    funext x
    have hflux := congrFun
      (localizationFz_flux_eq_smul_cubeFluctuationVec sigma omega lowScale highScale e'
        R wD wN) x
    show (Real.sqrt sig0)⁻¹ •
      (localizationFz sigma omega lowScale highScale e' R wD wN).flux x = _
    rw [hflux]
    show (Real.sqrt sig0)⁻¹ • (Real.sqrt (sigma : ℝ) •
      cubeFluctuationVec R (neumannFluxField sigma omega lowScale highScale e' wN) x) = _
    rw [smul_smul]
  rw [hleg, cubeBesovPositiveVectorPartialSeminormTwo_const_smul,
    cubeBesovPositiveVectorPartialSeminormTwo_cubeFluctuationVec R s N _ hmem]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
