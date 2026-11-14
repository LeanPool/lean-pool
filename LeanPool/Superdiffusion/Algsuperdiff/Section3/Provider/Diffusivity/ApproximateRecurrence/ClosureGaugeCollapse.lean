/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseLoadMeas
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellSumZeroDirection

/-!
# ClosureGaugeCollapse

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The per-cube collapse of the gauged doubled quadratic form

ABK26, `l.approximate.recurrence.formula`, Steps 4 and 5.

Both Step-4 and Step-5 displays start from the same per-cube identity: the
gauged doubled quadratic form

`| bfAhom_{m-h}^{1/2} G_{-(h)_{z+cu_n}} bfAhom_{m-h}^{-1/2} P_z |^2`

collapses to two scalar slots.  This module proves that collapse at the exact
carrier the closure consumes (`gaugedPrincipalLoadShell`, the load), once and
for all, and reads it at the Step-5 branch `e' = 0`.

## The identity

With

* `a = e' + (grad w_D)_R` the potential slot,
* `b = e + (grad w_N + shom^{-1} h e')_R` the flux slot, and
* `H = (h)_R = freshShellCubeAverage R omega n m` the averaged fresh shell,

the two `shom^{±1/2}` normalizations of `P_z` cancel against the two diagonal
weights `shom^{±1}` and the identity is

`|a|^2 + |b - shom^{-1} H a|^2`.

That is exactly the right-hand side of the manuscript's own per-cube displays:
there at `e = 0`, `w_D = 0`, and there at `e' = 0`, `w_N = 0`, expanded into
its four terms.

## What is supplied

* `blockVecDot_gaugedPrincipalLoadShell_blockDiag` — the collapse, at every
  direction pair.  It is an **unconditional algebraic identity**: no solution,
  measurability, selection or normalization property of `wD`, `wN` is used, and
  no binder is carried.
* `neumannFluxField_zero_direction` — at `e' = 0` the flux leg field is the bare
  Neumann corrector gradient, the fresh-shell term of `e.Pz.def` vanishing with
  its direction.
* `blockVecDot_gaugedPrincipalLoadShell_blockDiag_flux` — the collapse read at
  the Step-5 branch `e' = 0`, again unconditionally.  The remaining
  `(grad w_N)_R` is killed by
  `Provider.Diffusivity.Corrector.FreshShellSumZeroDirection` at any consumer
  that carries the Neumann weak-solution binder; that reduction is deliberately
  *not* performed here, so that this module stays hypothesis-free.

## What is *not* here

Neither Step-4 nor Step-5 endpoint is proved, and neither
`Closure.Step4GaugeEndpoint` nor `Closure.Step5GaugeEndpoint` is discharged:
those need the corrector-energy display at the *localization grid*, which is a
different obligation.  Nothing below realizes a source node.

## References

* ABK26, `e.Pz.def`; the gauged load.
* ABK26, `e.lower.bound.pre1`; `e.lower.bound.pre2`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-- **The per-cube collapse of the gauged doubled quadratic form.**

The two `shom^{±1/2}` normalizations of `P_z` cancel against the two diagonal
weights `shom^{±1}`, leaving the potential slot `|e' + (grad w_D)_R|^2` and the
sheared flux slot `|(e + (grad w_N + shom^{-1} h e')_R) - shom^{-1} (h)_R
(e' + (grad w_D)_R)|^2`.

Unconditional: `wD` and `wN` are bare families and nothing is assumed of
them. -/
theorem blockVecDot_gaugedPrincipalLoadShell_blockDiag (sigma : PositiveScalar)
    {Q : TriadicCube d} (R : TriadicCube d) (n m : ℤ) (e e' : Vec d)
    (wD : Cutoff.ShellSeq d → H10Function (openCubeSet Q))
    (wN : Cutoff.ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (omega : Cutoff.ShellSeq d) :
    blockVecDot (gaugedPrincipalLoadShell sigma R n m e e' wD wN omega)
        (blockMatVecMul
          (Ch02.blockDiag ((sigma : ℝ) • (1 : Mat d)) (((sigma : ℝ))⁻¹ • (1 : Mat d)))
          (gaugedPrincipalLoadShell sigma R n m e e' wD wN omega))
      = vecNormSq (e' + cubeAverageVec R (fun x => (wD omega).toH1Function.grad x))
        + vecNormSq
            ((e + cubeAverageVec R (neumannFluxField sigma omega n m e' (wN omega)))
              - ((sigma : ℝ))⁻¹ • matVecMul (freshShellCubeAverage R omega n m)
                  (e' + cubeAverageVec R
                    (fun x => (wD omega).toH1Function.grad x))) := by
  classical
  set a : Vec d := e' + cubeAverageVec R (fun x => (wD omega).toH1Function.grad x)
    with ha
  set b : Vec d := e + cubeAverageVec R (neumannFluxField sigma omega n m e' (wN omega))
    with hb
  set H : Mat d := freshShellCubeAverage R omega n m with hH
  have hs0 : (0 : ℝ) < Real.sqrt (sigma : ℝ) := Real.sqrt_pos.2 sigma.2
  have hs : Real.sqrt (sigma : ℝ) * Real.sqrt (sigma : ℝ) = (sigma : ℝ) :=
    Real.mul_self_sqrt sigma.2.le
  have hP : principalPz sigma omega n m e e' R (wD omega) (wN omega)
      = (inverseSqrtLoad sigma a, sqrtLoad sigma b) := by
    refine Prod.ext ?_ ?_
    · exact principalPz_fst sigma omega n m e e' R (wD omega) (wN omega)
    · exact principalPz_snd sigma omega n m e e' R (wD omega) (wN omega)
  have hload : gaugedPrincipalLoadShell sigma R n m e e' wD wN omega
      = (inverseSqrtLoad sigma a,
          matVecMul (-H) (inverseSqrtLoad sigma a) + sqrtLoad sigma b) := by
    rw [gaugedPrincipalLoadShell, hP, blockMatVecMul_blockGauge]
  have hX2 : matVecMul (-H) (inverseSqrtLoad sigma a) + sqrtLoad sigma b
      = Real.sqrt (sigma : ℝ) • (b - ((sigma : ℝ))⁻¹ • matVecMul H a) := by
    rw [inverseSqrtLoad, sqrtLoad, neg_matVecMul, matVecMul_smul, smul_sub, smul_smul]
    have hcoef : Real.sqrt (sigma : ℝ) * ((sigma : ℝ))⁻¹
        = (Real.sqrt (sigma : ℝ))⁻¹ := by
      refine (inv_eq_of_mul_eq_one_right ?_).symm
      calc Real.sqrt (sigma : ℝ) * (Real.sqrt (sigma : ℝ) * ((sigma : ℝ))⁻¹)
          = (Real.sqrt (sigma : ℝ) * Real.sqrt (sigma : ℝ)) * ((sigma : ℝ))⁻¹ := by
            ring
        _ = (sigma : ℝ) * ((sigma : ℝ))⁻¹ := by rw [hs]
        _ = 1 := mul_inv_cancel₀ (ne_of_gt sigma.2)
    rw [hcoef]
    abel
  rw [hload, hX2, blockVecDot_blockMatVecMul_blockDiag_smul_one]
  have hfst : ((inverseSqrtLoad sigma a,
      Real.sqrt (sigma : ℝ) • (b - ((sigma : ℝ))⁻¹ • matVecMul H a)) :
        BlockVec d).1 = inverseSqrtLoad sigma a := rfl
  have hsnd : ((inverseSqrtLoad sigma a,
      Real.sqrt (sigma : ℝ) • (b - ((sigma : ℝ))⁻¹ • matVecMul H a)) :
        BlockVec d).2
      = Real.sqrt (sigma : ℝ) • (b - ((sigma : ℝ))⁻¹ • matVecMul H a) := rfl
  rw [hfst, hsnd, inverseSqrtLoad, vecNormSq_smul, vecNormSq_smul]
  have hsq : (Real.sqrt (sigma : ℝ))⁻¹ ^ 2 = ((sigma : ℝ))⁻¹ := by
    rw [inv_pow]
    congr 1
    rw [sq]
    exact hs
  have hsq' : (Real.sqrt (sigma : ℝ)) ^ 2 = (sigma : ℝ) := by
    rw [sq]; exact hs
  rw [hsq, hsq']
  have hne : ((sigma : ℝ)) ≠ 0 := ne_of_gt sigma.2
  field_simp

/-- At the zero flux direction the flux leg field of `e.Pz.def` is the bare
Neumann corrector gradient: the fresh-shell term `shom^{-1} h e'` vanishes with
its direction. -/
theorem neumannFluxField_zero_direction (sigma : PositiveScalar)
    (omega : Cutoff.ShellSeq d) (n m : ℤ) {Q : TriadicCube d}
    (wN : H1MeanZeroFunction (openCubeSet Q)) :
    neumannFluxField sigma omega n m (0 : Vec d) wN
      = fun x => wN.toH1Function.grad x := by
  funext x
  change wN.toH1Function.grad x
      + Corrector.streamForcing ((sigma : ℝ))⁻¹ omega n m (0 : Vec d) x = _
  rw [Corrector.streamForcing_zero_direction]
  exact add_zero _

/-- **The collapse at the Step-5 branch `e' = 0`.**

Still unconditional.  A consumer carrying the Neumann weak-solution binder of
`e.def.w` kills the remaining `(grad w_N)_R` by
`FreshShellSumZeroDirection.grad_ae_eq_zero_of_isMeanZeroNeumannRhsWeakSolution_streamForcing_zero`,
leaving the manuscript's `|(grad w_D)_R|^2 + |e - shom^{-1} (h)_R (grad w_D)_R|^2`. -/
theorem blockVecDot_gaugedPrincipalLoadShell_blockDiag_flux (sigma : PositiveScalar)
    {Q : TriadicCube d} (R : TriadicCube d) (n m : ℤ) (e : Vec d)
    (wD : Cutoff.ShellSeq d → H10Function (openCubeSet Q))
    (wN : Cutoff.ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (omega : Cutoff.ShellSeq d) :
    blockVecDot (gaugedPrincipalLoadShell sigma R n m e 0 wD wN omega)
        (blockMatVecMul
          (Ch02.blockDiag ((sigma : ℝ) • (1 : Mat d)) (((sigma : ℝ))⁻¹ • (1 : Mat d)))
          (gaugedPrincipalLoadShell sigma R n m e 0 wD wN omega))
      = vecNormSq (cubeAverageVec R (fun x => (wD omega).toH1Function.grad x))
        + vecNormSq
            ((e + cubeAverageVec R (fun x => (wN omega).toH1Function.grad x))
              - ((sigma : ℝ))⁻¹ • matVecMul (freshShellCubeAverage R omega n m)
                  (cubeAverageVec R
                    (fun x => (wD omega).toH1Function.grad x))) := by
  rw [blockVecDot_gaugedPrincipalLoadShell_blockDiag sigma R n m e 0 wD wN omega,
    neumannFluxField_zero_direction sigma omega n m (wN omega), zero_add]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
