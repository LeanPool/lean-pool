/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponsePSqrt

/-!
# PrincipalResponsePDef

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the principal load `P` of `e.recurrence.P.def`, and why it collapses

Source displays in ABK26:

* `e.recurrence.P.def` (label; display) sets, for `e, e'` in `R^d` with `|e|,
  |e'| <= 1`,

  ```
  P := bfAhom_{m-h}^{-1/2} (e'; e)   in R^{2d} .
  ```

  The manuscript's column has `e'` on the potential leg and `e` on the flux leg;
  that order is preserved below.
* Step 6 of the proof of `l.approximate.recurrence.formula` opens with the
  identity

  ```
  (e'; e) . bfAhom_{m-h}^{-1/2} bfAhom_m bfAhom_{m-h}^{-1/2} (e'; e)
      = P . bfAhom_m P ,
  ```

  then splits into the two cases `e = 0` and `e' = 0`.  The reason the whole
  construction is set up this way is that with `bfAhom_k = ((shom_k, 0), (0,
  shom_k^{-1}))` the conjugated matrix is again a scalar block diagonal, with
  entries `shom_m / shom_{m-h}` and its reciprocal; the two cases read off one
  entry each.  That collapse is proved here.

## What is *not* fixed here

The manuscript's localization scale is `n = m - h - 16 ceil |log_3 gamma|`
(`e.recurrence.params`, display, label).  Nothing in this module mentions a
localization scale, so the literal `16` appears nowhere and the buffer stays a
free parameter for the modules that need it.

## Main results

* `principalLoad`, `recurrenceP`
* `recurrenceP_eq`, `recurrenceP_fst`, `recurrenceP_snd`
* `blockVecDot_recurrenceP_annealedLimitBlock`
* `blockVecDot_recurrenceP_annealedLimitBlock_potential_unit` and
  `..._flux_unit`, the two unit cases, returning the reciprocal diffusivity
  ratios `shom_m / shom_{m-h}` and `shom_{m-h} / shom_m`
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## The normalization map -/

/-- The action of `bfAhom^{-1/2}` on a doubled load.  This is the operation applied
in `e.recurrence.P.def`, in `e.Pz.def` and in `e.Fz.def`. -/
def principalLoad (sigma : PositiveScalar) (X : BlockVec d) : BlockVec d :=
  blockMatVecMul (annealedLimitBlockInvSqrt sigma) X

/-- The two legs of the normalization: `sigma^{-1/2}` on the potential leg and
`sigma^{1/2}` on the flux leg. -/
theorem principalLoad_eq (sigma : PositiveScalar) (X : BlockVec d) :
    principalLoad sigma X = (inverseSqrtLoad sigma X.1, sqrtLoad sigma X.2) := by
  rw [principalLoad, ← Prod.mk.eta (p := X),
    blockMatVecMul_annealedLimitBlockInvSqrt]

@[simp] theorem principalLoad_fst (sigma : PositiveScalar) (X : BlockVec d) :
    (principalLoad sigma X).1 = inverseSqrtLoad sigma X.1 := by
  rw [principalLoad_eq]

@[simp] theorem principalLoad_snd (sigma : PositiveScalar) (X : BlockVec d) :
    (principalLoad sigma X).2 = sqrtLoad sigma X.2 := by
  rw [principalLoad_eq]

/-- The normalization is additive. -/
theorem principalLoad_add (sigma : PositiveScalar) (X Y : BlockVec d) :
    principalLoad sigma (X + Y) = principalLoad sigma X + principalLoad sigma Y := by
  rw [principalLoad, principalLoad, principalLoad, blockMatVecMul_add]

/-! ## The load `P` of `e.recurrence.P.def` -/

/-- **`e.recurrence.P.def`.**  The probe load `P = bfAhom_{m-h}^{-1/2} (e'; e)`,
at the positive scalar `sigma = shom_{m-h}`.

The manuscript's constraint `|e|, |e'| <= 1` is a constraint on the *use* of
`P` in the estimates downstream, not part of the display defining it, and is
therefore not a binder here. -/
def recurrenceP (sigma : PositiveScalar) (e e' : Vec d) : BlockVec d :=
  principalLoad sigma (e', e)

/-- The two legs of `P`. -/
theorem recurrenceP_eq (sigma : PositiveScalar) (e e' : Vec d) :
    recurrenceP sigma e e' = (inverseSqrtLoad sigma e', sqrtLoad sigma e) := by
  rw [recurrenceP, principalLoad_eq]

@[simp] theorem recurrenceP_fst (sigma : PositiveScalar) (e e' : Vec d) :
    (recurrenceP sigma e e').1 = inverseSqrtLoad sigma e' := by
  rw [recurrenceP_eq]

@[simp] theorem recurrenceP_snd (sigma : PositiveScalar) (e e' : Vec d) :
    (recurrenceP sigma e e').2 = sqrtLoad sigma e := by
  rw [recurrenceP_eq]

/-! ## The collapse -/

private theorem vecNormSq_inverseSqrtLoad (sigma : PositiveScalar) (x : Vec d) :
    vecNormSq (inverseSqrtLoad sigma x) = (sigma : ℝ)⁻¹ * vecNormSq x := by
  rw [inverseSqrtLoad, vecNormSq_smul, ← Real.sqrt_inv, Real.sq_sqrt
    (inv_pos.2 sigma.2).le]

private theorem vecNormSq_sqrtLoad (sigma : PositiveScalar) (x : Vec d) :
    vecNormSq (sqrtLoad sigma x) = (sigma : ℝ) * vecNormSq x := by
  rw [sqrtLoad, vecNormSq_smul, Real.sq_sqrt sigma.2.le]

/-- **, right-hand reading.**  The doubled quadratic form of `bfAhom_m` at the
probe load `P = bfAhom_{m-h}^{-1/2}(e'; e)` collapses to two scalar terms with
the reciprocal coefficients `shom_m / shom_{m-h}` and `shom_{m-h} / shom_m`. -/
theorem blockVecDot_recurrenceP_annealedLimitBlock
    (sigmaTop sigmaLow : PositiveScalar) (e e' : Vec d) :
    blockVecDot (recurrenceP (d := d) sigmaLow e e')
        (blockMatVecMul (annealedLimitBlock (d := d) sigmaTop)
          (recurrenceP (d := d) sigmaLow e e')) =
      ((sigmaTop : ℝ) / (sigmaLow : ℝ)) * vecNormSq e' +
        ((sigmaLow : ℝ) / (sigmaTop : ℝ)) * vecNormSq e := by
  rw [annealedLimitBlock, blockVecDot_blockMatVecMul_blockDiag_smul_one,
    recurrenceP_fst, recurrenceP_snd, vecNormSq_inverseSqrtLoad,
    vecNormSq_sqrtLoad]
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, ← mul_assoc]
  congr 2
  rw [mul_comm]

/-- **, the case `e = 0`.**  Probing with a unit potential direction returns
exactly the diffusivity ratio `shom_m / shom_{m-h}`. -/
theorem blockVecDot_recurrenceP_annealedLimitBlock_potential_unit
    (sigmaTop sigmaLow : PositiveScalar) {e' : Vec d} (he' : vecNormSq e' = 1) :
    blockVecDot (recurrenceP (d := d) sigmaLow 0 e')
        (blockMatVecMul (annealedLimitBlock (d := d) sigmaTop)
          (recurrenceP (d := d) sigmaLow 0 e')) =
      (sigmaTop : ℝ) / (sigmaLow : ℝ) := by
  rw [blockVecDot_recurrenceP_annealedLimitBlock, he']
  simp [vecNormSq, vecDot]

/-- **, the case `e' = 0`.**  Probing with a unit flux direction returns the
reciprocal ratio `shom_{m-h} / shom_m`. -/
theorem blockVecDot_recurrenceP_annealedLimitBlock_flux_unit
    (sigmaTop sigmaLow : PositiveScalar) {e : Vec d} (he : vecNormSq e = 1) :
    blockVecDot (recurrenceP (d := d) sigmaLow e 0)
        (blockMatVecMul (annealedLimitBlock (d := d) sigmaTop)
          (recurrenceP (d := d) sigmaLow e 0)) =
      (sigmaLow : ℝ) / (sigmaTop : ℝ) := by
  rw [blockVecDot_recurrenceP_annealedLimitBlock, he]
  simp [vecNormSq, vecDot]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
