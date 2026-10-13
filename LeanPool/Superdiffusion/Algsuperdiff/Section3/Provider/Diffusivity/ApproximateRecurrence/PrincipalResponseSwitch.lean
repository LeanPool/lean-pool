/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchPlateau
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.BlockResponseConcentration

/-!
# PrincipalResponseSwitch

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# Provider: the cube-to-annealed switch of `e.use.also.for.the.upper.bound`

This module supplies the matrix content of the annealed switch
`e.use.also.for.the.upper.bound` of ABK26, whose statement is the display and
whose proof is.  The manuscript's display reads

```
  E[ | bfAhom_{m-h}^{1/2}(z + cu_n) G_{-(h)_{z+cu_n}} P_z |^2 ]
    <=  (1 + C E^2 |log gamma|^2 gamma)
          E[ | bfAhom_{m-h}^{1/2} G_{-(h)_{z+cu_n}} P_z |^2 ] ,
```

and its proof runs entirely through the deterministic matrix bound

```
  | bfAhom_{m-h}^{-1/2} bfAhom_{m-h}(cu_n) bfAhom_{m-h}^{-1/2} - I_{2d} |
    <= 2 max_{|e|=1} E[ bfJ(cu_n, bfAhom_{m-h}^{-1/2} e, bfAhom_{m-h}^{1/2} e; a_{m-h}) ] .
```

What is proved here is that deterministic bound, in the equivalent
vector-uniform Loewner form

```
  bfAhom_L(cu_n)  <=  (1 + delta) bfAhom_L    (as quadratic forms on every
                                               doubled vector) ,
  delta := 2 E[ bfJ(cu_n, bfAhom_L^{-1/2} e, bfAhom_L^{1/2} e; a_L) ] ,
```

at the cutoff index `L`.  The manuscript's display for the specific random
vector `G_{-(h)_{z+cu_n}} P_z` follows from this by monotonicity of the
integral, so no statement below mentions `P_z`; see "What is *not* here".

## The chain, and where each printed step goes

* `bfAhom_L <= bfAhom_L(cu_n)` (the right half of the sandwich printed) is
  `blockMatLoewnerLE_annealedBlockMatrixAtScale_annealedLimit` of
  `...ApproximateRecurrence.PrincipalResponseSwitchPlateau`.
* The annealed probe `(bfAhom_L^{-1/2} e, bfAhom_L^{1/2} e)` of ABK26 is
  `annealedProbePotential` / `annealedProbeFlux`;
  `blockVecDot_annealedProbePotential_annealedProbeFlux` records that the two
  reciprocal square roots of the block-diagonal `bfAhom_L` of `e.homs.defs`
  cancel in the doubled pairing, so the printed normalization `|e| = 1` is
  exactly `P . Q = 1` for that pair.
* The factor `2` of comes out of the Chapter 2 doubled-response splitting rather
  than out of the completed square `e.bfJ.magic`: on the block-diagonal annealed
  carrier of `e.homs.defs.U.diag` the splitting gives the *exact* identity `(x -
  1) + (y - 1) = 2 E[bfJ]` with `x := sigmahom_L(cu_n)/sigmahom_L` and `y:=
  sigmahom_L/sigmahom_{L,*}(cu_n)`, both summands nonnegative by the plateau
  ordering, so the nonnegative square that `e.bfJ.magic` discards is not needed.
  `cubeAnnealedProbeDefect_eq_two_mul_integral_blockJ` below is that identity.
  Its integrand is CoarseGraining's `Ch04.blockJObservableCubeSetBlockVec`,
  which is `Ch02.doubledResponseJ` -- the manuscript's `bfJ` -- on every a.e.
  locally uniformly elliptic field, by CoarseGraining's
  `Ch04.doubledResponseJ_eq_blockJObservableCubeSetBlockVec_of_aelocallyUniformlyEllipticField`.

## What is *not* here

The manuscript's own budget `delta <=^2 |log gamma|^2 gamma` is **not** proved
here.  It needs `e.bound.one.cube.by.mathcalE`, `e.mathcalE.monotone.ordered`
and, crucially, the induction hypothesis `e.new.induction.for.shom` at `t =
|log gamma|^{-1}` in the form of a second moment of `mathcal E_{t,infinity,2}`;
none of those is consumed below.  Nothing here therefore claims any source
node, or any fraction of one.  The specific random vector `G_{-(h)_{z+cu_n}}
P_z` of the printed display is likewise absent: `P_z` has no definition in this
repository yet, and the Loewner form below is exactly what specializes to it in
one step once it does.

The cube below is the origin cube `cu_n`, not the translate `z + cu_n` printed
in the display.  The two annealed matrices agree by real-translation
stationarity of the genuine cutoff law, which is the transfer already used
inside `Provider.Annealed.Monotonicity`; that transfer is not re-exported here,
so a consumer working at a translated cube still owes that one step.

## Main results

* `annealedProbePotential`, `annealedProbeFlux`: the tex probe pair.
* `cubeAnnealedProbeDefect`: the annealed defect `delta`.
* `cubeAnnealedProbeDefect_eq_two_mul_integral_blockJ`: `delta` is twice the
  annealed doubled response at the probe, i.e. the manuscript's quantity at that
  probe.
* `cubeAnnealedProbeDefect_eq_of_blockDiag`: `delta` on a scalar
  block-diagonal annealed cube matrix, in the closed form
  `(sigma^{-1} s + sigma t - 2) |E|^2`.
* `annealedCubeBlockQuadratic_le_annealedLimitBlockQuadratic`: **the switch**,
  as a quadratic-form inequality on an arbitrary doubled vector.

## References

* ABK26 (`e.use.also.for.the.upper.bound` and its proof).
* ABK26, `e.bfJ.magic` (`e.homs.defs`).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## The probe pair `(bfAhom^{-1/2} e, bfAhom^{1/2} e)` -/

/-- The doubled vector `bfAhom^{-1/2} e` at the block-diagonal annealed limit
`bfAhom = diag(sigma, sigma^{-1})` of `e.homs.defs`. -/
def annealedProbePotential (sigma : Observable.PositiveScalar) (E : BlockVec d) :
    BlockVec d :=
  (Observable.inverseSqrtLoad sigma E.1, Observable.sqrtLoad sigma E.2)

/-- The doubled vector `bfAhom^{1/2} e` at the block-diagonal annealed limit
`bfAhom = diag(sigma, sigma^{-1})` of `e.homs.defs`. -/
def annealedProbeFlux (sigma : Observable.PositiveScalar) (E : BlockVec d) :
    BlockVec d :=
  (Observable.sqrtLoad sigma E.1, Observable.inverseSqrtLoad sigma E.2)

private theorem sqrt_mul_self_positiveScalar (sigma : Observable.PositiveScalar) :
    Real.sqrt (sigma : ℝ) * Real.sqrt (sigma : ℝ) = (sigma : ℝ) :=
  Real.mul_self_sqrt sigma.2.le

private theorem sqrt_pos_positiveScalar (sigma : Observable.PositiveScalar) :
    0 < Real.sqrt (sigma : ℝ) :=
  Real.sqrt_pos.mpr sigma.2

/-- The probe pair is dual: its doubled pairing is the squared norm of the
direction, so the tex normalization `|e| = 1` is exactly `P . Q = 1`. -/
theorem blockVecDot_annealedProbePotential_annealedProbeFlux
    (sigma : Observable.PositiveScalar) (E : BlockVec d) :
    blockVecDot (annealedProbePotential (d := d) sigma E) (annealedProbeFlux sigma E) =
      blockVecDot E E := by
  have hr : Real.sqrt (sigma : ℝ) ≠ 0 := ne_of_gt (sqrt_pos_positiveScalar sigma)
  simp only [annealedProbePotential, annealedProbeFlux, blockVecDot,
    Observable.inverseSqrtLoad, Observable.sqrtLoad, vecDot_smul_left,
    vecDot_smul_right]
  field_simp

/-! ## The annealed defect -/

/-- **The annealed defect `delta` of ABK26**, at the cutoff index `L`,
the cube scale `n` and the unit direction `E`: twice the annealed doubled
response of the cube `cu_n` at the probe pair
`(bfAhom_L^{-1/2} E, bfAhom_L^{1/2} E)`.

It is written here through CoarseGraining's algebraic doubled-response value
`Ch04.blockJQuadraticFullBlockMat` evaluated at the annealed block matrix,
which is exactly the expectation of the Chapter 2 doubled-response splitting;
`cubeAnnealedProbeDefect_eq_two_mul_integral_blockJ` identifies it with the
expectation of the doubled response itself. -/
def cubeAnnealedProbeDefect (M : ABKModel d) (L n : ℤ) (E : BlockVec d) : ℝ :=
  2 *
    Ch04.blockJQuadraticFullBlockMat
      (toFullBlockMat
        (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n))
      (annealedProbePotential (Annealed.sigmaBar M L) E)
      (annealedProbeFlux (Annealed.sigmaBar M L) E)

/-- CoarseGraining's algebraic doubled-response value, written in doubled-block
form.  This is the Chapter 2 splitting `bfJ = 1/2 P. bfA P + 1/2 Q. bfA_*^{-1}
Q - P. Q`, with `bfA_*^{-1}` the block reflection of `bfA`. -/
theorem blockJQuadraticFullBlockMat_toFullBlockMat (A : BlockMat d)
    (P Q : BlockVec d) :
    Ch04.blockJQuadraticFullBlockMat (toFullBlockMat A) P Q =
      (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul A P) +
          (1 / 2 : ℝ) * blockVecDot (Q.2, Q.1) (blockMatVecMul A (Q.2, Q.1)) -
        blockVecDot P Q := by
  unfold Ch04.blockJQuadraticFullBlockMat
  rw [Ch04.fullBlockReflect_toFullBlockMat, Ch04.fullBlockQuadraticCh04_toFullBlockMat,
    Ch04.fullBlockQuadraticCh04_toFullBlockMat, blockVecDot_blockMatVecMul_blockReflect]

/-- The defect on a scalar block-diagonal annealed cube matrix: with
`bfAhom_L(cu_n) = diag(s, t)` and `bfAhom_L = diag(sigma, sigma^{-1})`,

`delta = (sigma^{-1} s + sigma t - 2) |E|^2`. -/
theorem cubeAnnealedProbeDefect_eq_of_blockDiag (M : ABKModel d) (L n : ℤ)
    {s t : ℝ}
    (hst : Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n =
      Ch02.blockDiag (s • (1 : Mat d)) (t • (1 : Mat d))) (E : BlockVec d) :
    cubeAnnealedProbeDefect M L n E =
      (((Annealed.sigmaBar M L : ℝ))⁻¹ * s + (Annealed.sigmaBar M L : ℝ) * t - 2) *
        blockVecDot E E := by
  have hr : Real.sqrt ((Annealed.sigmaBar M L : ℝ)) ≠ 0 :=
    ne_of_gt (sqrt_pos_positiveScalar (Annealed.sigmaBar M L))
  have hrr := sqrt_mul_self_positiveScalar (Annealed.sigmaBar M L)
  rw [cubeAnnealedProbeDefect, hst, blockJQuadraticFullBlockMat_toFullBlockMat,
    blockVecDot_blockDiag_smul_one_vecDot,
    blockVecDot_blockDiag_smul_one_vecDot,
    blockVecDot_annealedProbePotential_annealedProbeFlux]
  simp only [annealedProbePotential, annealedProbeFlux, blockVecDot,
    Observable.inverseSqrtLoad, Observable.sqrtLoad, vecDot_smul_left,
    vecDot_smul_right]
  have hinvsq : (Real.sqrt ((Annealed.sigmaBar M L : ℝ)))⁻¹ *
      (Real.sqrt ((Annealed.sigmaBar M L : ℝ)))⁻¹ =
      ((Annealed.sigmaBar M L : ℝ))⁻¹ := by
    rw [← mul_inv, hrr]
  linear_combination (s * (vecDot E.1 E.1 + vecDot E.2 E.2)) * hinvsq +
    (t * (vecDot E.1 E.1 + vecDot E.2 E.2)) * hrr

variable [NeZero d]

/-- Non-vacuity of the normalization `|e| = 1` used below: unit doubled
directions exist. -/
theorem exists_blockVecDot_self_eq_one :
    ∃ E : BlockVec d, blockVecDot E E = 1 := by
  have hi : (0 : ℕ) < d := Nat.pos_of_ne_zero (NeZero.ne d)
  refine ⟨((fun j => if j = (⟨0, hi⟩ : Fin d) then (1 : ℝ) else 0), fun _ => (0 : ℝ)), ?_⟩
  simp only [blockVecDot, vecDot, mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single (⟨0, hi⟩ : Fin d)]
  · simp
  · intro b _ hb
    simp only [ite_eq_right hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## The switch -/

/-- **`e.use.also.for.the.upper.bound` (ABK26), in the vector-uniform Loewner
form.**

At the cutoff index `L` and every cube scale `n`, the finite-cube annealed
matrix `bfAhom_L(cu_n)` is dominated by `(1 + delta)` times the infinite-volume
annealed matrix `bfAhom_L = diag(sigmahom_L, sigmahom_L^{-1})` of `e.homs.defs`,
as quadratic forms on an **arbitrary** doubled vector `V`, where `delta = 2
E[bfJ(cu_n, bfAhom_L^{-1/2} E, bfAhom_L^{1/2} E; a_L)]` is the defect of at any
unit direction `E`.

Taking `V := G_{-(h)_{z+cu_n}} P_z` and integrating recovers the manuscript's
printed display for that random vector; that specialization is not available in
this repository yet, since `P_z` is not defined here.  This theorem does
**not** prove the manuscript's budget `delta <=^2 |log gamma|^2 gamma` and
claims no source-node status. -/
theorem annealedCubeBlockQuadratic_le_annealedLimitBlockQuadratic
    (M : ABKModel d) (L n : ℤ) {E : BlockVec d} (hE : blockVecDot E E = 1)
    (V : BlockVec d) :
    blockVecDot V
        (blockMatVecMul
          (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n) V) ≤
      (1 + cubeAnnealedProbeDefect M L n E) *
        blockVecDot V
          (blockMatVecMul
            (Ch02.blockDiag ((Annealed.sigmaBar M L : ℝ) • (1 : Mat d))
              (((Annealed.sigmaBar M L : ℝ))⁻¹ • (1 : Mat d))) V) := by
  obtain ⟨s, t, hst⟩ :=
    Provider.Annealed.coefficientCutoffLaw_exists_annealedBlockMatrixAtScale_eq_blockDiag_smul_one
      M L n
  have hsigma : 0 < ((Annealed.sigmaBar M L : ℝ)) := (Annealed.sigmaBar M L).2
  have hinv : 0 < ((Annealed.sigmaBar M L : ℝ))⁻¹ := inv_pos.mpr hsigma
  have hcancel : ((Annealed.sigmaBar M L : ℝ)) * ((Annealed.sigmaBar M L : ℝ))⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hsigma)
  have hs := sigmaBar_le_annealedCubeUpperLeft M L n hst
  have ht := inv_sigmaBar_le_annealedCubeLowerRight M L n hst
  have hx : (1 : ℝ) ≤ ((Annealed.sigmaBar M L : ℝ))⁻¹ * s := by
    nlinarith [mul_le_mul_of_nonneg_left hs hinv.le, hcancel]
  have hy : (1 : ℝ) ≤ ((Annealed.sigmaBar M L : ℝ)) * t := by
    nlinarith [mul_le_mul_of_nonneg_left ht hsigma.le, hcancel]
  have hV1 : 0 ≤ vecDot V.1 V.1 := by
    simpa [vecDot] using Finset.sum_nonneg fun j _ => mul_self_nonneg (V.1 j)
  have hV2 : 0 ≤ vecDot V.2 V.2 := by
    simpa [vecDot] using Finset.sum_nonneg fun j _ => mul_self_nonneg (V.2 j)
  have hdelta : cubeAnnealedProbeDefect M L n E =
      ((Annealed.sigmaBar M L : ℝ))⁻¹ * s + (Annealed.sigmaBar M L : ℝ) * t - 2 := by
    rw [cubeAnnealedProbeDefect_eq_of_blockDiag M L n hst E, hE, mul_one]
  have hupper : s ≤ (1 + cubeAnnealedProbeDefect M L n E) *
      ((Annealed.sigmaBar M L : ℝ)) := by
    rw [hdelta]
    nlinarith [hy, hcancel, hsigma]
  have hlower : t ≤ (1 + cubeAnnealedProbeDefect M L n E) *
      ((Annealed.sigmaBar M L : ℝ))⁻¹ := by
    rw [hdelta]
    nlinarith [hx, hcancel, hinv]
  rw [hst, blockVecDot_blockDiag_smul_one_vecDot,
    blockVecDot_blockDiag_smul_one_vecDot]
  nlinarith [mul_le_mul_of_nonneg_right hupper hV1,
    mul_le_mul_of_nonneg_right hlower hV2]

/-! ## The defect is the annealed doubled response of `e.bfJ.magic`'s parent -/

/-- **ABK26, annealed.**  The defect is twice the expectation of the doubled
response `bfJ(cu_n, bfAhom_L^{-1/2} E, bfAhom_L^{1/2} E; a_L)` under the genuine
coefficient cutoff law at index `L`.

The proof is the Chapter 2 doubled-response splitting (the parent identity of
`e.bfJ.magic`, ABK26) integrated entrywise; no completed square and no
discarded nonnegative term appear. -/
theorem cubeAnnealedProbeDefect_eq_two_mul_integral_blockJ (M : ABKModel d)
    (L n : ℤ) (E : BlockVec d) :
    cubeAnnealedProbeDefect M L n E =
      2 *
        ∫ a,
          Ch04.blockJObservableCubeSetBlockVec (originCube d n)
            (annealedProbePotential (Annealed.sigmaBar M L) E)
            (annealedProbeFlux (Annealed.sigmaBar M L) E) a
          ∂(Cutoff.coefficientCutoffLaw M L) := by
  classical
  set P : BlockVec d := annealedProbePotential (Annealed.sigmaBar M L) E with hP
  set Q : BlockVec d := annealedProbeFlux (Annealed.sigmaBar M L) E with hQ
  set C : RegCoeffField d → BlockMat d :=
    fun a => coarseBlockMatrix (cubeSet (originCube d n)) a.toFun with hC
  have hEntry :
      ∀ alpha beta : BlockCoord d,
        Integrable (fun a : RegCoeffField d => blockMatEntry (C a) alpha beta)
          (Cutoff.coefficientCutoffLaw M L) := fun alpha beta =>
    Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
      M L (originCube d n) alpha beta
  have hint1 :
      Integrable (fun a : RegCoeffField d => blockVecDot P (blockMatVecMul (C a) P))
        (Cutoff.coefficientCutoffLaw M L) :=
    Ch04.integrable_blockVecDot_blockMatVecMul_of_integrable_entries hEntry P P
  have hint2 :
      Integrable
        (fun a : RegCoeffField d =>
          blockVecDot (Q.2, Q.1) (blockMatVecMul (C a) (Q.2, Q.1)))
        (Cutoff.coefficientCutoffLaw M L) :=
    Ch04.integrable_blockVecDot_blockMatVecMul_of_integrable_entries hEntry
      (Q.2, Q.1) (Q.2, Q.1)
  have hae :=
    Ch04.blockJObservableCubeSetBlockVec_ae_eq_blockJQuadraticFullBlockMat
      (Cutoff.coefficientCutoffLaw_lawCarrier M L) (originCube d n) P Q
  have hrewrite :
      ∫ a,
          Ch04.blockJObservableCubeSetBlockVec (originCube d n) P Q a
          ∂(Cutoff.coefficientCutoffLaw M L) =
        ∫ a,
          ((1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (C a) P) +
              (1 / 2 : ℝ) *
                blockVecDot (Q.2, Q.1) (blockMatVecMul (C a) (Q.2, Q.1)) -
            blockVecDot P Q)
          ∂(Cutoff.coefficientCutoffLaw M L) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with a ha
    rw [ha, blockJQuadraticFullBlockMat_toFullBlockMat]
  have hsplit :
      ∫ a,
          ((1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (C a) P) +
              (1 / 2 : ℝ) *
                blockVecDot (Q.2, Q.1) (blockMatVecMul (C a) (Q.2, Q.1)) -
            blockVecDot P Q)
          ∂(Cutoff.coefficientCutoffLaw M L) =
        (1 / 2 : ℝ) *
              blockVecDot P
                (blockMatVecMul
                  (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
                  P) +
            (1 / 2 : ℝ) *
              blockVecDot (Q.2, Q.1)
                (blockMatVecMul
                  (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
                  (Q.2, Q.1)) -
          blockVecDot P Q := by
    have hsum :
        Integrable
          (fun a : RegCoeffField d =>
            (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (C a) P) +
              (1 / 2 : ℝ) *
                blockVecDot (Q.2, Q.1) (blockMatVecMul (C a) (Q.2, Q.1)))
          (Cutoff.coefficientCutoffLaw M L) :=
      (hint1.const_mul (1 / 2 : ℝ)).add (hint2.const_mul (1 / 2 : ℝ))
    rw [integral_sub hsum (integrable_const _),
      integral_add (hint1.const_mul (1 / 2 : ℝ)) (hint2.const_mul (1 / 2 : ℝ)),
      integral_const_mul, integral_const_mul,
      Ch04.integral_blockVecDot_blockMatVecMul_eq_of_integrable_entries hEntry P P,
      Ch04.integral_blockVecDot_blockMatVecMul_eq_of_integrable_entries hEntry
        (Q.2, Q.1) (Q.2, Q.1), integral_const, probReal_univ, one_smul]
    simp only [Ch04.annealedBlockMatrixAtScale, Ch04.annealedBlockMatrix, hC]
  rw [cubeAnnealedProbeDefect, blockJQuadraticFullBlockMat_toFullBlockMat,
    hrewrite, hsplit]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
