/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineExpectation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.VarianceClosure
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.StarredFluctuationIntegrable
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4UpperMoments

/-!
# InitialJLBoundIntegrability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `(e.initial.JL.bound)`, Parts A and B: envelopes and global integrability

ABK26 (the display `e.initial.JL.bound`) and its proof.

## Content part carried by this file

This module is the **first of the two files** into which the Step-1 assembly of
the corrected combine is split.  It carries Parts A and B: the *unconditional*
descendant envelope of the `sigma_*^{-1}kappa` channel, the pointwise envelopes
of the two deterministic blocks of the good-event display, their global
integrability at the genuine cutoff sample law, and the resulting discharge of
the two `IntegrableOn` binders of the proved `CombineExpectation` endpoints.
This is item (4) of the depgraph record and item (i).

Part C --- the corridor summation, the anchor wiring, the absorption and the
assembly into the printed display --- is in
`Provider/Homogenization/InitialJLBound.lean`, which imports this file.

## Part A: the unconditional envelope and the two global integrabilities

`VarianceClosure.lean` produces the `sigma_*^{-1}kappa` descendant envelope only
*on the good event*, at the cost of a geometric weight, because it routes the
upper-left block through the `Lambda^2` extraction.  The route taken here is the
other one: the **unconditional** chain

* `Cutoff.maxDescendantBMatrixNormCoeffFieldAtScale_le_cutoffEnvelope` (the
  ambient form of `Cutoff.maxDescendantBMatrixNormAtScale_le_cutoffEnvelope`),
  depth-uniform, no event, no weight, read on the `coarseBlockMatrix` carrier
  through the public CoarseGraining `Ch05.Section52` sup identity
  `maxDescendantBMatrixNormCoeffFieldAtScale_eq_sup_upperLeft_of_aelocallyUniformlyEllipticField`.
  That reading is **not performed here**: it is the proved sibling public
  `matrixOperatorNorm_coarseBlockMatrix_upperLeft_le_cutoffEnvelope`
  (`Provider/Homogenization/StarredFluctuationIntegrable.lean`), which this file
  imports and consumes;
* the sharp positive semidefinite off-diagonal bound
  `matrixOperatorNorm_lowerLeft_le_sqrt_of_isSymmetricBlockMat_of_blockPosDef`
  (`VarianceClosure.lean`, public 13), whose `hSymm`/`hPos` come from the public
  CoarseGraining
  `coarseBlockMatrix_cubeSet_symm_of_aelocallyUniformlyEllipticField` and
  `coarseBlockMatrix_cubeSet_blockPosDef_of_aelocallyUniformlyEllipticField`,
  exactly as in `VarianceClosure.lean`;
* the deterministic lower-right envelope
  `matrixOperatorNorm_coarseBlockMatrix_lowerRight_le_of_mem_descendantsAtScale`
  (`VarianceClosure.lean`, public 9),

which gives, for every descendant `R` of every cube `Q` at every depth and for
**every** sample,

`|(sigma_*^{-1}kappa)(R;omega)| <= 4 d nu^{-1} E(omega)`,
`E := Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q`.

Since every natural power of `E` is integrable at `(Cutoff.cutoffSampleLaw
M).toMeasure` (`Cutoff.integrable_coefficientCutoffCubeEllipticityUpper_pow`),
the two `CombineExpectation` block carriers `coarseMatrixVariationBlock` and
`coarseScaleSeparationBlock` are **globally** integrable at that measure, with
no event and no hypothesis beyond the standing model data.  The corridor weight
`3^{-(m-n)}` is at most `1` on `[L,m]` and the corridor is finite, so the
second block costs only the deterministic factor `card (Finset.Icc L m)`.

## Part B: the two `IntegrableOn` binders

`IntegrableOn` follows from global `Integrable` by `Integrable.integrableOn`.

## Declaration census and the `Internal` namespace

Seven of the module's eighteen exported statements live here; the remaining
eleven live in `InitialJLBound.lean`.  Below them are five `private` helpers
and four more in a nested `namespace Internal`, opened in three places so that
the file's declaration order is unchanged.  Those four are exactly the helpers
that Part C also needs: the split forced their visibility, and `Internal` is
the repository's convention for a helper that is public only because a sibling
file consumes it (see the `Internal` namespaces of
`Provider/Diffusivity/RecurrenceIntegration/Core.lean`, `Bootstrap.lean` and
`Descent.lean`).  They are *not* part of the module's exported surface.

## References

* ABK26, Section 3.5, proof of `p.combine.under.S`, Step 1.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Besov
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} [NeZero d]

namespace Internal

omit [NeZero d] in
/-- Two-point triangle inequality for the Chapter 2 Euclidean matrix operator
norm. -/
theorem matrixOperatorNorm_sub_le_add' (X Y : Mat d) :
    Ch02.matrixOperatorNorm (X - Y) ≤
      Ch02.matrixOperatorNorm X + Ch02.matrixOperatorNorm Y := by
  change ‖X - Y‖ ≤ ‖X‖ + ‖Y‖
  exact norm_sub_le X Y

end Internal

open Algsuperdiff.Section3.Provider.Homogenization.Internal

omit [NeZero d] in
/-- Depth membership is scale membership at the shifted scale. -/
private theorem mem_descendantsAtScale_of_mem_descendantsAtDepth {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) := by
  have hk : Q.scale - (j : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le j)
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
  simpa using hR

namespace Internal

omit [NeZero d] in
/-- Every cube is its own descendant at depth `0`. -/
theorem self_mem_descendantsAtScale (Q : TriadicCube d) :
    Q ∈ descendantsAtScale Q (Q.scale - ((0 : ℕ) : ℤ)) :=
  mem_descendantsAtScale_of_mem_descendantsAtDepth (by simp [descendantsAtDepth])

end Internal

omit [NeZero d] in
/-- The random upper ellipticity envelope of a cube is nonnegative. -/
private theorem coefficientCutoffCubeEllipticityUpper_nonneg (M : ABKModel d) (L : ℤ)
    (omega : Cutoff.CutoffSample d) (Q : TriadicCube d) :
    0 ≤ Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q := by
  unfold Cutoff.coefficientCutoffCubeEllipticityUpper
  exact div_nonneg (by positivity) M.nu_pos.le

omit [NeZero d] in
/-- The molecular coercivity constant `4 d nu⁻¹` is nonnegative. -/
private theorem four_mul_dim_mul_inv_nu_nonneg (M : ABKModel d) :
    (0 : ℝ) ≤ 4 * (d : ℝ) * M.nu⁻¹ :=
  mul_nonneg (mul_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le d))
    (inv_nonneg.mpr M.nu_pos.le)

open _root_.HCPolySupport.HighContrast.EntryScale in
/-- **The unconditional descendant envelope of the `sigma_*^{-1}kappa` block.**
For every descendant `R` of every cube `Q` at every depth `j`, and for *every*
sample `omega`,

`|(sigma_*^{-1}kappa)(R;omega)| <= 4 d nu⁻¹ E(omega)`,

with `E := Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q`.

The three inputs are the sharp positive semidefinite off-diagonal block bound
(`matrixOperatorNorm_lowerLeft_le_sqrt_of_isSymmetricBlockMat_of_blockPosDef`,
`VarianceClosure.lean`), the unconditional upper-left envelope above, and the
deterministic lower-right envelope
(`matrixOperatorNorm_coarseBlockMatrix_lowerRight_le_of_mem_descendantsAtScale`,
`VarianceClosure.lean`).  Unlike
`geometricWeight_mul_matrixOperatorNorm_coarseBlockMatrix_lowerLeft_le`
(`VarianceClosure.lean`) this carries **no** good event and **no** geometric
weight: the price is that the right side is random rather than deterministic.
Every natural power of `E` is integrable at `(Cutoff.cutoffSampleLaw
M).toMeasure` (`Cutoff.integrable_coefficientCutoffCubeEllipticityUpper_pow`),
which is exactly what the integrability lane below needs. -/
theorem matrixOperatorNorm_coarseBlockMatrix_lowerLeft_le_cutoffEnvelope
    (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d) (Q : TriadicCube d)
    (j : ℕ) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ))) :
    Ch02.matrixOperatorNorm
        (coarseBlockMatrix (cubeSet R)
          (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft ≤
      4 * (d : ℝ) * M.nu⁻¹ *
        Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q := by
  have hlocal : Ch04.AELocallyUniformlyEllipticField
      (Cutoff.coefficientCutoff M.nu L omega) :=
    Cutoff.coefficientCutoff_aelocallyUniformlyElliptic M L omega
  have hpsd :=
    matrixOperatorNorm_lowerLeft_le_sqrt_of_isSymmetricBlockMat_of_blockPosDef
      (coarseBlockMatrix_cubeSet_symm_of_aelocallyUniformlyEllipticField R hlocal)
      (coarseBlockMatrix_cubeSet_blockPosDef_of_uniformEllipticity R hlocal)
  refine hpsd.trans ?_
  have hul := matrixOperatorNorm_coarseBlockMatrix_upperLeft_le_cutoffEnvelope
    M L omega Q j hR
  have hlr := matrixOperatorNorm_coarseBlockMatrix_lowerRight_le_of_mem_descendantsAtScale
    M L omega Q j hR
  have hcoef := four_mul_dim_mul_inv_nu_nonneg M
  have hE := coefficientCutoffCubeEllipticityUpper_nonneg M L omega Q
  have hstep :
      Ch02.matrixOperatorNorm
            (coarseBlockMatrix (cubeSet R)
              (Cutoff.coefficientCutoff M.nu L omega).toFun).upperLeft *
          Ch02.matrixOperatorNorm
            (coarseBlockMatrix (cubeSet R)
              (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight ≤
        (4 * (d : ℝ) * M.nu⁻¹ *
          Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q) ^ 2 := by
    have := mul_le_mul hul hlr (Ch02.matrixOperatorNorm_nonneg _)
      (mul_nonneg hcoef (sq_nonneg _))
    nlinarith [this]
  refine (Real.sqrt_le_sqrt hstep).trans (le_of_eq ?_)
  exact Real.sqrt_sq (mul_nonneg hcoef hE)

namespace Internal

/-- **Pointwise envelope of the comparison vector.**  The squared length of the
block comparison vector `sigma_*^{-1}(Q)q - (sigma_*^{-1}kappa)(Q)p - p` at the
genuine cutoff is at most a deterministic affine function of `E(Q;omega)^2`.
The constant `4` (rather than the sharp `3`) comes from applying the two-term
Euclidean split `vecNormSq_sub_le` twice; only integrability is used
downstream, so no sharpness is lost. -/
theorem vecNormSq_coarseBlockScaleSeparation_le_cutoffEnvelope
    (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d) (Q : TriadicCube d)
    (p q : Vec d) :
    vecNormSq (coarseBlockScaleSeparation Q p q (Cutoff.coefficientCutoff M.nu L omega)) ≤
      4 * (4 * (d : ℝ) * M.nu⁻¹) ^ 2 * vecNormSq q + 2 * vecNormSq p +
        4 * (4 * (d : ℝ) * M.nu⁻¹) ^ 2 * vecNormSq p *
          Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ 2 := by
  have hself := self_mem_descendantsAtScale Q
  have hlr := matrixOperatorNorm_coarseBlockMatrix_lowerRight_le_of_mem_descendantsAtScale
    M L omega Q 0 hself
  have hll := matrixOperatorNorm_coarseBlockMatrix_lowerLeft_le_cutoffEnvelope
    M L omega Q 0 hself
  have hlr2 :
      Ch02.matrixOperatorNorm
          (coarseBlockMatrix (cubeSet Q)
            (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight ^ 2 ≤
        (4 * (d : ℝ) * M.nu⁻¹) ^ 2 :=
    pow_le_pow_left₀ (Ch02.matrixOperatorNorm_nonneg _) hlr 2
  have hll2 :
      Ch02.matrixOperatorNorm
          (coarseBlockMatrix (cubeSet Q)
            (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft ^ 2 ≤
        (4 * (d : ℝ) * M.nu⁻¹) ^ 2 *
          Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ 2 := by
    have h := pow_le_pow_left₀ (Ch02.matrixOperatorNorm_nonneg _) hll 2
    calc _ ≤ (4 * (d : ℝ) * M.nu⁻¹ *
            Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q) ^ 2 := h
      _ = _ := by ring
  have hmvq :=
    Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
      (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight q
  have hmvp :=
    Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
      (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft p
  have hq0 : (0 : ℝ) ≤ vecNormSq q := vecNormSq_nonneg q
  have hp0 : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  have hA : vecNormSq (matVecMul
      (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight q) ≤
      (4 * (d : ℝ) * M.nu⁻¹) ^ 2 * vecNormSq q :=
    hmvq.trans (mul_le_mul_of_nonneg_right hlr2 hq0)
  have hB : vecNormSq (matVecMul
      (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft p) ≤
      (4 * (d : ℝ) * M.nu⁻¹) ^ 2 *
        Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ 2 * vecNormSq p :=
    hmvp.trans (mul_le_mul_of_nonneg_right hll2 hp0)
  have hsplit :
      vecNormSq (coarseBlockScaleSeparation Q p q (Cutoff.coefficientCutoff M.nu L omega)) ≤
        2 * (2 * (vecNormSq (matVecMul
              (coarseBlockMatrix (cubeSet Q)
                (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight q) +
            vecNormSq (matVecMul
              (coarseBlockMatrix (cubeSet Q)
                (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft p)) +
          vecNormSq p) := by
    have h1 := vecNormSq_sub_le
      (matVecMul (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight q -
        matVecMul (coarseBlockMatrix (cubeSet Q)
          (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft p) p
    have h2 := vecNormSq_sub_le
      (matVecMul (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight q)
      (matVecMul (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft p)
    have hcarrier :
        coarseBlockScaleSeparation Q p q (Cutoff.coefficientCutoff M.nu L omega) =
          matVecMul (coarseBlockMatrix (cubeSet Q)
              (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight q -
            matVecMul (coarseBlockMatrix (cubeSet Q)
              (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft p - p := rfl
    rw [hcarrier]
    linarith
  nlinarith [hsplit, hA, hB]

/-- **Pointwise envelope of the coarse-matrix variation.**  For a descendant `R`
of `Q` at any depth, the squared coarse-matrix variation between `Q` and `R` at
the genuine cutoff is at most a deterministic affine function of `E(Q;omega)^2`.
Both channels use the two descendant envelopes; the `sigma_*^{-1}` channel is
deterministic, the `sigma_*^{-1}kappa` channel carries the random `E`. -/
theorem coarseBlockMatrixVariationSq_le_cutoffEnvelope
    (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d) (Q : TriadicCube d)
    (p q : Vec d) {j : ℕ} {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q j) :
    coarseBlockMatrixVariationSq Q p q (Cutoff.coefficientCutoff M.nu L omega) R ≤
      2 * (2 * (4 * (d : ℝ) * M.nu⁻¹)) ^ 2 * vecNormSq q +
        2 * (2 * (4 * (d : ℝ) * M.nu⁻¹)) ^ 2 * vecNormSq p *
          Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ 2 := by
  have hRs := mem_descendantsAtScale_of_mem_descendantsAtDepth hR
  have hself := self_mem_descendantsAtScale Q
  have hlrQ := matrixOperatorNorm_coarseBlockMatrix_lowerRight_le_of_mem_descendantsAtScale
    M L omega Q 0 hself
  have hlrR := matrixOperatorNorm_coarseBlockMatrix_lowerRight_le_of_mem_descendantsAtScale
    M L omega Q j hRs
  have hllQ := matrixOperatorNorm_coarseBlockMatrix_lowerLeft_le_cutoffEnvelope
    M L omega Q 0 hself
  have hllR := matrixOperatorNorm_coarseBlockMatrix_lowerLeft_le_cutoffEnvelope
    M L omega Q j hRs
  have hbase := coarseBlockMatrixVariationSq_le_two_mul_add_two_mul Q R p q
    (Cutoff.coefficientCutoff M.nu L omega)
  have htriLR := matrixOperatorNorm_sub_le_add'
    (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight
    (coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight
  have htriLL := matrixOperatorNorm_sub_le_add'
    (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft
    (coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft
  have hLR2 :
      Ch02.matrixOperatorNorm
          ((coarseBlockMatrix (cubeSet Q)
              (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight -
            (coarseBlockMatrix (cubeSet R)
              (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight) ^ 2 ≤
        (2 * (4 * (d : ℝ) * M.nu⁻¹)) ^ 2 :=
    pow_le_pow_left₀ (Ch02.matrixOperatorNorm_nonneg _) (by linarith) 2
  have hLL2 :
      Ch02.matrixOperatorNorm
          ((coarseBlockMatrix (cubeSet Q)
              (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft -
            (coarseBlockMatrix (cubeSet R)
              (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft) ^ 2 ≤
        (2 * (4 * (d : ℝ) * M.nu⁻¹)) ^ 2 *
          Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q ^ 2 := by
    have h := pow_le_pow_left₀ (Ch02.matrixOperatorNorm_nonneg _)
      (by linarith : Ch02.matrixOperatorNorm
          ((coarseBlockMatrix (cubeSet Q)
              (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft -
            (coarseBlockMatrix (cubeSet R)
              (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft) ≤
        2 * (4 * (d : ℝ) * M.nu⁻¹ *
          Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q)) 2
    calc _ ≤ (2 * (4 * (d : ℝ) * M.nu⁻¹ *
          Cutoff.coefficientCutoffCubeEllipticityUpper M L omega Q)) ^ 2 := h
      _ = _ := by ring
  have hq0 : (0 : ℝ) ≤ vecNormSq q := vecNormSq_nonneg q
  have hp0 : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  nlinarith [hbase, mul_le_mul_of_nonneg_right hLR2 hq0,
    mul_le_mul_of_nonneg_right hLL2 hp0]

end Internal

/-- **Pointwise unconditional envelope of the second good-event block.**  The
corridor sum of descendant averages of the coarse-matrix variation is bounded,
sample by sample and with no event, by a deterministic multiple of
`1 + E(omega)^2`, with `E` the cutoff cube ellipticity upper envelope of the
parent cube. -/
private theorem coarseMatrixVariationBlock_le_cutoffEnvelope (M : ABKModel d) (m L : ℤ)
    (e : Vec d) (omega : Cutoff.CutoffSample d) :
    coarseMatrixVariationBlock M m L e omega ≤
      ((Finset.Icc L m).card : ℝ) *
        (2 * (2 * (4 * (d : ℝ) * M.nu⁻¹)) ^ 2 *
            vecNormSq (Observable.sqrtLoad (Annealed.sigmaBar M L) e) +
          2 * (2 * (4 * (d : ℝ) * M.nu⁻¹)) ^ 2 *
              vecNormSq (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e) *
            Cutoff.coefficientCutoffCubeEllipticityUpper M L omega (originCube d m) ^ 2) := by
  set K : ℝ :=
    2 * (2 * (4 * (d : ℝ) * M.nu⁻¹)) ^ 2 *
        vecNormSq (Observable.sqrtLoad (Annealed.sigmaBar M L) e) +
      2 * (2 * (4 * (d : ℝ) * M.nu⁻¹)) ^ 2 *
          vecNormSq (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e) *
        Cutoff.coefficientCutoffCubeEllipticityUpper M L omega (originCube d m) ^ 2 with hK
  have hK0 : (0 : ℝ) ≤ K := by
    have := vecNormSq_nonneg (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
    have := vecNormSq_nonneg (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
    rw [hK]; positivity
  have hterm : ∀ n ∈ Finset.Icc L m,
      (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
          descendantsAverage (originCube d m) (m - n).toNat
            (coarseMatrixVariationSq (Cutoff.coefficientCutoff M.nu L omega)
              (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega)
              (originCube d m)
              (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
              (Observable.sqrtLoad (Annealed.sigmaBar M L) e)) ≤ K := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hw1 : (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      have : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hn.2
      linarith
    have havg :
        descendantsAverage (originCube d m) (m - n).toNat
          (coarseMatrixVariationSq (Cutoff.coefficientCutoff M.nu L omega)
            (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega)
            (originCube d m)
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M L) e)) ≤ K := by
      refine le_trans (descendantsAverage_le_descendantsAverage _ _ ?_)
        (le_of_eq (descendantsAverage_const _ _ K))
      intro R hR
      rw [coarseMatrixVariationSq_eq_coarseBlockMatrixVariationSq]
      exact coarseBlockMatrixVariationSq_le_cutoffEnvelope M L omega _ _ _ hR
    calc _ ≤ (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) * K := mul_le_mul_of_nonneg_left havg hw0
      _ ≤ K := mul_le_of_le_one_left hK0 hw1
  have hsum := Finset.sum_le_card_nsmul (Finset.Icc L m) _ K hterm
  rw [nsmul_eq_mul] at hsum
  exact hsum

/-- **Pointwise unconditional envelope of the third good-event block.** -/
private theorem coarseScaleSeparationBlock_le_cutoffEnvelope (M : ABKModel d) (m L : ℤ)
    (e : Vec d) (omega : Cutoff.CutoffSample d) :
    coarseScaleSeparationBlock M m L e omega ≤
      4 * (4 * (d : ℝ) * M.nu⁻¹) ^ 2 *
            vecNormSq (Observable.sqrtLoad (Annealed.sigmaBar M L) e) +
          2 * vecNormSq (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e) +
        4 * (4 * (d : ℝ) * M.nu⁻¹) ^ 2 *
            vecNormSq (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e) *
          Cutoff.coefficientCutoffCubeEllipticityUpper M L omega (originCube d m) ^ 2 := by
  rw [coarseScaleSeparationBlock, coarseScaleSeparation_eq_coarseBlockScaleSeparation]
  exact vecNormSq_coarseBlockScaleSeparation_le_cutoffEnvelope M L omega _ _ _

omit [NeZero d] in
/-- The third good-event block is a squared length, hence nonnegative. -/
theorem coarseScaleSeparationBlock_nonneg (M : ABKModel d) (m L : ℤ) (e : Vec d)
    (omega : Cutoff.CutoffSample d) : 0 ≤ coarseScaleSeparationBlock M m L e omega :=
  vecNormSq_nonneg _

omit [NeZero d] in
/-- The second good-event block is a nonnegatively weighted corridor sum of
descendant averages of squared lengths, hence nonnegative. -/
theorem coarseMatrixVariationBlock_nonneg (M : ABKModel d) (m L : ℤ) (e : Vec d)
    (omega : Cutoff.CutoffSample d) : 0 ≤ coarseMatrixVariationBlock M m L e omega := by
  refine Finset.sum_nonneg fun n _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
  exact descendantsAverage_nonneg _ _ _ fun R _ => coarseMatrixVariationSq_nonneg _ _ _ _ _ R

/-- **Global integrability of the third good-event block** at the genuine cutoff
sample law, with no event and no hypothesis beyond the standing model data.  The
dominating function is `A + B E^2`;
`Cutoff.integrable_coefficientCutoffCubeEllipticityUpper_pow` supplies the
integrability of `E^2`. -/
theorem integrable_coarseScaleSeparationBlock (M : ABKModel d) (m L : ℤ) (e : Vec d) :
    Integrable (coarseScaleSeparationBlock M m L e) (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hE2 :=
    Cutoff.integrable_coefficientCutoffCubeEllipticityUpper_pow M L (originCube d m) 2
  refine Integrable.mono'
    ((integrable_const (4 * (4 * (d : ℝ) * M.nu⁻¹) ^ 2 *
          vecNormSq (Observable.sqrtLoad (Annealed.sigmaBar M L) e) +
        2 * vecNormSq (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e))).add
      (hE2.const_mul (4 * (4 * (d : ℝ) * M.nu⁻¹) ^ 2 *
        vecNormSq (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e))))
    (aemeasurable_coarseScaleSeparationSq M m L e).aestronglyMeasurable ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (coarseScaleSeparationBlock_nonneg M m L e omega)]
  exact coarseScaleSeparationBlock_le_cutoffEnvelope M m L e omega

/-- **Global integrability of the second good-event block** at the genuine cutoff
sample law.  The corridor weight `3^{-(m-n)}` is at most `1` and the corridor is
finite, so the envelope of the single descendant average is multiplied by the
deterministic factor `card (Finset.Icc L m)`. -/
theorem integrable_coarseMatrixVariationBlock (M : ABKModel d) (m L : ℤ) (e : Vec d) :
    Integrable (coarseMatrixVariationBlock M m L e) (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hE2 :=
    Cutoff.integrable_coefficientCutoffCubeEllipticityUpper_pow M L (originCube d m) 2
  refine Integrable.mono'
    (((integrable_const (2 * (2 * (4 * (d : ℝ) * M.nu⁻¹)) ^ 2 *
          vecNormSq (Observable.sqrtLoad (Annealed.sigmaBar M L) e))).add
        (hE2.const_mul (2 * (2 * (4 * (d : ℝ) * M.nu⁻¹)) ^ 2 *
          vecNormSq (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)))).const_mul
      ((Finset.Icc L m).card : ℝ))
    (aemeasurable_coarseMatrixVariationCorridor M m L e).aestronglyMeasurable ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (coarseMatrixVariationBlock_nonneg M m L e omega)]
  refine (coarseMatrixVariationBlock_le_cutoffEnvelope M m L e omega).trans (le_of_eq ?_)
  simp only [Pi.add_apply]

/-- **The second `IntegrableOn` binder of the proved `CombineExpectation`
endpoints, discharged.**  Global integrability restricts to any set. -/
theorem integrableOn_coarseScaleSeparationBlock_compl_observationScaleBadEvent
    (M : ABKModel d) (m L : ℤ) (e : Vec d) :
    IntegrableOn (coarseScaleSeparationBlock M m L e)
      (observationScaleBadEvent M L m)ᶜ (Cutoff.cutoffSampleLaw M).toMeasure :=
  (integrable_coarseScaleSeparationBlock M m L e).integrableOn

theorem integrableOn_coarseMatrixVariationBlock_compl_observationScaleBadEvent
    (M : ABKModel d) (m L : ℤ) (e : Vec d) :
    IntegrableOn (coarseMatrixVariationBlock M m L e)
      (observationScaleBadEvent M L m)ᶜ (Cutoff.cutoffSampleLaw M).toMeasure :=
  (integrable_coarseMatrixVariationBlock M m L e).integrableOn

end

end Algsuperdiff.Section3.Provider.Homogenization
