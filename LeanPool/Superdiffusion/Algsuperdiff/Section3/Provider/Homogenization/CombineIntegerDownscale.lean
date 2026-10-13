/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.CubeScalar
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Annealed.Monotonicity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.ResponseCommonDomination
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.Expectations

/-!
# CombineIntegerDownscale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Step 2 of `p.combine.under.S`: the squared means-downscale-by-defect estimate

ABK26, Step 2 of Proposition `p.combine.under.S`.  The step opens by taking the
expectation of the coarse-grained identity `e.J.coarse.grained` and combining
it with subadditivity `e.subaddJ.nosymm` and the vanishing annealed coupling
`e.annealed.khom.zero` to get, for scale indices `n <= m` and `e, e'` with `|e|
= 1`,

```
0 <= shom_{L,*}^{-1}(cu_n) - shom_{L,*}^{-1}(cu_m)
   = 2 E[ J(cu_n, 0, e; a_L) - J(cu_m, 0, e; a_L) ]
  <= 2 E[ J(cu_n, e', e; a_L) - J(cu_m, e', e; a_L) ]
```

and then, under the load normalization `e.pq.normed`, the printed display

```
0 <= shom_{L,*}^{-1}(cu_n) - shom_{L,*}^{-1}(cu_m)
  <= 2 shom_{L,*}^{-1}(cu_m) E[ J(cu_n, p, q; a_L) - J(cu_m, p, q; a_L) ] .
```

The last declaration below states the strictly stronger form obtained by
replacing the right-hand gauge `shom_{L,*}^{-1}(cu_m)` by
`|q|^{-2} = shom_L^{-1}`; see *Route*.

## Scope

The first group of declarations corresponds to the two mean-propagation
displays; these carry no constant and no premise beyond the load normalization.

The second group completes Step 2 with the squared estimate
`e.means.downscale.by.defect` (closed).  It consumes the proposition's own
one-cube fourth-moment premise `e.moment.bound.onmathcalE` and the load
normalization `e.pq.normed` as hypotheses, in three steps:

1. nonnegativity of `E[J(cu_m,p,q;a_L)]` and the subadditivity chain
   `E[J(cu_n,p,q;a_L)] <= E[J(cu_L,p,q;a_L)]` for `L <= n`;
2. the one-cube bound `E[J(cu_L,p,q;a_L)] <= delta_1`, obtained from the first
   inequality of `e.mathcalE.monotone.ordered` (in the form of the proved
   simultaneous directional domination `J <= E_{s,infinity,2}^2`) and
   Cauchy--Schwarz `E[X^2] <= E[X^4]^{1/2}`.  The sub-cube discount
   `e.bound.one.cube.by.mathcalE` is not used: the observed cube and the
   coefficient cutoff cube are both `cu_L`, so its `k = m` instance is the
   identity;
3. squaring against the `|q|^{-2} = shom_L^{-1}` gauge of the first group.

Because the gauge of step 3 is already `shom_L^{-1}`, the printed step
`shom_{L,*}^{-1}(cu_m) <= 2 shom_L^{-1}` -- the only place where the moment
premise is used a second time -- is not needed, and the universal constant of
`e.means.downscale.by.defect` is delivered as the explicit numeral `4`.

## Rendering of the moment premise

The printed premise `E[E_{s,infinity,2}(cu_L; a_L, shom_L)^4]^{1/2} <= delta_1`
asserts in particular that the fourth moment of a nonnegative observable is
*finite*.  Bochner's `∫` returns `0` on a non-integrable function, so the
literal transcription `Real.sqrt (∫ ...) <= delta_1` would be satisfied
vacuously by an infinite moment.  The premise is therefore carried in its
lower-integral form `∫⁻.ofReal (E^4) <=.ofReal (delta_1 ^ 2)`, which is exactly
`E[E^4] <= delta_1^2` for the nonnegative observable and encodes finiteness and
the bound in one clause.  `lintegral_ofReal_le_ofReal_sq_of_sqrt_integral_le`
converts the Bochner pair (integrability together with the literal `Real.sqrt`
bound) into it.

The observable itself is `Observable.cutoffHomogenizationErrorRepresentative M
L L hs (Annealed.sigmaBar M L)`, the proved measurable representative of
`E_{s,infinity,2}(cu_L; a_L, shom_L)`: coefficient-cutoff scale `L`, observed
cube `cu_L`, comparator the genuine running diffusivity `shom_L`.  It is a.e.
equal to the literal CoarseGraining expression by
`Observable.cutoffHomogenizationErrorRaw_ae_eq_representative`, so the premise
is the same statement as the printed one.

The load normalization is carried as its two printed clauses
`q = shom_L p` and `|q|^2 = shom_L`; the derivation uses both (the first to
identify `p`, the second to identify `|q|^2` and the unit direction).

## Route

The printed derivation of the normalized display uses the coefficient-field
homogeneity `e.homogeneous.J` to move the load `(p, q)` onto the unit pair
`(e', e)`.  That rescaling is not available on the `CoeffOn`/`Domain` carriers
of this repository.  It is not needed: the annealed coarse-grained identity is
an *exact* quadratic form in `(p, q)`, so the load enters only through `|q|^2 =
vecNormSq q` and through a second quadratic form in `p` which is nonnegative by
the same subadditivity input.  The conclusion below is therefore obtained with
the load kept general, and it is strictly stronger than the printed display:
the printed right-hand side carries the factor `shom_{L,*}^{-1}(cu_m)`, and
`|q|^{-2} = shom_L^{-1} <= shom_{L,*}^{-1}(cu_m)` by the unconditional Loewner
monotonicity and infinite-volume limit of `e.homs.defs`, not by the moment
premise; the moment premise supplies only the opposite half
`shom_{L,*}^{-1}(cu_m) <= 2 shom_L^{-1}`.  The printed display is recoverable
in this repository from
`Provider.Diffusivity.ApproximateRecurrence.inv_sigmaBar_le_annealedCubeLowerRight`
together with
`Provider.Annealed.coefficientCutoffLaw_exists_annealedBlockMatrixAtScale_eq_blockDiag_smul_one`.

The `e.homogeneous.J` bypass now covers the squaring step as well, and there
too no rescaling is performed.  The printed proof invokes homogeneity to put
the load in the normalized form the one-cube input expects; but `shom_L` is a
*positive scalar*, so `e.pq.normed` already presents the load in that form:
`exists_unit_loads_of_pq_normed` certifies that `q = shom_L p` together with
`|q|^2 = shom_L` forces `(p, q) = (shom_L^{-1/2} e, shom_L^{1/2} e)` for the
unit vector `e = shom_L^{-1/2} q`.  The identification is an equality of loads,
not a rescaling of the coefficient field, so the whole file is free of
`e.homogeneous.J`.

## Inputs

* `e.J.coarse.grained`: CoarseGraining's
  `Ch04.RestrictionLawCarrier.integral_restrictionResponseJObservableCubeSet_eq_quadratic_annealedBlockMatrix`,
  whose integrability side condition is discharged here (not assumed) from
  `Provider.Annealed.coefficientCutoffLaw_integrable_coarseFullBlockMatrixAtCube`.
* `e.annealed.khom.zero`:
  `Provider.Annealed.coefficientCutoffLaw_annealedBlockMatrix_lowerLeft_eq_zero`.
* `e.subaddJ.nosymm`, at every integer scale:
  `Provider.Annealed.coefficientCutoffLaw_matLoewnerLE_annealedSigmaStarInvAtScale`
  and `..._matLoewnerLE_annealedBAtScale`.
* Scalarity of the annealed inverse-star block on origin cubes:
  `Provider.Annealed.coefficientCutoffLaw_isScalarMatrix_annealedSigmaStarInvAtScale`.
* the first inequality of `e.mathcalE.monotone.ordered` at the cutoff cube, in
  the simultaneous directional form
  `Provider.Homogenization.ae_forall_cutoffResponseJ_le_observationHomogenizationError_sq`,
  read at `cubeScale = coefficientScale = L`, together with
  `Observable.ae_forall_cutoffResponseJ_eq_literal`, which identifies the
  measurable response with the literal `J(cu_L, shom_L^{-1/2} e, shom_L^{1/2} e; a_L)`.

## Main results

* `annealedSigmaStarInvScalarAtScale`
* `coefficientCutoffLaw_annealedSigmaStarInvAtScale_eq_smul_one`
* `coefficientCutoffLaw_vecDot_matVecMul_annealedSigmaStarInvAtScale`
* `coefficientCutoffLaw_annealedResponseJAtScale_eq_annealedDiagonalBlocks`
* `coefficientCutoffLaw_annealedResponseJAtScale_eq_scalar`
* `coefficientCutoffLaw_annealedResponseJAtScale_sub_eq`
* `coefficientCutoffLaw_annealedSigmaStarInvScalarAtScale_antitone`
* `coefficientCutoffLaw_annealedSigmaStarInvScalarAtScale_sub_mul_vecNormSq_le_two_mul_annealedResponseJAtScale_sub`
* `coefficientCutoffLaw_annealedSigmaStarInvScalarAtScale_sub_le_two_mul_inv_vecNormSq_mul_annealedResponseJAtScale_sub`
* `coefficientCutoffLaw_annealedResponseJAtScale_nonneg`
* `coefficientCutoffLaw_annealedResponseJAtScale_antitone`
* `coefficientCutoffLaw_annealedResponseJAtScale_le_of_moment_bound`
* `coefficientCutoffLaw_sq_abs_annealedSigmaStarInvScalarAtScale_sub_le`
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The quadratic form of a scalar matrix is the scalar times the squared
norm. -/
private theorem vecDot_matVecMul_smul_one (c : ℝ) (x : Vec d) :
    vecDot x (matVecMul (c • (1 : Mat d)) x) = c * vecNormSq x := by
  have hone : matVecMul (1 : Mat d) x = x := Matrix.one_mulVec x
  rw [smul_matVecMul, vecDot_smul_right, hone, vecNormSq]

omit [NeZero d] in
/-- The mixed block contributes nothing once it vanishes. -/
private theorem vecDot_matVecMul_zero (x y : Vec d) :
    vecDot x (matVecMul (0 : Mat d) y) = 0 := by
  simp [vecDot, matVecMul]

/-- The scalar `shom_{L,*}^{-1}(cu_n)` of ABK26 Step 2: the annealed
inverse-star block of the genuine coefficient cutoff on the origin cube at
integer scale `n` is a scalar matrix, and this is its scalar. -/
def annealedSigmaStarInvScalarAtScale (M : ABKModel d) (L n : ℤ) : ℝ :=
  Ch04.annealedSigmaStarInvAtScale (Cutoff.coefficientCutoffLaw M L) n 0 0

/-- The annealed inverse-star block of the genuine cutoff on an origin cube is
the scalar multiple of the identity determined by
`annealedSigmaStarInvScalarAtScale`. -/
theorem coefficientCutoffLaw_annealedSigmaStarInvAtScale_eq_smul_one
    (M : ABKModel d) (L n : ℤ) :
    Ch04.annealedSigmaStarInvAtScale (Cutoff.coefficientCutoffLaw M L) n =
      annealedSigmaStarInvScalarAtScale M L n • (1 : Mat d) := by
  obtain ⟨c, hc⟩ :=
    Annealed.coefficientCutoffLaw_isScalarMatrix_annealedSigmaStarInvAtScale M L n
  have hscalar : annealedSigmaStarInvScalarAtScale M L n = c := by
    show Ch04.annealedSigmaStarInvAtScale (Cutoff.coefficientCutoffLaw M L) n 0 0 = c
    rw [hc]
    simp
  rw [hscalar, hc]

/-- Scalar form of the annealed inverse-star quadratic form. -/
theorem coefficientCutoffLaw_vecDot_matVecMul_annealedSigmaStarInvAtScale
    (M : ABKModel d) (L n : ℤ) (x : Vec d) :
    vecDot x
        (matVecMul (Ch04.annealedSigmaStarInvAtScale (Cutoff.coefficientCutoffLaw M L) n) x) =
      annealedSigmaStarInvScalarAtScale M L n * vecNormSq x := by
  rw [coefficientCutoffLaw_annealedSigmaStarInvAtScale_eq_smul_one M L n,
    vecDot_matVecMul_smul_one]

/-- **ABK26 `e.J.coarse.grained` in the mean, with `e.annealed.khom.zero`.**
The expected response of the genuine coefficient cutoff on the origin cube at
any integer scale `n` is the block-diagonal quadratic form

`E[J(cu_n, p, q; a_L)] = 1/2 q. shom_{L,*}^{-1}(cu_n) q - p. q
    + 1/2 p. bhom_L(cu_n) p`.

The mixed block is absent because the annealed coupling of the cutoff law
vanishes; the integrability side condition of the expectation identity is
discharged from the proved cutoff moment layer, not assumed. -/
theorem coefficientCutoffLaw_annealedResponseJAtScale_eq_annealedDiagonalBlocks
    (M : ABKModel d) (L n : ℤ) (p q : Vec d) :
    Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) n p q =
      (1 / 2 : ℝ) *
          vecDot q
            (matVecMul
              (Ch04.annealedSigmaStarInvAtScale (Cutoff.coefficientCutoffLaw M L) n) q) -
        vecDot p q +
        (1 / 2 : ℝ) *
          vecDot p
            (matVecMul (Ch04.annealedBAtScale (Cutoff.coefficientCutoffLaw M L) n) p) := by
  have hquad :=
    (Cutoff.coefficientCutoffLaw_lawCarrier M
        L).integral_restrictionResponseJObservableCubeSet_eq_quadratic_annealedBlockMatrix
      (originCube d n) p q
      (Annealed.coefficientCutoffLaw_integrable_coarseFullBlockMatrixAtCube M L
        (originCube d n))
  have hmixed :
      (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M L)
        (cubeSet (originCube d n))).lowerLeft = 0 :=
    Annealed.coefficientCutoffLaw_annealedBlockMatrix_lowerLeft_eq_zero M L (originCube d n)
  have hlowerRight :
      (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M L)
        (cubeSet (originCube d n))).lowerRight =
        Ch04.annealedSigmaStarInvAtScale (Cutoff.coefficientCutoffLaw M L) n := rfl
  have hupperLeft :
      (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M L)
        (cubeSet (originCube d n))).upperLeft =
        Ch04.annealedBAtScale (Cutoff.coefficientCutoffLaw M L) n := rfl
  rw [hmixed, vecDot_matVecMul_zero, hlowerRight, hupperLeft] at hquad
  show ∫ a, Ch04.restrictionResponseJObservableCubeSet (originCube d n) p q a
      ∂(Cutoff.coefficientCutoffLaw M L) = _
  rw [hquad]
  ring

/-- Scalarized form of
`coefficientCutoffLaw_annealedResponseJAtScale_eq_annealedDiagonalBlocks`. -/
theorem coefficientCutoffLaw_annealedResponseJAtScale_eq_scalar
    (M : ABKModel d) (L n : ℤ) (p q : Vec d) :
    Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) n p q =
      (1 / 2 : ℝ) * (annealedSigmaStarInvScalarAtScale M L n * vecNormSq q) -
        vecDot p q +
        (1 / 2 : ℝ) *
          vecDot p
            (matVecMul (Ch04.annealedBAtScale (Cutoff.coefficientCutoffLaw M L) n) p) := by
  rw [coefficientCutoffLaw_annealedResponseJAtScale_eq_annealedDiagonalBlocks M L n p q,
    coefficientCutoffLaw_vecDot_matVecMul_annealedSigmaStarInvAtScale M L n q]

/-- **Exact mean response defect.**  The `p . q` terms cancel, so the response
defect between two integer cube scales splits into the inverse-star scalar
increment weighted by `|q|^2` and the increment of the annealed upper-left
quadratic form. -/
theorem coefficientCutoffLaw_annealedResponseJAtScale_sub_eq
    (M : ABKModel d) (L n m : ℤ) (p q : Vec d) :
    Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) n p q -
        Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) m p q =
      (1 / 2 : ℝ) *
          ((annealedSigmaStarInvScalarAtScale M L n -
            annealedSigmaStarInvScalarAtScale M L m) * vecNormSq q) +
        ((1 / 2 : ℝ) *
            vecDot p
              (matVecMul (Ch04.annealedBAtScale (Cutoff.coefficientCutoffLaw M L) n) p) -
          (1 / 2 : ℝ) *
            vecDot p
              (matVecMul (Ch04.annealedBAtScale (Cutoff.coefficientCutoffLaw M L) m) p)) := by
  rw [coefficientCutoffLaw_annealedResponseJAtScale_eq_scalar M L n p q,
    coefficientCutoffLaw_annealedResponseJAtScale_eq_scalar M L m p q]
  ring

/-- **Nonnegativity of the mean defect at every integer scale.**  This is the
left-hand inequality of the ABK26 Step-2 display: the annealed inverse-star
scalar of the cutoff is nonincreasing along the integer cube scales. -/
theorem coefficientCutoffLaw_annealedSigmaStarInvScalarAtScale_antitone
    (M : ABKModel d) (L : ℤ) {n m : ℤ} (hnm : n ≤ m) :
    annealedSigmaStarInvScalarAtScale M L m ≤ annealedSigmaStarInvScalarAtScale M L n := by
  have hloewner :=
    Annealed.coefficientCutoffLaw_matLoewnerLE_annealedSigmaStarInvAtScale M L hnm
  rw [coefficientCutoffLaw_annealedSigmaStarInvAtScale_eq_smul_one M L m,
    coefficientCutoffLaw_annealedSigmaStarInvAtScale_eq_smul_one M L n] at hloewner
  exact Ch04.scalar_le_of_matLoewnerLE_smul_one hloewner

/-- **ABK26 Step 2 with a general load.**  For every integer pair of cube
scales `n <= m` and every load `(p, q)`,

`(shom_{L,*}^{-1}(cu_n) - shom_{L,*}^{-1}(cu_m)) |q|^2
    <= 2 E[J(cu_n, p, q; a_L) - J(cu_m, p, q; a_L)]`.

This is the load-general form of the printed display: no rescaling of the load
directions is needed, because the annealed coarse-grained identity is exact. -/
theorem coefficientCutoffLaw_annealedSigmaStarInvScalarAtScale_sub_mul_vecNormSq_le_two_mul_annealedResponseJAtScale_sub
    (M : ABKModel d) (L : ℤ) {n m : ℤ} (hnm : n ≤ m) (p q : Vec d) :
    (annealedSigmaStarInvScalarAtScale M L n - annealedSigmaStarInvScalarAtScale M L m) *
        vecNormSq q ≤
      2 * (Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) n p q -
        Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) m p q) := by
  have hsplit := coefficientCutoffLaw_annealedResponseJAtScale_sub_eq M L n m p q
  have hb := Annealed.coefficientCutoffLaw_matLoewnerLE_annealedBAtScale M L hnm p
  linarith

/-- **ABK26 Step 2, normalized display.**  Under the load normalization
`e.pq.normed` the squared norm `|q|^2 = shom_L` is positive, and the mean
defect obeys

`0 <= shom_{L,*}^{-1}(cu_n) - shom_{L,*}^{-1}(cu_m)
    <= 2 |q|^{-2} E[J(cu_n, p, q; a_L) - J(cu_m, p, q; a_L)]`

for every integer pair of cube scales `n <= m`. -/
theorem coefficientCutoffLaw_annealedSigmaStarInvScalarAtScale_sub_le_two_mul_inv_vecNormSq_mul_annealedResponseJAtScale_sub
    (M : ABKModel d) (L : ℤ) {n m : ℤ} (hnm : n ≤ m) (p : Vec d) {q : Vec d}
    (hq : 0 < vecNormSq q) :
    0 ≤ annealedSigmaStarInvScalarAtScale M L n - annealedSigmaStarInvScalarAtScale M L m ∧
      annealedSigmaStarInvScalarAtScale M L n - annealedSigmaStarInvScalarAtScale M L m ≤
        2 * (vecNormSq q)⁻¹ *
          (Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) n p q -
            Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) m p q) := by
  refine ⟨by linarith [coefficientCutoffLaw_annealedSigmaStarInvScalarAtScale_antitone M L hnm],
    ?_⟩
  have hmul :=
    coefficientCutoffLaw_annealedSigmaStarInvScalarAtScale_sub_mul_vecNormSq_le_two_mul_annealedResponseJAtScale_sub
      M L hnm p q
  have hne : vecNormSq q ≠ 0 := ne_of_gt hq
  rw [← sub_nonneg]
  have hkey :
      2 * (vecNormSq q)⁻¹ *
            (Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) n p q -
              Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) m p q) -
          (annealedSigmaStarInvScalarAtScale M L n -
            annealedSigmaStarInvScalarAtScale M L m) =
        (vecNormSq q)⁻¹ *
          (2 * (Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) n p q -
              Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) m p q) -
            (annealedSigmaStarInvScalarAtScale M L n -
              annealedSigmaStarInvScalarAtScale M L m) * vecNormSq q) := by
    field_simp
  rw [hkey]
  exact mul_nonneg (inv_nonneg.mpr hq.le) (by linarith)

/-! ## Step 2, part (i): sign and monotonicity of the mean response

The two facts the squaring step needs about the mean response itself: it is
nonnegative at every scale (`e.Jenergyv.nosymm`, in the mean), and it is
nonincreasing along the integer cube scales (`e.subaddJ.nosymm`).
-/

omit [NeZero d] in
/-- **Nonnegativity of the mean response.**  The response functional is
pointwise nonnegative, hence so is its expectation, at every integer cube
scale and every load. -/
theorem coefficientCutoffLaw_annealedResponseJAtScale_nonneg
    (M : ABKModel d) (L n : ℤ) (p q : Vec d) :
    0 ≤ Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) n p q := by
  refine integral_nonneg ?_
  intro a
  exact Ch04.restrictionResponseJObservableCubeSet_nonneg (originCube d n) p q a

/-- **The subadditivity chain of ABK26 Step 2.**  The mean response of the
genuine coefficient cutoff is nonincreasing in the cube scale, at every pair of
integer scales `n <= k` and every load.  Applied at `n = L` this is the
inequality `E[J(cu_n,p,q;a_L)] <= E[J(cu_L,p,q;a_L)]` for `L <= n`. -/
theorem coefficientCutoffLaw_annealedResponseJAtScale_antitone
    (M : ABKModel d) (L : ℤ) {n k : ℤ} (hnk : n ≤ k) (p q : Vec d) :
    Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) k p q ≤
      Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) n p q := by
  have hsplit := coefficientCutoffLaw_annealedResponseJAtScale_sub_eq M L n k p q
  have hb := Annealed.coefficientCutoffLaw_matLoewnerLE_annealedBAtScale M L hnk p
  have hstar := coefficientCutoffLaw_annealedSigmaStarInvScalarAtScale_antitone M L hnk
  have hgauge : 0 ≤ (annealedSigmaStarInvScalarAtScale M L n -
      annealedSigmaStarInvScalarAtScale M L k) * vecNormSq q :=
    mul_nonneg (sub_nonneg.2 hstar) (vecNormSq_nonneg q)
  linarith

/-! ## Step 2, part (ii): the one-cube bound under the moment premise -/

/-- Cauchy--Schwarz against the constant on a probability space: the square of
the mean is below the mean of the square. -/
private theorem sq_integral_le_integral_sq_prob {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
    {f : Omega → ℝ} (hf : Integrable f mu) (hf2 : Integrable (fun x => f x ^ 2) mu) :
    (∫ x, f x ∂mu) ^ 2 ≤ ∫ x, f x ^ 2 ∂mu := by
  set c : ℝ := ∫ x, f x ∂mu with hc
  have hexp : (fun x => (f x - c) ^ 2) =
      fun x => f x ^ 2 + (-(2 * c) * f x + c ^ 2) := by
    funext x
    ring
  have hint : Integrable (fun x => -(2 * c) * f x + c ^ 2) mu :=
    (hf.const_mul (-(2 * c))).add (integrable_const _)
  have hnn : (0 : ℝ) ≤ ∫ x, (f x - c) ^ 2 ∂mu := integral_nonneg fun _ => sq_nonneg _
  rw [hexp, integral_add hf2 hint,
    integral_add (hf.const_mul (-(2 * c))) (integrable_const _),
    integral_const_mul] at hnn
  have hconst : ∫ _x : Omega, c ^ 2 ∂mu = c ^ 2 := by simp
  rw [hconst, ← hc] at hnn
  nlinarith [hnn]

/-- **The second moment under the fourth-moment premise.**  For a measurable
real observable on a probability space whose fourth moment is at most `b ^ 2`
in the lower integral, the square is integrable and its mean is at most `b`.
This is `E[X^2] <= E[X^4]^{1/2}`. -/
private theorem integral_sq_le_of_lintegral_ofReal_pow_four_le {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → ℝ} (hX : Measurable X) {b : ℝ} (hb : 0 ≤ b)
    (hmoment : ∫⁻ x, ENNReal.ofReal (X x ^ 4) ∂mu ≤ ENNReal.ofReal (b ^ 2)) :
    Integrable (fun x => X x ^ 2) mu ∧ ∫ x, X x ^ 2 ∂mu ≤ b := by
  have hfour : ∀ x, 0 ≤ X x ^ 4 := fun x => by positivity
  have hint4 : Integrable (fun x => X x ^ 4) mu := by
    refine ⟨(hX.pow_const 4).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hfour)]
    exact lt_of_le_of_lt hmoment ENNReal.ofReal_lt_top
  have hint2 : Integrable (fun x => X x ^ 2) mu := by
    have hmaj : Integrable (fun x => 1 + X x ^ 4) mu := (integrable_const _).add hint4
    refine hmaj.mono' ((hX.pow_const 2).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (X x ^ 2 - 1), hfour x]
  have hfour_le : ∫ x, X x ^ 4 ∂mu ≤ b ^ 2 := by
    have heq : ∫ x, X x ^ 4 ∂mu = (∫⁻ x, ENNReal.ofReal (X x ^ 4) ∂mu).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hfour)
        ((hX.pow_const 4).aestronglyMeasurable)
    rw [heq]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hmoment
  refine ⟨hint2, ?_⟩
  have hcs : (∫ x, X x ^ 2 ∂mu) ^ 2 ≤ ∫ x, X x ^ 4 ∂mu := by
    have hpow : (fun x => (X x ^ 2) ^ 2) = fun x => X x ^ 4 := by
      funext x
      ring
    have h := sq_integral_le_integral_sq_prob hint2 (by rw [hpow]; exact hint4)
    rwa [hpow] at h
  have hnn : 0 ≤ ∫ x, X x ^ 2 ∂mu := integral_nonneg fun x => by positivity
  nlinarith [hcs, hfour_le, hnn, hb]

/-- The mean response of the genuine cutoff at an integer cube scale, read on
the cutoff-sample carrier.  The coefficient law is the pushforward of the
sample law along the genuine coefficient cutoff, so no new hypothesis enters. -/
private theorem coefficientCutoffLaw_annealedResponseJAtScale_eq_integral_cutoffSampleLaw
    (M : ABKModel d) (L n : ℤ) (p q : Vec d) :
    Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) n p q =
      ∫ omega, ResponseJ (cubeSet (originCube d n)) p q
          (Cutoff.coefficientCutoff M.nu L omega).toFun
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have hmeas : AEStronglyMeasurable
      (Ch04.restrictionResponseJObservableCubeSet (originCube d n) p q)
      (Cutoff.coefficientCutoffLaw M L) :=
    ((Cutoff.coefficientCutoffLaw_lawCarrier M
        L).aemeasurable_restrictionResponseJObservableCubeSet
      (originCube d n) p q).aestronglyMeasurable
  show ∫ a, Ch04.restrictionResponseJObservableCubeSet (originCube d n) p q a
      ∂(Cutoff.coefficientCutoffLaw M L) = _
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hmeas ⊢
  rw [integral_map (Cutoff.measurable_coefficientCutoff M.nu L).aemeasurable hmeas]
  rfl

omit [NeZero d] in
/-- **`e.pq.normed` names a unit direction.**  A load pair with `q = shom_L p`
and `|q|^2 = shom_L` is exactly the pair `(shom_L^{-1/2} e, shom_L^{1/2} e)`
for the unit vector `e = shom_L^{-1/2} q`. -/
private theorem exists_unit_loads_of_pq_normed (M : ABKModel d) (L : ℤ) {p q : Vec d}
    (hpq : q = (Annealed.sigmaBar M L : ℝ) • p)
    (hqnorm : vecNormSq q = (Annealed.sigmaBar M L : ℝ)) :
    ∃ e : Vec d, vecNormSq e = 1 ∧
      Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e = p ∧
      Observable.sqrtLoad (Annealed.sigmaBar M L) e = q := by
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M L : ℝ) := (Annealed.sigmaBar M L).property
  have hroot : (0 : ℝ) < Real.sqrt (Annealed.sigmaBar M L : ℝ) := Real.sqrt_pos.2 hsigma
  have hrootne : Real.sqrt (Annealed.sigmaBar M L : ℝ) ≠ 0 := ne_of_gt hroot
  have hrootsq : Real.sqrt (Annealed.sigmaBar M L : ℝ) ^ 2 = (Annealed.sigmaBar M L : ℝ) :=
    Real.sq_sqrt hsigma.le
  refine ⟨(Real.sqrt (Annealed.sigmaBar M L : ℝ))⁻¹ • q, ?_, ?_, ?_⟩
  · rw [vecNormSq_smul, hqnorm, inv_pow, hrootsq]
    field_simp
  · have hscalar : (Real.sqrt (Annealed.sigmaBar M L : ℝ))⁻¹ *
        (Real.sqrt (Annealed.sigmaBar M L : ℝ))⁻¹ * (Annealed.sigmaBar M L : ℝ) = 1 := by
      field_simp
      exact hrootsq.symm
    rw [Observable.inverseSqrtLoad, smul_smul, hpq, smul_smul, hscalar, one_smul]
  · rw [Observable.sqrtLoad, smul_smul, mul_inv_cancel₀ hrootne, one_smul]

/-- **The one-cube bound.**  Under the proposition's fourth-moment premise
`e.moment.bound.onmathcalE` and the load normalization `e.pq.normed`, the mean
response of the genuine coefficient cutoff on its own cube obeys

`E[J(cu_L, p, q; a_L)] <= delta_1`.

The route is the first inequality of `e.mathcalE.monotone.ordered` at the
cutoff cube -- the a.e. domination
`J(cu_L, shom_L^{-1/2} e, shom_L^{1/2} e; a_L) <=
E_{s,infinity,2}(cu_L; a_L, shom_L)^2` in every unit direction -- followed by
Cauchy--Schwarz.  The universal constant of the printed bound is therefore
`1` here. -/
theorem coefficientCutoffLaw_annealedResponseJAtScale_le_of_moment_bound
    (M : ABKModel d) (L : ℤ) {s : ℝ} (hs : 0 < s) {delta1 : ℝ}
    (hdelta1 : delta1 ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hmoment : ∫⁻ omega, ENNReal.ofReal
        (Observable.cutoffHomogenizationErrorRepresentative M L L hs
          (Annealed.sigmaBar M L) omega ^ 4)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (delta1 ^ 2))
    {p q : Vec d} (hpq : q = (Annealed.sigmaBar M L : ℝ) • p)
    (hqnorm : vecNormSq q = (Annealed.sigmaBar M L : ℝ)) :
    Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) L p q ≤ delta1 := by
  obtain ⟨e, he, hpload, hqload⟩ := exists_unit_loads_of_pq_normed M L hpq hqnorm
  obtain ⟨hint2, hbound⟩ :=
    integral_sq_le_of_lintegral_ofReal_pow_four_le
      (mu := (Cutoff.cutoffSampleLaw M).toMeasure)
      (Observable.measurable_cutoffHomogenizationErrorRepresentative M L L hs
        (Annealed.sigmaBar M L)) hdelta1.1.le hmoment
  rw [coefficientCutoffLaw_annealedResponseJAtScale_eq_integral_cutoffSampleLaw M L L]
  refine le_trans (integral_mono_of_nonneg ?_ hint2 ?_) hbound
  · exact Filter.Eventually.of_forall fun _ =>
      responseJ_nonneg (cubeSet (originCube d L)) p q _
  · have hunit : Ch02.vecNorm e = 1 :=
      Ch05.Section56.vecNorm_eq_one_of_vecNormSq_eq_one he
    filter_upwards
      [Observable.ae_forall_cutoffResponseJ_eq_literal M L L,
        ae_forall_cutoffResponseJ_le_observationHomogenizationError_sq M L L hs]
      with omega hliteral hdomination
    rw [← hpload, ← hqload, ← hliteral e]
    exact hdomination e hunit

/-! ## Step 2, part (iii): the squared means-downscale-by-defect display -/

/-- **ABK26 `e.means.downscale.by.defect` (closed).**  Under the proposition's
fourth-moment premise `e.moment.bound.onmathcalE` with `delta_1 in (0, 1/2]`
and the load normalization `e.pq.normed`, for all integer cube scales `L <= n
<= m`,

`|shom_{L,*}^{-1}(cu_m) - shom_{L,*}^{-1}(cu_n)|^2 <= 4 shom_L^{-2} delta_1^2`.

The universal constant is the explicit numeral `4`.  The proof chains the
normalized propagation display above (whose gauge is already `|q|^{-2} =
shom_L^{-1}`) with `E[J(cu_m,p,q;a_L)] >= 0`, the subadditivity chain
`E[J(cu_n,p,q;a_L)] <= E[J(cu_L,p,q;a_L)]` at `L <= n`, and the one-cube bound;
the printed step `shom_{L,*}^{-1}(cu_m) <= 2 shom_L^{-1}` is not used. -/
theorem coefficientCutoffLaw_sq_abs_annealedSigmaStarInvScalarAtScale_sub_le
    (M : ABKModel d) {L n m : ℤ} (hLn : L ≤ n) (hnm : n ≤ m)
    {s : ℝ} (hs : 0 < s) {delta1 : ℝ} (hdelta1 : delta1 ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hmoment : ∫⁻ omega, ENNReal.ofReal
        (Observable.cutoffHomogenizationErrorRepresentative M L L hs
          (Annealed.sigmaBar M L) omega ^ 4)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (delta1 ^ 2))
    {p q : Vec d} (hpq : q = (Annealed.sigmaBar M L : ℝ) • p)
    (hqnorm : vecNormSq q = (Annealed.sigmaBar M L : ℝ)) :
    |annealedSigmaStarInvScalarAtScale M L m -
        annealedSigmaStarInvScalarAtScale M L n| ^ 2 ≤
      4 * ((Annealed.sigmaBar M L : ℝ))⁻¹ ^ 2 * delta1 ^ 2 := by
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M L : ℝ) := (Annealed.sigmaBar M L).property
  have hone :=
    coefficientCutoffLaw_annealedResponseJAtScale_le_of_moment_bound M L hs hdelta1 hmoment
      hpq hqnorm
  have hchain := coefficientCutoffLaw_annealedResponseJAtScale_antitone M L hLn p q
  have hlast := coefficientCutoffLaw_annealedResponseJAtScale_nonneg M L m p q
  have hqpos : 0 < vecNormSq q := by
    rw [hqnorm]
    exact hsigma
  obtain ⟨hnonneg, hgauge⟩ :=
    coefficientCutoffLaw_annealedSigmaStarInvScalarAtScale_sub_le_two_mul_inv_vecNormSq_mul_annealedResponseJAtScale_sub
      M L hnm p hqpos
  rw [hqnorm] at hgauge
  have hinv : (0 : ℝ) < ((Annealed.sigmaBar M L : ℝ))⁻¹ := inv_pos.2 hsigma
  have hdefect : annealedSigmaStarInvScalarAtScale M L n -
      annealedSigmaStarInvScalarAtScale M L m ≤
      2 * ((Annealed.sigmaBar M L : ℝ))⁻¹ * delta1 := by
    have hstep : Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) n p q -
        Ch04.annealedResponseJAtScale (Cutoff.coefficientCutoffLaw M L) m p q ≤ delta1 := by
      linarith
    nlinarith [hgauge, hstep, hinv]
  have habs : |annealedSigmaStarInvScalarAtScale M L m -
      annealedSigmaStarInvScalarAtScale M L n| =
      annealedSigmaStarInvScalarAtScale M L n -
        annealedSigmaStarInvScalarAtScale M L m := by
    rw [abs_sub_comm]
    exact abs_of_nonneg hnonneg
  rw [habs]
  nlinarith [mul_self_le_mul_self hnonneg hdefect]

end

end Algsuperdiff.Section3.Provider.Homogenization
