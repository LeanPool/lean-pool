/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.JResponseApplication
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.BigLambdaSensitivity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.SimplexPartition
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Localization
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# CrudeResponseBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The crude response bounds and the `J -> Lambda` middle of Step 1

This module is the cube/descendant precursor for the middle of Step 1 of
`p.bfA.multiscalebound` (ABK26): the passage from the response `J(., p, 0;
a_L)` and `J(., 0, q; a_L)` at a *fine* carrier to the multiscale gauges
`Lambda_{1/4,2}(z + square_j; a_L)` and `lambda^{-1}_{1/4,2}(z + square_j;
a_L)` of the containing cube, and then to `a_j` through the proved
`Lambda`-half `e.big.Lambda.sensitivity` and the proved `lambda`-transfer of
entry.

The two crude bounds the manuscript uses with an unnamed `C` are

```
J(square, p, 0; a) <= C |p|^2 Lambda_{1/4,2}(square'; a) ,
J(square, 0, q; a) <= C |q|^2 lambda^{-1}_{1/4,2}(square'; a) ,
```

with `square` the fine carrier and `square'` a strictly larger cube.

## Carrier scope: the cube precursor and its downstream simplex transfer

The manuscript applies the two crude bounds at `square = spx`, a **simplex** of
`SW(square_n)` contained in the Whitney cube `z + square_j`.  Every statement
below is at a **triadic descendant cube** `R` of the gauge cube `Q`; this file
itself supplies only that cube-carrier stage.  The distinction is
mathematically substantive:

* `b(.; a)` is not monotone under inclusion of carriers.  Coarse-graining is
  subadditive downwards (`l.subadd.betterer`: `bfA(V) <= sum_i (|U_i|/|V|)
  bfA(U_i)`), so a single fine carrier's `b` is *not* bounded by the coarse
  carrier's `b`, and in particular `|b(spx; a)|` is not bounded by
  `|b(supportCube(spx); a)|`.
* `Lambda_{s,q}(Q; a)` is built from `|b(z + square_k; a)|` over triadic
  **cubes** only (definition (2.23)), so the only carriers it controls are
  triadic descendants.
* The route from cubes to the source simplex is a triadic Whitney decomposition of the
  open simplex into countably many disjoint triadic cubes `R_i` of scales
  `k_i` filling it up to a null set, followed by `l.subadd.betterer` at that
  dissection and the summability of `sum_i (|R_i|/|spx|) 3^{2 s (j - k_i)}`
  (convergent for `s < 1/2`, hence at `s = 1/4`).  That decomposition and its
  counting estimate are now proved downstream in `SimplexDissection.lean` and
  consumed by `SimplexResponseBound.lean`; they are not part of the declarations
  in this cube-only file.

states that "the tex's step is recovered by supplying that depth bound".  This
file proves the *scale* estimate for the local cube problem (the depth of `spx`
inside `z + square_j` is `1 + h_{k+1} - h_k`, a `b`-only bound) but not the
*shape* half (a simplex is not a triadic descendant).  The final section below
proves the scale half at the support cube of a cell of `SW(square_m)`, which is
a triadic descendant of the Whitney cube at precisely the printed depth
(`Whitney.mem_whitneySimplexCells_iff`,
`Whitney.toNat_scale_sub_simplexScale`).  The downstream simplex files provide
the shape transfer, without changing the local scope of the theorems here or
conferring graph-node status.

## What the two assembled legs are

* the `p̂` leg: the crude `Lambda`-bound at `a_L`, then
  `e.big.Lambda.sensitivity` at the cube — the proved
  `LambdaSq_quarter_le_of_notMem_bad_ae` of `BigLambdaSensitivity.lean`, whose
  smallness gate is already discharged on `not B_osc and not B_loc`;
* Reading is the one used: the leg is produced at `a_L` by the polarization
  display and transferred to `a_j` here, exactly as the entry's adopted
  correction prescribes.

The remaining two arrows of Step 1 — the `not B_loc` reduction of the two
gauges at `a_j` to `10 sigmabar_j^{\pm 1}` and the running-diffusivity
comparison — are outside this module: the second is proved in
`JResponseApplication.lean` (`sigmaBar_le_four_mul_rpow_mul_sigmaBar`,
`sigmaBar_le_four_mul_sigmaBar`), and the `lambda`-half of the first is proved
in `JSmallness.lean`
(`sigmaBar_le_ten_mul_cubeLowerEllipticity_of_notMem_badLoc`).

## Main results

* `responseJ_zero_flux_le_coarseBMatrixNorm`,
  `responseJ_zero_slope_le_coarseSigmaStarInvMatrixNorm`: the one-cube Rayleigh
  form of the two pure legs.
* `responseJ_zero_flux_le_LambdaSq_of_mem_descendantsAtScale`,
  `responseJ_zero_slope_le_lambdaSq_inv_of_mem_descendantsAtScale`: **the crude
  response bounds**, at a triadic descendant, with the explicit depth constant.

## References

* ABK26 (`p.bfA.multiscalebound`, Step 1).
* ABK26, `e.J.by.means.of.bfA`, the definitions (2.22)--(2.23),
  `e.ellipticities.monotone.ordered`, `e.bound.one.cube.by.lambdas`.
* ABK26, `e.big.Lambda.sensitivity` (`e.SW.def`).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-! ## The one-cube Rayleigh form of the two pure legs -/

/-- **The pure-potential leg at one cube.**  Combining the identity
`2 J(U, p, 0; a) = p . b(U; a) p` of `e.J.by.means.of.bfA` with the Euclidean
Rayleigh cap gives

```
J(z + square_k, p, 0; a) <= (1/2) |b(z + square_k; a)| |p|^2 .
```

No positivity of `b` is used: the Rayleigh cap is applied through the absolute
value. -/
theorem responseJ_zero_flux_le_coarseBMatrixNorm (R : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) (p : Vec d) :
    Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R) p 0 ≤
      1 / 2 * Ch02.coarseBMatrixNorm R a * vecNormSq p := by
  have hid := blockVecDot_coarseBlockMatrix_pure_potential (Ch02.cubeDomain R)
    (a.coeffOn R) p
  have hquad : blockVecDot ((p, 0) : BlockVec d)
      (blockMatVecMul (Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (a.coeffOn R))
        (p, 0)) =
      vecDot p (matVecMul (Ch02.bCoarse (Ch02.cubeDomain R) (a.coeffOn R)) p) := by
    simp [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left]
  have hray := Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq
    (Ch02.bCoarse (Ch02.cubeDomain R) (a.coeffOn R)) p
  have hnorm : Ch02.matrixOperatorNorm
      (Ch02.bCoarse (Ch02.cubeDomain R) (a.coeffOn R)) =
      Ch02.coarseBMatrixNorm R a := rfl
  rw [hnorm] at hray
  rw [hquad] at hid
  have habs := le_abs_self
    (vecDot p (matVecMul (Ch02.bCoarse (Ch02.cubeDomain R) (a.coeffOn R)) p))
  linarith [hray, hid, habs]

/-- **The pure-flux leg at one cube.**  The mirror of
`responseJ_zero_flux_le_coarseBMatrixNorm` through
`2 J(U, 0, q; a) = q . sigma_*^{-1}(U; a) q`:

```
J(z + square_k, 0, q; a) <= (1/2) |sigma_*^{-1}(z + square_k; a)| |q|^2 .
```
-/
theorem responseJ_zero_slope_le_coarseSigmaStarInvMatrixNorm (R : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) (q : Vec d) :
    Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R) 0 q ≤
      1 / 2 * Ch02.coarseSigmaStarInvMatrixNorm R a * vecNormSq q := by
  have hid := blockVecDot_coarseBlockMatrix_pure_flux (Ch02.cubeDomain R)
    (a.coeffOn R) q
  have hquad : blockVecDot ((0, q) : BlockVec d)
      (blockMatVecMul (Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (a.coeffOn R))
        (0, q)) =
      vecDot q
        (matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) (a.coeffOn R)) q) := by
    simp [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left]
  have hray := Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq
    (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) (a.coeffOn R)) q
  have hnorm : Ch02.matrixOperatorNorm
      (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) (a.coeffOn R)) =
      Ch02.coarseSigmaStarInvMatrixNorm R a := rfl
  rw [hnorm] at hray
  rw [hquad] at hid
  have habs := le_abs_self
    (vecDot q
      (matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) (a.coeffOn R)) q))
  linarith [hray, hid, habs]

/-! ## The crude response bounds at a triadic descendant -/

/-- The second inequality of `e.ellipticities.monotone.ordered` at both admissible
exponent branches, in the form this module consumes. -/
private theorem coarseSigmaStarInvMatrixNorm_le_lambdaSq_inv [NeZero d]
    (R : TriadicCube d) (a : Ch02.TriadicCoeffFamily d) {s : ℝ}
    {qe : Ch02.MultiscaleExponent} (hs : 0 < s) (hq : qe.IsAdmissible) :
    Ch02.coarseSigmaStarInvMatrixNorm R a ≤ (Ch02.lambdaSq R s qe a)⁻¹ := by
  cases qe with
  | finite q =>
      exact Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv R a hs (by simpa using hq)
  | infinity =>
      exact Ch02.oneCube_sigmaStarInv_le_lambdaSq_infinity_inv R a hs

/-- The scale weight `3^{2s(m-k)}` of `e.bound.one.cube.by.lambdas` is
nonnegative. -/
theorem multiscaleDescendantWeight_nonneg (Q : TriadicCube d) (k : ℤ) (s : ℝ) :
    0 ≤ Ch02.multiscaleDescendantWeight Q k s :=
  Real.rpow_nonneg (by norm_num) _


/-- For every triadic descendant `R` of `Q` at scale `k`, every `s > 0` and every
admissible exponent,

```
J(R, p, 0; a)  <=  (1/2) . 3^{2 s (Q.scale - k)} . Lambda_{s,q}(Q; a) . |p|^2 .
```

The constant is explicit and grows by `3^{2s}` per triadic generation of depth;
it is `1/2` at `k = Q.scale`.  See the module header for the downstream
simplex-dissection route that transports this cube estimate to the manuscript's
carrier. -/
theorem responseJ_zero_flux_le_LambdaSq_of_mem_descendantsAtScale [NeZero d]
    {Q R : TriadicCube d} {k : ℤ} (a : Ch02.TriadicCoeffFamily d) {s : ℝ}
    {qe : Ch02.MultiscaleExponent} (hR : R ∈ descendantsAtScale Q k) (hs : 0 < s)
    (hq : qe.IsAdmissible) (p : Vec d) :
    Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R) p 0 ≤
      1 / 2 * (Ch02.multiscaleDescendantWeight Q k s * Ch02.LambdaSq Q s qe a) *
        vecNormSq p := by
  have hbase := responseJ_zero_flux_le_coarseBMatrixNorm R a p
  have hone : Ch02.coarseBMatrixNorm R a ≤ Ch02.LambdaSq R s qe a :=
    Ch02.oneCube_b_le_LambdaSq R a hs hq
  have hdesc : Ch02.LambdaSq R s qe a ≤
      Ch02.multiscaleDescendantWeight Q k s * Ch02.LambdaSq Q s qe a :=
    Ch02.descendant_LambdaSq_le a hR hs hq
  have hnp : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  refine hbase.trans ?_
  have hchain := hone.trans hdesc
  nlinarith [hnp, hchain]

/-- For every triadic descendant `R` of `Q` at scale `k`,

```
J(R, 0, q; a)  <=  (1/2) . 3^{2 s (Q.scale - k)} . lambda^{-1}_{s,q}(Q; a) . |q|^2 .
```
-/
theorem responseJ_zero_slope_le_lambdaSq_inv_of_mem_descendantsAtScale [NeZero d]
    {Q R : TriadicCube d} {k : ℤ} (a : Ch02.TriadicCoeffFamily d) {s : ℝ}
    {qe : Ch02.MultiscaleExponent} (hR : R ∈ descendantsAtScale Q k) (hs : 0 < s)
    (hq : qe.IsAdmissible) (q : Vec d) :
    Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R) 0 q ≤
      1 / 2 * (Ch02.multiscaleDescendantWeight Q k s * (Ch02.lambdaSq Q s qe a)⁻¹) *
        vecNormSq q := by
  have hbase := responseJ_zero_slope_le_coarseSigmaStarInvMatrixNorm R a q
  have hone : Ch02.coarseSigmaStarInvMatrixNorm R a ≤ (Ch02.lambdaSq R s qe a)⁻¹ :=
    coarseSigmaStarInvMatrixNorm_le_lambdaSq_inv R a hs hq
  have hdesc : (Ch02.lambdaSq R s qe a)⁻¹ ≤
      Ch02.multiscaleDescendantWeight Q k s * (Ch02.lambdaSq Q s qe a)⁻¹ :=
    Ch02.descendant_lambdaSq_inv_le a hR hs hq
  have hnq : (0 : ℝ) ≤ vecNormSq q := vecNormSq_nonneg q
  refine hbase.trans ?_
  have hchain := hone.trans hdesc
  nlinarith [hnq, hchain]


/-! ## The two legs of Step 1 on the bad-event complement -/


/-! ## The depth of a cell of `SW(square_m)` inside its Whitney cube -/


end

end Algsuperdiff.Section3.Provider.Multiscale
