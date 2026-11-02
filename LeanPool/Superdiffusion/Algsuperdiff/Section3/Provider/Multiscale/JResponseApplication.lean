/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.LambdaSensitivityTwin
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.BlockCoarseMatrix

/-!
# JResponseApplication

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The good-carrier matrix estimate: the two deterministic legs of Step 1

This module supplies the two carrier-free ingredients of
the `J`-response application of `p.bfA.multiscalebound` (ABK26):

2. the **running-diffusivity comparison**, `sigmabar_{n-1} sigmabar_j^{-1}
   <=^{gamma(n-1-j)}` and `sigmabar_j sigmabar_{n-1}^{-1} <= C`, with `C = 4`
   explicit.

## Local scope and downstream carrier transfer

The manuscript's Step 1 runs on a simplex `spx` of the Whitney simplex
partition `SW(square_n)`.  This historical precursor does not itself construct
that partition; both ingredients here are stated at the carrier-independent
level at which the manuscript's argument uses them:

* the polarization split is proved for an **arbitrary** `Ch02.Domain d` — the
  bounded convex open carrier class of `e.J.by.means.of.bfA`, which contains
  cubes and simplices — so it applies without a new constant;
* the running-diffusivity comparison is a statement about `sigmabar` alone and
  carries no carrier.

The middle of Step 1 — the passage from `J(spx, .; a_L)` to `Lambda_{1/4,2}(z + square_j;
  a_L)` — begins in `CrudeResponseBound.lean` at the cube/descendant carrier. Thus the
declarations below remain local providers, not a source-node closure.

## The base case is not consumed

The node's dependency list names `p.base.case`, because it cites `e.basecase.diffusivity`
"if `n
- 1 < mstar`".  In the frozen Lean rendering the citation is **redundant**:
`Algsuperdiff.Frozen.Section3.inductionState M m0 E` transcribes
`d.mathcalS.def` verbatim, and `e.shom.h.bounds` there is asserted "for every
`m` in `Z` with `m <= m0`" — with no lower bound.  Both scales used, namely `n
- 1` and `j = n - k - h_k <= n - 1`, are below `m0 = m - 1`, so the two-sided
  `sigmabar` clause of the induction state alone proves both ratios.
  Consequently the frozen `draft_sorry` `base_case` is **not** consumed, and no
  source-shaped A binder for it appears below.

## Main results

* `blockVecDot_coarseBlockMatrix_pure_potential`,
  `blockVecDot_coarseBlockMatrix_pure_flux`: each pure leg of the block
  quadratic form is twice the corresponding response.
* `blockVecDot_coarseBlockMatrix_le_four_responseJ_add`: **the polarization
  split**, at an arbitrary domain.
* `sigmaBar_le_four_mul_rpow_mul_sigmaBar`, `sigmaBar_le_four_mul_sigmaBar`:
  **the running-diffusivity comparison**, with `C = 4`.

## References

* ABK26 (`p.bfA.multiscalebound`, Step 1).
* ABK26, `e.J.by.means.of.bfA`.
* ABK26, `d.mathcalS.def`, `e.shom.h.bounds`.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The polarization split of `e.J.by.means.of.bfA` -/

/-- Expanding the doubled quadratic form of a block matrix on the four loads
`(x, y)`, `(x, -y)`, `(x, 0)`, `(0, y)`.  Only bilinearity is used: no symmetry
and no positivity of the block matrix. -/
private theorem blockVecDot_blockMatVecMul_parallelogram (A : BlockMat d)
    (x y : Vec d) :
    blockVecDot (x, y) (blockMatVecMul A (x, y)) +
        blockVecDot (x, -y) (blockMatVecMul A (x, -y)) =
      2 * blockVecDot (x, 0) (blockMatVecMul A (x, 0)) +
        2 * blockVecDot (0, y) (blockMatVecMul A (0, y)) := by
  simp only [blockVecDot, blockMatVecMul, matVecMul_neg,
    matVecMul_zero, vecDot_add_right, vecDot_neg_left, vecDot_neg_right,
    vecDot_zero_left, add_zero, zero_add]
  ring

/-- Flipping the sign of the potential slot leaves the pure-potential quadratic
form unchanged. -/
private theorem blockVecDot_blockMatVecMul_neg_fst (A : BlockMat d) (x : Vec d) :
    blockVecDot (-x, 0) (blockMatVecMul A (-x, 0)) =
      blockVecDot (x, 0) (blockMatVecMul A (x, 0)) := by
  simp only [blockVecDot, blockMatVecMul, matVecMul_neg, matVecMul_zero,
    vecDot_neg_left, vecDot_neg_right, vecDot_zero_left, add_zero, neg_neg,
    neg_zero]

/-- **The pure-potential leg of `e.J.by.means.of.bfA`**: on the load `(p, 0)` the
`bfA(U; a)` quadratic form is `2 J(U, p, 0; a)`.  The cross term `- p . q` is
invisible at this loading. -/
theorem blockVecDot_coarseBlockMatrix_pure_potential (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (p : Vec d) :
    blockVecDot (p, 0) (blockMatVecMul (Ch02.coarseBlockMatrix U a) (p, 0)) =
      2 * Ch02.responseJ U a p 0 := by
  have h := HCPolySupport.Internal.Ch02.BookCh02.responseJ_eq_block_quadratic U a
    p 0
  rw [blockVecDot_blockMatVecMul_neg_fst (Ch02.coarseBlockMatrix U a) p] at h
  rw [h, vecDot_zero_right]
  ring

/-- **The pure-flux leg of `e.J.by.means.of.bfA`**: on the load `(0, q)` the
`bfA(U; a)` quadratic form is `2 J(U, 0, q; a)`. -/
theorem blockVecDot_coarseBlockMatrix_pure_flux (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (q : Vec d) :
    blockVecDot (0, q) (blockMatVecMul (Ch02.coarseBlockMatrix U a) (0, q)) =
      2 * Ch02.responseJ U a 0 q := by
  have h := HCPolySupport.Internal.Ch02.BookCh02.responseJ_eq_block_quadratic U a
    0 q
  rw [neg_zero] at h
  rw [h, vecDot_zero_left]
  ring

/-- **The polarization split of ABK26**, at an arbitrary bounded convex domain.
For every load `(x, y)` in `R^{2d}`,

```
(x, y) . bfA(U; a) (x, y)  <=  4 ( J(U, x, 0; a) + J(U, 0, y; a) ) .
```

The manuscript writes the left side as `|bfA^{1/2}(U; a) (x, y)|^2`.  The proof
is the parallelogram identity together with the positive definiteness of
`bfA(U; a)` on the residual load `(x, -y)`; the two pure legs are then
`e.J.by.means.of.bfA`.

Applied with `(x, y) = bfAhom_{n-1}^{-1/2} P̂ = (sigmabar_{n-1}^{-1/2} p̂,
sigmabar_{n-1}^{1/2} q̂)`, using that `bfAhom` is the block-diagonal
`diag(sigmabar, sigmabar^{-1})` of `e.homs.defs`, this is the manuscript's
display verbatim. -/
theorem blockVecDot_coarseBlockMatrix_le_four_responseJ_add (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (x y : Vec d) :
    blockVecDot (x, y) (blockMatVecMul (Ch02.coarseBlockMatrix U a) (x, y)) ≤
      4 * (Ch02.responseJ U a x 0 + Ch02.responseJ U a 0 y) := by
  have hpar := blockVecDot_blockMatVecMul_parallelogram
    (Ch02.coarseBlockMatrix U a) x y
  have hpos : 0 ≤ blockVecDot ((x, -y) : BlockVec d)
      (blockMatVecMul (Ch02.coarseBlockMatrix U a) (x, -y)) := by
    by_cases hzero : ((x, -y) : BlockVec d) = 0
    · rw [hzero]
      simp [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left]
    · exact ((Ch02.blockCoarseMatrixTheory U a).block_matrix_posDef _ hzero).le
  rw [blockVecDot_coarseBlockMatrix_pure_potential U a x,
    blockVecDot_coarseBlockMatrix_pure_flux U a y] at hpar
  linarith [hpar, hpos]

/-! ## The running-diffusivity comparison -/

/-- The induction-state envelope `max{cstar gamma^{-1} 3^{2 gamma m}, nu^2}`. -/
noncomputable def sigmaEnvelope (M : ABKModel d) (m : ℤ) : ℝ :=
  max (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))) (M.nu ^ 2)

private theorem sigmaEnvelope_nonneg (M : ABKModel d) (m : ℤ) :
    0 ≤ sigmaEnvelope M m :=
  le_trans (sq_nonneg M.nu) (le_max_right _ _)

/-- The envelope grows by exactly `3^{2 gamma (i - j)}` between scales. -/
private theorem sigmaEnvelope_le_rpow_mul (M : ABKModel d) {i j : ℤ} (hji : j ≤ i) :
    sigmaEnvelope M i ≤
      (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - (j : ℝ))) * sigmaEnvelope M j := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - (j : ℝ))) := by
    refine Real.one_le_rpow (by norm_num) ?_
    have : (0 : ℝ) ≤ (i : ℝ) - (j : ℝ) := by
      have := (Int.cast_le (R := ℝ)).2 hji
      linarith
    positivity
  have hsplit : (3 : ℝ) ^ (2 * M.gamma * (i : ℝ)) =
      (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - (j : ℝ))) *
        (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  have hcstar : 0 ≤ Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ :=
    mul_nonneg (Algsuperdiff.Section3.Disorder.cstar_characterization M).1.le
      (inv_nonneg.2 hgamma.le)
  refine max_le ?_ ?_
  · have hA : Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * M.gamma * (i : ℝ)) =
      (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - (j : ℝ))) *
        (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
          (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) := by
      rw [hsplit]; ring
    rw [hA]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _)
      (le_trans zero_le_one hone)
  · calc (M.nu ^ 2 : ℝ) ≤ sigmaEnvelope M j := le_max_right _ _
      _ = 1 * sigmaEnvelope M j := (one_mul _).symm
      _ ≤ (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - (j : ℝ))) * sigmaEnvelope M j :=
          mul_le_mul_of_nonneg_right hone (sigmaEnvelope_nonneg M j)

/-- **The first running-diffusivity comparison of ABK26**, with the constant `C
= 4` explicit:

```
sigmabar_i  <=  4 . 3^{gamma (i - j)} . sigmabar_j     for  j <= i <= m0 .
```

Only the two-sided clause `e.shom.h.bounds` of the induction state is used;
see the module header on why `p.base.case` is not needed. -/
theorem sigmaBar_le_four_mul_rpow_mul_sigmaBar (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) {i j : ℤ}
    (hji : j ≤ i) (hi : i ≤ m0) :
    (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) ≤
      4 * (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (j : ℝ))) *
        (Algsuperdiff.Section3.Annealed.sigmaBar M j : ℝ) := by
  have hj : j ≤ m0 := le_trans hji hi
  have hposi : (0 : ℝ) < (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar M i).2
  have hposj : (0 : ℝ) < (Algsuperdiff.Section3.Annealed.sigmaBar M j : ℝ) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar M j).2
  have hupper : (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) ^ 2 ≤
      4 * sigmaEnvelope M i := (hS.1 i hi).2
  have hlower : (1 / 4 : ℝ) * sigmaEnvelope M j ≤
      (Algsuperdiff.Section3.Annealed.sigmaBar M j : ℝ) ^ 2 := (hS.1 j hj).1
  have henv := sigmaEnvelope_le_rpow_mul M hji
  set s : ℝ := (3 : ℝ) ^ (M.gamma * ((i : ℝ) - (j : ℝ))) with hs
  have hspos : 0 < s := Real.rpow_pos_of_pos (by norm_num) _
  have hssq : s ^ 2 = (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - (j : ℝ))) := by
    rw [hs, ← Real.rpow_natCast ((3 : ℝ) ^ (M.gamma * ((i : ℝ) - (j : ℝ)))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
    ring_nf
  have hsq : (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) ^ 2 ≤
      (4 * s * (Algsuperdiff.Section3.Annealed.sigmaBar M j : ℝ)) ^ 2 := by
    have hstep : (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) ^ 2 ≤
        4 * (s ^ 2 * sigmaEnvelope M j) := by
      refine hupper.trans ?_
      rw [hssq]
      exact mul_le_mul_of_nonneg_left henv (by norm_num)
    nlinarith [hstep, hlower, sq_nonneg s, hspos]
  have hrhs : 0 ≤ 4 * s * (Algsuperdiff.Section3.Annealed.sigmaBar M j : ℝ) := by
    positivity
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hposi.le, Real.sqrt_sq hrhs] at this

/-- **The second running-diffusivity comparison of ABK26**, with the constant `C
= 4` explicit:

```
sigmabar_j  <=  4 sigmabar_i      for  j <= i <= m0 .
```
-/
theorem sigmaBar_le_four_mul_sigmaBar (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) {i j : ℤ}
    (hji : j ≤ i) (hi : i ≤ m0) :
    (Algsuperdiff.Section3.Annealed.sigmaBar M j : ℝ) ≤
      4 * (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) := by
  have hj : j ≤ m0 := le_trans hji hi
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hposi : (0 : ℝ) < (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar M i).2
  have hposj : (0 : ℝ) < (Algsuperdiff.Section3.Annealed.sigmaBar M j : ℝ) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar M j).2
  have hupper : (Algsuperdiff.Section3.Annealed.sigmaBar M j : ℝ) ^ 2 ≤
      4 * sigmaEnvelope M j := (hS.1 j hj).2
  have hlower : (1 / 4 : ℝ) * sigmaEnvelope M i ≤
      (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) ^ 2 := (hS.1 i hi).1
  have hcstar : 0 ≤ Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ :=
    mul_nonneg (Algsuperdiff.Section3.Disorder.cstar_characterization M).1.le
      (inv_nonneg.2 hgamma.le)
  have hmono : sigmaEnvelope M j ≤ sigmaEnvelope M i := by
    refine max_le ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_left _ _)
    refine mul_le_mul_of_nonneg_left ?_ hcstar
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hcast : (j : ℝ) ≤ (i : ℝ) := (Int.cast_le (R := ℝ)).2 hji
    have h2g : (0 : ℝ) < 2 * M.gamma := by linarith
    exact mul_le_mul_of_nonneg_left hcast h2g.le
  have hsq : (Algsuperdiff.Section3.Annealed.sigmaBar M j : ℝ) ^ 2 ≤
      (4 * (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ)) ^ 2 := by
    nlinarith [hupper, hlower, hmono]
  have hrhs : 0 ≤ 4 * (Algsuperdiff.Section3.Annealed.sigmaBar M i : ℝ) := by
    positivity
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hposj.le, Real.sqrt_sq hrhs] at this

end

end Algsuperdiff.Section3.Provider.Multiscale
