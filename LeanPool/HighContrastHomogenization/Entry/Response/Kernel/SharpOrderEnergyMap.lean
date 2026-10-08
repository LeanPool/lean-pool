/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentScaleEnergyRoute

/-!
# High-contrast homogenization: Entry.Response.Kernel.SharpOrderEnergyMap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The sharp-order layer of the coarse energy map

Given the extra hypothesis ordering the primal and adjoint coarse blocks, this file sharpens the
coarse energy-map comparison of the diagonal weak-norm estimate: it bounds the Loewner order of the
recentred block by a scalar multiple of the sharp companion `swapSharp`, transports that bound
through the block congruence, and records the monotonicity, block-diagonal form and scalar action
of `swapSharp` these steps use.  These are the sharp-order steps of the response-transfer
proposition `p.response.transfer`.
-/

section
/-!
## The sharp (primal-adjoint) order layer: the hypothesis `hcmp` supplied

Nothing here restates or weakens any existing declaration, and the target
`diagonalWeakNorm_primal_le` in `DiagonalWeakNormBound.lean` is untouched.

## Why this module exists

The energy-map comparison `energy_map_congr_le` in
`RecentScaleEnergyRoute.lean` has a shared root for two consumers, and what both
consumers still share is exactly one hypothesis: its `hcmp`, the form used here of
`diagonalMetric_le_scaled_coarseStarred_adaptedCellAtCenter`.  That hypothesis is supplied here,
and the comparison is discharged with it.

## The design decision, and why no definition is introduced

Two routes encode the same comparison.  The first goes through
`blockSharp`, `fullBlockSharp`, `relSize`, `blockSize`, `diagonalWeakMetricFactor`,
`metricBlockNormSq`, `adaptedResponse` and `adaptedDomainAt`: eight new definitions, all
currently zero declarations in this development.  The second expresses the comparison through
the carriers already present, and this module takes it.

**This module introduces no definition at all.**  Every declaration below is a `theorem`, so no
satisfiability obligation arises from a definition.  The two substantive hypotheses that do
carry content — positive definiteness and sharp self-duality of the reference block — are
hypotheses of theorems, and their satisfiability is nevertheless proved outright, in this module
and before the consumer statements that use them: the witness `R = M_0(F)^{1/2}` that the
consumers actually print is exhibited as an explicit `∃`.

The three encodings needed and already available:

* `fullBlockSharp H = 𝐑 H⁻¹ 𝐑` is written out as the literal product
  `toFullBlockMat (blockSwap d) * H⁻¹ * toFullBlockMat (blockSwap d)`; `blockSwap`
  (`Setup/ProjectiveDistance.lean`) is `Book.Ch02.blockR`, that is `fullBlockRefl`, on the nose;
* `relSize P Q = ‖matSqrt Q⁻¹ * P * matSqrt Q⁻¹‖` is definitionally
  `‖toFullBlockMat (normalizedBlock P Q)‖` (`Setup/ProjectiveDistance.lean`);
* `blockSharp (coarseBlockMatrix U a) = coarseStarredBlockMatrix U a`, which needs no
  positivity at all because `𝐑` is an involution.

## Two simplifications of the route

1. The sharp comparison replaces the sizes `E` against `M` and `A` against `E` by arbitrary
  positive `k` and `e` carrying only the two Loewner inequalities the proof uses.  That is
  strictly more general, and it is the shape a consumer has: consumers own bounds on the two
  sizes, not their exact values.  A separate size step recovers the exact-size instance when a
  consumer wants it.
2. The self-duality step goes through `blockMatInv_metric_eq_blockReflect`; here it is done as
  the direct `2 × 2` block computation, so that lemma is not needed.

The route below is proved directly on the carriers of this development and of `CoarseGraining`;
nothing is imported from any other development and no file is copied.
-/

open HCPolySupport.HighContrast (blockScale matSqrt matSqrt_spec normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open HCPolySupport.Book.Ch02

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The reflection and the sharp map on the flattened carrier -/

/-- **The flattened reflection is its own transpose.** -/
theorem transpose_swapFull (d : ℕ) :
    (toFullBlockMat (blockSwap d))ᵀ = toFullBlockMat (blockSwap d) := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using!
    (Analysis.toFullBlockMat_isHermitian_iff (blockSwap d)).2
      (Analysis.isSymmetricBlockMat_blockSwap d)

/-- **The flattened reflection is its own inverse.** -/
theorem inv_swapFull (d : ℕ) :
    (toFullBlockMat (blockSwap d))⁻¹ = toFullBlockMat (blockSwap d) :=
  Matrix.inv_eq_right_inv (Analysis.toFullBlockMat_blockSwap_mul_self d)

/-- **The sharp map reverses the Loewner order.** -/
theorem swapSharp_antitone {X Y : FullBlockMat d} (hX : X.PosDef) (hY : Y.PosDef)
    (hXY : X ≤ Y) :
    toFullBlockMat (blockSwap d) * Y⁻¹ * toFullBlockMat (blockSwap d) ≤
      toFullBlockMat (blockSwap d) * X⁻¹ * toFullBlockMat (blockSwap d) := by
  have hinv : Y⁻¹ ≤ X⁻¹ := inv_le_inv_of_le hX hY hXY
  simpa only [transpose_swapFull] using
    Analysis.matrix_congr_le hinv (toFullBlockMat (blockSwap d))

/-- **The sharp map is homogeneous of degree minus one.** -/
theorem swapSharp_smul {X : FullBlockMat d} (hX : X.PosDef) {c : ℝ} (hc : 0 < c) :
    toFullBlockMat (blockSwap d) * (c • X)⁻¹ * toFullBlockMat (blockSwap d) =
      c⁻¹ • (toFullBlockMat (blockSwap d) * X⁻¹ * toFullBlockMat (blockSwap d)) := by
  rw [inv_smul_of_isUnit hc.ne' ((Matrix.isUnit_iff_isUnit_det X).mp hX.isUnit),
    Matrix.mul_smul, Matrix.smul_mul]

/-- **Dilation by a nonnegative scalar is monotone for the Loewner order.** -/
theorem matrix_smul_le_smul {X Y : FullBlockMat d} {c : ℝ} (hc : 0 ≤ c) (h : X ≤ Y) :
    c • X ≤ c • Y := by
  refine Matrix.le_iff.mpr ?_
  have hrw : c • Y - c • X = c • (Y - X) := (smul_sub c Y X).symm
  rw [hrw]
  exact (Matrix.le_iff.mp h).smul hc

/-! ## The two-step sharp comparison -/

/-- **The sharp comparison.**  If the reference block `M` is its own sharp, then two
Loewner comparisons `E ≤ k M` and `A ≤ e E` reverse under the sharp involution into a single
comparison of `M` against the sharp of `A`:

`M ≤ (k e) · 𝐑 A⁻¹ 𝐑`.

The sizes `E` against `M` and `A` against `E` are replaced by arbitrary positive `k` and `e`
carrying only the two inequalities the proof actually uses.  That is strictly more general than
fixing those sizes, and it is the shape a consumer has: consumers carry bounds on the two sizes,
not their exact values. -/
theorem le_smul_swapSharp {M E A : FullBlockMat d} (hM : M.PosDef) (hE : E.PosDef)
    (hA : A.PosDef)
    (hMsharp : toFullBlockMat (blockSwap d) * M⁻¹ * toFullBlockMat (blockSwap d) = M)
    {k e : ℝ} (hk : 0 < k) (he : 0 < e) (hEM : E ≤ k • M) (hAE : A ≤ e • E) :
    M ≤ (k * e) • (toFullBlockMat (blockSwap d) * A⁻¹ * toFullBlockMat (blockSwap d)) := by
  have hsharpEM : k⁻¹ • M ≤
      toFullBlockMat (blockSwap d) * E⁻¹ * toFullBlockMat (blockSwap d) := by
    have h := swapSharp_antitone hE (hM.smul hk) hEM
    rwa [swapSharp_smul hM hk, hMsharp] at h
  have hMsharpE : M ≤ k • (toFullBlockMat (blockSwap d) * E⁻¹ * toFullBlockMat (blockSwap d)) := by
    have h := matrix_smul_le_smul hk.le hsharpEM
    rwa [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] at h
  have hsharpAE : e⁻¹ • (toFullBlockMat (blockSwap d) * E⁻¹ * toFullBlockMat (blockSwap d)) ≤
      toFullBlockMat (blockSwap d) * A⁻¹ * toFullBlockMat (blockSwap d) := by
    have h := swapSharp_antitone hA (hE.smul he) hAE
    rwa [swapSharp_smul hE he] at h
  have hEsharpA : toFullBlockMat (blockSwap d) * E⁻¹ * toFullBlockMat (blockSwap d) ≤
      e • (toFullBlockMat (blockSwap d) * A⁻¹ * toFullBlockMat (blockSwap d)) := by
    have h := matrix_smul_le_smul he.le hsharpAE
    rwa [smul_smul, mul_inv_cancel₀ he.ne', one_smul] at h
  have hscaled := matrix_smul_le_smul hk.le hEsharpA
  rw [smul_smul] at hscaled
  exact hMsharpE.trans hscaled

/-! ## The starred coarse block is the sharp of the coarse block -/

/-- **The starred coarse block.**  On the flattened carrier the Chapter 2 starred coarse
response `𝐀_*(U;a)` is the sharp of the ordinary coarse response, `𝐑 𝐀(U;a)⁻¹ 𝐑`.

The route needs no positivity at all: `𝐑` is an involution, so `(𝐑 X 𝐑)⁻¹ = 𝐑 X⁻¹ 𝐑`
unconditionally. -/
theorem toFullBlockMat_coarseStarred (U : Domain d) (a : CoeffOn U) :
    toFullBlockMat (Book.Ch02.coarseStarredBlockMatrix U a) =
      toFullBlockMat (blockSwap d) *
        (toFullBlockMat (Book.Ch02.coarseBlockMatrix U a))⁻¹ *
        toFullBlockMat (blockSwap d) := by
  have hrefl : toFullBlockMat (blockReflect (Book.Ch02.coarseBlockMatrix U a)) =
      toFullBlockMat (blockSwap d) * toFullBlockMat (Book.Ch02.coarseBlockMatrix U a) *
        toFullBlockMat (blockSwap d) := by
    have h := congrArg toFullBlockMat
      (Analysis.swapConj_eq_blockReflect (Book.Ch02.coarseBlockMatrix U a))
    rw [toFullBlockMat_ofFullBlockMat] at h
    exact h.symm
  rw [Book.Ch02.coarseStarredBlockMatrix,
    (Book.Ch02.blockCoarseMatrixTheory U a).starred_inverse_formula,
    Book.Ch02.blockMatInv, toFullBlockMat_ofFullBlockMat, hrefl,
    Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_swapFull]
  noncomm_ring

/-! ## The relative size, on the `normalizedBlock` carrier -/

/-- **The size step.**  A block is dominated by its reference, dilated by the operator norm of
the `Q`-normalized block:

`P ≤ |Q^{-1/2} P Q^{-1/2}| · Q`.

No new definition is needed for the relative size: `toFullBlockMat (normalizedBlock P Q)`
unfolds to exactly `matSqrt Q⁻¹ * P * matSqrt Q⁻¹`, so
`‖toFullBlockMat (normalizedBlock P Q)‖` is `‖matSqrt Q⁻¹ * P * matSqrt Q⁻¹‖` on the flattened
carrier.  The proof is one observation: conjugation by `Q^{-1/2}` is a congruence sending `Q`
to `1`, and the spectral norm reads a bound against `1` off directly. -/
theorem le_smul_of_normalizedBlock {P Q : BlockMat d}
    (hP : (toFullBlockMat P).PosSemidef) (hQ : (toFullBlockMat Q).PosDef) :
    toFullBlockMat P ≤
      ‖toFullBlockMat (normalizedBlock P Q)‖ • toFullBlockMat Q := by
  have hSsymm : (matSqrt (toFullBlockMat Q))ᵀ = matSqrt (toFullBlockMat Q) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using!
      (matSqrt_spec hQ.posSemidef).1.isHermitian
  have hSIsymm : (matSqrt (toFullBlockMat Q)⁻¹)ᵀ = matSqrt (toFullBlockMat Q)⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using!
      (matSqrt_spec hQ.inv.posSemidef).1.isHermitian
  have hSS : matSqrt (toFullBlockMat Q) * matSqrt (toFullBlockMat Q) = toFullBlockMat Q :=
    (matSqrt_spec hQ.posSemidef).2
  have hSSI : matSqrt (toFullBlockMat Q) * matSqrt (toFullBlockMat Q)⁻¹ = 1 :=
    HCPolySupport.HighContrast.matSqrt_mul_matSqrt_inv hQ
  have hSIS : matSqrt (toFullBlockMat Q)⁻¹ * matSqrt (toFullBlockMat Q) = 1 :=
    HCPolySupport.HighContrast.matSqrt_inv_mul_matSqrt hQ
  have hN : toFullBlockMat (normalizedBlock P Q) =
      matSqrt (toFullBlockMat Q)⁻¹ * toFullBlockMat P * matSqrt (toFullBlockMat Q)⁻¹ := by
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
  have hNpsd : (toFullBlockMat (normalizedBlock P Q)).PosSemidef := by
    have h := hP.conjTranspose_mul_mul_same (B := matSqrt (toFullBlockMat Q)⁻¹)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hSIsymm] at h
    rwa [hN]
  have hone := GeometricMean.le_smul_one_of_norm_le hNpsd (le_refl ‖toFullBlockMat
    (normalizedBlock P Q)‖)
  have hcongr := Analysis.matrix_congr_le hone (matSqrt (toFullBlockMat Q))
  rw [hSsymm] at hcongr
  have hleft : matSqrt (toFullBlockMat Q) * toFullBlockMat (normalizedBlock P Q) *
      matSqrt (toFullBlockMat Q) = toFullBlockMat P := by
    rw [hN]
    calc
      matSqrt (toFullBlockMat Q) *
            (matSqrt (toFullBlockMat Q)⁻¹ * toFullBlockMat P * matSqrt (toFullBlockMat Q)⁻¹) *
            matSqrt (toFullBlockMat Q)
          = matSqrt (toFullBlockMat Q) * matSqrt (toFullBlockMat Q)⁻¹ * toFullBlockMat P *
            (matSqrt (toFullBlockMat Q)⁻¹ * matSqrt (toFullBlockMat Q)) := by noncomm_ring
      _ = toFullBlockMat P := by rw [hSSI, hSIS, Matrix.one_mul, Matrix.mul_one]
  have hright : matSqrt (toFullBlockMat Q) *
      (‖toFullBlockMat (normalizedBlock P Q)‖ • (1 : FullBlockMat d)) *
      matSqrt (toFullBlockMat Q) =
      ‖toFullBlockMat (normalizedBlock P Q)‖ • toFullBlockMat Q := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hSS]
  rwa [hleft, hright] at hcongr

/-! ## The hypothesis `hcmp`, supplied -/

/-- **`hcmp`, in general form.**  The reference block `M`, self-dual under the sharp
involution, is dominated by the starred coarse response of `(U; a)`, dilated by the product of
the two size constants.

This is the hypothesis `hcmp` of the energy-map comparison, the form used here of
`diagonalMetric_le_scaled_coarseStarred_adaptedCellAtCenter`.  Route: the sharp comparison on the
flattened carrier, then the identification of `𝐑 𝐀⁻¹ 𝐑` with `𝐀_*`, then
`blockMatLoewnerLE_of_le` back into the block dialect.  No new definition is introduced, and
no sharp involution is named in the statement. -/
theorem blockLoewner_le_smul_coarseStarred {U : Domain d} (a : CoeffOn U) {M E : BlockMat d}
    (hM : (toFullBlockMat M).PosDef)
    (hMsharp : toFullBlockMat (blockSwap d) * (toFullBlockMat M)⁻¹ *
      toFullBlockMat (blockSwap d) = toFullBlockMat M)
    (hE : (toFullBlockMat E).PosDef) {k e : ℝ} (hk : 0 < k) (he : 0 < e)
    (hEM : toFullBlockMat E ≤ k • toFullBlockMat M)
    (hAE : toFullBlockMat (Book.Ch02.coarseBlockMatrix U a) ≤ e • toFullBlockMat E) :
    BlockMatLoewnerLE M
      (blockScale (k * e) (Book.Ch02.coarseStarredBlockMatrix U a)) := by
  have hA : (toFullBlockMat (Book.Ch02.coarseBlockMatrix U a)).PosDef :=
    posDef_toFullBlockMat (Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix U a)
      (Book.Ch02.blockCoarseMatrixTheory U a).block_matrix_posDef
  have hcore := le_smul_swapSharp hM hE hA hMsharp hk he hEM hAE
  rw [← toFullBlockMat_coarseStarred U a, ← toFullBlockMat_blockScale] at hcore
  simpa only [ofFullBlockMat_toFullBlockMat] using Analysis.blockMatLoewnerLE_of_le hcore

/-- **`hcmp` in the form consumed.**  The general form with the reference block taken to be the
congruence `R^T I R`. -/
theorem congr_le_smul_coarseStarred {U : Domain d} (a : CoeffOn U) {R E : BlockMat d}
    (hM : (toFullBlockMat (blockCongr R (Book.Ch02.blockIdentity d))).PosDef)
    (hMsharp : toFullBlockMat (blockSwap d) *
        (toFullBlockMat (blockCongr R (Book.Ch02.blockIdentity d)))⁻¹ *
        toFullBlockMat (blockSwap d) =
      toFullBlockMat (blockCongr R (Book.Ch02.blockIdentity d)))
    (hE : (toFullBlockMat E).PosDef) {k e : ℝ} (hk : 0 < k) (he : 0 < e)
    (hEM : toFullBlockMat E ≤
      k • toFullBlockMat (blockCongr R (Book.Ch02.blockIdentity d)))
    (hAE : toFullBlockMat (Book.Ch02.coarseBlockMatrix U a) ≤ e • toFullBlockMat E) :
    BlockMatLoewnerLE (blockCongr R (Book.Ch02.blockIdentity d))
      (blockScale (k * e) (Book.Ch02.coarseStarredBlockMatrix U a)) :=
  blockLoewner_le_smul_coarseStarred a hM hMsharp hE hk he hEM hAE

/-! ## The self-duality hypothesis is satisfiable, with an explicit witness -/

/-- **The self-dual diagonal metric.**  The diagonal metric `diag(m, m⁻¹)` is its own sharp.
The proof is the direct `2 × 2` block computation. -/
theorem swapSharp_blockDiag {m : Mat d} (hm : m.PosDef) :
    toFullBlockMat (blockSwap d) * (toFullBlockMat (Book.Ch02.blockDiag m m⁻¹))⁻¹ *
        toFullBlockMat (blockSwap d) =
      toFullBlockMat (Book.Ch02.blockDiag m m⁻¹) := by
  have hu : IsUnit m.det := (Matrix.isUnit_iff_isUnit_det m).mp hm.isUnit
  have hmmi : m * m⁻¹ = 1 := Matrix.mul_nonsing_inv m hu
  have hmim : m⁻¹ * m = 1 := Matrix.nonsing_inv_mul m hu
  have hd : toFullBlockMat (Book.Ch02.blockDiag m m⁻¹) =
      Matrix.fromBlocks m 0 0 m⁻¹ := toFullBlockMat_eq_fromBlocks _
  have hR : toFullBlockMat (blockSwap d) = Matrix.fromBlocks (0 : Mat d) 1 1 0 := by
    rw [toFullBlockMat_eq_fromBlocks]; rfl
  have hdinv : (Matrix.fromBlocks m 0 0 m⁻¹ : FullBlockMat d)⁻¹ =
      Matrix.fromBlocks m⁻¹ 0 0 m := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.fromBlocks_multiply]
    simp [hmmi, hmim, Matrix.fromBlocks_one]
  rw [hd, hR, hdinv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- **Congruence by the block square root.**  Congruence of the identity by the block square
root returns the block: `(A^{1/2})^T I A^{1/2} = A`.  This is what makes the congruence shape
and the diagonal-metric shape the same statement. -/
theorem toFullBlockMat_congr_blockSqrt {A : BlockMat d}
    (hA : (toFullBlockMat A).PosSemidef) :
    toFullBlockMat (blockCongr (blockSqrt A) (Book.Ch02.blockIdentity d)) =
      toFullBlockMat A := by
  have hI : toFullBlockMat (Book.Ch02.blockIdentity d) = (1 : FullBlockMat d) := by
    ext (i | i) (j | j) <;>
      simp [toFullBlockMat, Book.Ch02.blockIdentity, Book.Ch02.blockDiag, Matrix.one_apply]
  have hS : toFullBlockMat (blockSqrt A) = matSqrt (toFullBlockMat A) := by
    rw [blockSqrt, toFullBlockMat_ofFullBlockMat]
  have hSsymm : (matSqrt (toFullBlockMat A))ᵀ = matSqrt (toFullBlockMat A) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using!
      (matSqrt_spec hA).1.isHermitian
  rw [blockCongr, toFullBlockMat_ofFullBlockMat, hS, hI, Matrix.mul_one, hSsymm,
    (matSqrt_spec hA).2]

/-! ## The comparison discharged -/

/-- **The comparison with its `hcmp` discharged.**  The shared root of the two consumers, with
no Loewner hypothesis left: the `R`-metric size of the doubled cell average is controlled by
the cell energy, as soon as the reference `E` sits between the metric root and the coarse
response with the two size constants `k` and `e`.

This is `energy_map_congr_le` in `RecentScaleEnergyRoute.lean` composed with the
preceding form of `hcmp`. -/
theorem energy_map_congr_le_coarseStarred {U : Domain d} {lam Lam : ℝ} (a : CoeffOn U)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    {Y : DoubledField d} (hY : Book.Ch02.IsDoubledResponseField U a Y)
    {R E : BlockMat d}
    (hM : (toFullBlockMat (blockCongr R (Book.Ch02.blockIdentity d))).PosDef)
    (hMsharp : toFullBlockMat (blockSwap d) *
        (toFullBlockMat (blockCongr R (Book.Ch02.blockIdentity d)))⁻¹ *
        toFullBlockMat (blockSwap d) =
      toFullBlockMat (blockCongr R (Book.Ch02.blockIdentity d)))
    (hE : (toFullBlockMat E).PosDef) {k e : ℝ} (hk : 0 < k) (he : 0 < e)
    (hEM : toFullBlockMat E ≤
      k • toFullBlockMat (blockCongr R (Book.Ch02.blockIdentity d)))
    (hAE : toFullBlockMat (Book.Ch02.coarseBlockMatrix U a) ≤ e • toFullBlockMat E) :
    blockVecDot
        (blockMatVecMul R
          ((Book.Ch02.averageVec U Y.potential,
            Book.Ch02.averageVec U Y.flux) : BlockVec d))
        (blockMatVecMul R
          ((Book.Ch02.averageVec U Y.potential,
            Book.Ch02.averageVec U Y.flux) : BlockVec d)) ≤
      (k * e) *
        Book.Ch02.average U (fun x =>
          blockVecDot (Y.eval x)
            (blockMatVecMul (Book.Ch02.blockMatrixField a x) (Y.eval x))) :=
  energy_map_congr_le a hEll hY R (mul_pos hk he).le
    (congr_le_smul_coarseStarred a hM hMsharp hE hk he hEM hAE)

/-- **The comparison discharged on the metric root, the shape both consumers print.**
The preceding theorem with `R := M_0(F)^{1/2}`, whose two hypotheses are discharged outright by
the explicit witness.  What remains are exactly the two size inputs each consumer already owns:
a reference `E` squeezed between the metric `M_0(F)` and the cell's coarse response.

`blockVecDot (M_0^{1/2} (Y)_U) (M_0^{1/2} (Y)_U) ≤ (k e) ⨍_U Y·𝐀Y`. -/
theorem energy_map_respM0_le_coarseStarred {U : Domain d} {lam Lam : ℝ} (a : CoeffOn U)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    {Y : DoubledField d} (hY : Book.Ch02.IsDoubledResponseField U a Y)
    {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef)
    {E : BlockMat d} (hE : (toFullBlockMat E).PosDef) {k e : ℝ} (hk : 0 < k) (he : 0 < e)
    (hEM : toFullBlockMat E ≤ k • toFullBlockMat (respM0 F))
    (hAE : toFullBlockMat (Book.Ch02.coarseBlockMatrix U a) ≤ e • toFullBlockMat E) :
    blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          ((Book.Ch02.averageVec U Y.potential,
            Book.Ch02.averageVec U Y.flux) : BlockVec d))
        (blockMatVecMul (blockSqrt (respM0 F))
          ((Book.Ch02.averageVec U Y.potential,
            Book.Ch02.averageVec U Y.flux) : BlockVec d)) ≤
      (k * e) *
        Book.Ch02.average U (fun x =>
          blockVecDot (Y.eval x)
            (blockMatVecMul (Book.Ch02.blockMatrixField a x) (Y.eval x))) := by
  have hcongr : toFullBlockMat
      (blockCongr (blockSqrt (respM0 F)) (Book.Ch02.blockIdentity d)) =
      toFullBlockMat (respM0 F) :=
    toFullBlockMat_congr_blockSqrt (respM0_full_posDef hm).posSemidef
  refine energy_map_congr_le_coarseStarred a hEll hY ?_ ?_ hE hk he ?_ hAE
  · rw [hcongr]; exact respM0_full_posDef hm
  · rw [hcongr]; exact swapSharp_blockDiag (m := explicitCanonicalMetric F) hm
  · rw [hcongr]; exact hEM

end

end HCPolySupport.HighContrast.Multiscale
end
