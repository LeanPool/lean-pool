/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.ParentChildRecurrence
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Initial.GeometricMean
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.LoadMeanIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.CoarseBlockPerCellInput
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalDefectCarriers
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentHeadDefectHalves
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ReferenceCubeAveragePullback

/-!
# High-contrast homogenization: Entry.Response.Kernel.RandomToAnnealedRecentring

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The random-to-annealed recentring bound

This file proves the analytic core of the recentring bound `p.response.transfer`: the flat
quadratic-form comparison bounding the metric size of the random cell average's deviation from its
annealed mean, and the resulting bound `integral_respRecentre_sq_le_minus`/`_plus` after
integrating over the coefficient law. It also completes, for the adjoint sample, the `weakCellSum`
half of the recent-head cell-defect estimate — the normalized root-mean-square of the
child-optimizer mean defects as the reflected coarse-block defect action of the adjoint
coefficient — and the adjoint twin of the per-scale analytic input, whose sign-free algebraic
spine is reused unchanged.
-/

section
/-!
## The recentring vector `c_a` in the self-dual metric

The analytic core of the recentring bound (`WeakEstimateAssembly.lean`,
`integral_respRecentre_sq_le_minus/_plus`)
has three layers:

* `centered_metric_quadratic_le` -- the flat quadratic-form comparison, the entire analytic
  content;
* `metricBlockNormSq_responseAverage_sub_le` / `sqrt_metricBlockNormSq_responseAverage_sub_le`
  -- its packaging through the mean identity;
* `profilePrimalCenterVariance_le_variance` -- the recentring bound, of which
`recentre_sq_le_minus` and
  `recentre_sq_le_plus` below are the pathwise half.

The `eLpNorm`/`ℝ≥0∞` formulation of these bounds carries four extra carriers `metricBlockNormSq`,
`blockSize`, `relSize`, `diagonalWeakMetricFactor`/`diagonalWeakLoadMinus`, none of which this
tree has.  The proof below therefore works in Bochner integrals and spells the carriers out in
this tree's own vocabulary:

| carrier | here |
|---|---|
| `metricBlockNormSq m v` | `blockVecDot (blockMatVecMul (blockSqrt (respM0 F)) v) (…)` |
| `relSize E M` | `blockOpNorm (normalizedBlock E (respM0 F))` |
| `blockSize D E` | `blockOpNorm (normalizedBlock D E)` |
| `diagonalWeakMetricFactor m E ^ 2` | `respK0SqMinus P jStar F t` (`blockSpecBound`!) |
| `diagonalWeakLoadMinus E p r ^ 2` | `respLsqMinus P jStar F t e` |
| `scaleVariance` | `respAllScaleAbs` |

The one place the dictionary is not a rename is `diagonalWeakMetricFactor ↦ respK0Sq±`: the former
is an operator norm (`relSize`), while the latter is a `blockSpecBound`.  They agree on a positive
semidefinite block, which is what `blockOpNorm_le_blockSpecBound` below supplies.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace blockScale blockSub matSqrt matSqrt_spec
  normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## 1. The flat quadratic-form comparison -/

/-- **THE ANALYTIC CORE.**  The flat comparison `centered_metric_quadratic_le`, with the carrier
`relSize E M` written out as `‖M^{-1/2} E M^{-1/2}‖`:

`(D x) · M⁻¹ (D x) ≤ ‖M^{-1/2} E M^{-1/2}‖ · ‖E^{-1/2} D E^{-1/2}‖² · (x · E x)`.

Route: factor `D = E^{1/2} B E^{1/2}` with `B = E^{-1/2} D E^{-1/2}`, so
`M^{-1/2} D x = (M^{-1/2} E^{1/2}) B (E^{1/2} x)`; apply `vecSq_mulVec_le` twice and read the
outer factor off the C*-identity `‖N‖² = ‖N Nᵀ‖` at `N = M^{-1/2} E^{1/2}`, where
`N Nᵀ = M^{-1/2} E M^{-1/2}`. -/
theorem centered_metric_quadratic_le_recentring {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M E D : Matrix ι ι ℝ} (hM : M.PosDef) (hE : E.PosDef) (x : ι → ℝ) :
    (D *ᵥ x) ⬝ᵥ (M⁻¹ *ᵥ (D *ᵥ x)) ≤
      ‖matSqrt M⁻¹ * E * matSqrt M⁻¹‖ * ‖matSqrt E⁻¹ * D * matSqrt E⁻¹‖ ^ 2 * (x ⬝ᵥ (E *ᵥ x)) := by
  set SM : Matrix ι ι ℝ := matSqrt M⁻¹ with hSM
  set SE : Matrix ι ι ℝ := matSqrt E with hSE
  set SI : Matrix ι ι ℝ := matSqrt E⁻¹ with hSI
  set B : Matrix ι ι ℝ := SI * D * SI with hB
  set N : Matrix ι ι ℝ := SM * SE with hN
  set y : ι → ℝ := SE *ᵥ x with hy
  set z : ι → ℝ := B *ᵥ y with hz
  have hSMsymm : SMᵀ = SM := transpose_eq_of_psd (matSqrt_inv_posDef_full hM).posSemidef
  have hSEsymm : SEᵀ = SE := transpose_eq_of_psd (matSqrt_spec hE.posSemidef).1
  have hSMSM : SM * SM = M⁻¹ := (matSqrt_spec hM.inv.posSemidef).2
  have hSESE : SE * SE = E := (matSqrt_spec hE.posSemidef).2
  have hSESI : SE * SI = 1 := HCPolySupport.HighContrast.matSqrt_mul_matSqrt_inv hE
  have hSISE : SI * SE = 1 := HCPolySupport.HighContrast.matSqrt_inv_mul_matSqrt hE
  have hfactorD : SE * B * SE = D := by
    rw [hB]
    calc SE * (SI * D * SI) * SE = (SE * SI) * D * (SI * SE) := by noncomm_ring
      _ = D := by rw [hSESI, hSISE, Matrix.one_mul, Matrix.mul_one]
  have hquadM : (D *ᵥ x) ⬝ᵥ (M⁻¹ *ᵥ (D *ᵥ x)) = (SM *ᵥ (D *ᵥ x)) ⬝ᵥ (SM *ᵥ (D *ᵥ x)) := by
    rw [← hSMSM, ← Matrix.mulVec_mulVec]
    exact GeometricMean.dotProduct_mulVec_symm hSMsymm (D *ᵥ x) (SM *ᵥ (D *ᵥ x))
  have hwform : N *ᵥ z = SM *ᵥ (D *ᵥ x) := by
    have hmatrix : N * B * SE = SM * D := by
      rw [hN]
      calc SM * SE * B * SE = SM * (SE * B * SE) := by noncomm_ring
        _ = SM * D := by rw [hfactorD]
    calc N *ᵥ z = N *ᵥ (B *ᵥ (SE *ᵥ x)) := by rw [hz, hy]
      _ = (N * B * SE) *ᵥ x := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = (SM * D) *ᵥ x := by rw [hmatrix]
      _ = SM *ᵥ (D *ᵥ x) := by rw [Matrix.mulVec_mulVec]
  have hyquad : y ⬝ᵥ y = x ⬝ᵥ (E *ᵥ x) := by
    calc y ⬝ᵥ y = (SE *ᵥ x) ⬝ᵥ (SE *ᵥ x) := by rw [hy]
      _ = x ⬝ᵥ (SE *ᵥ (SE *ᵥ x)) := (GeometricMean.dotProduct_mulVec_symm hSEsymm x (SE *ᵥ x)).symm
      _ = x ⬝ᵥ ((SE * SE) *ᵥ x) := by rw [Matrix.mulVec_mulVec]
      _ = x ⬝ᵥ (E *ᵥ x) := by rw [hSESE]
  have hNnorm : ‖N‖ ^ 2 = ‖SM * E * SM‖ := by
    have hNN : N * Nᴴ = SM * E * SM := by
      rw [hN, Matrix.conjTranspose_mul, Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.conjTranspose_eq_transpose_of_trivial, hSEsymm, hSMsymm]
      calc SM * SE * (SE * SM) = SM * (SE * SE) * SM := by noncomm_ring
        _ = SM * E * SM := by rw [hSESE]
    rw [pow_two, ← CStarRing.norm_self_mul_star, Matrix.star_eq_conjTranspose, hNN]
  have hwle : (N *ᵥ z) ⬝ᵥ (N *ᵥ z) ≤ ‖N‖ ^ 2 * (z ⬝ᵥ z) := vecSq_mulVec_le N z
  have hzle : z ⬝ᵥ z ≤ ‖B‖ ^ 2 * (y ⬝ᵥ y) := by rw [hz]; exact vecSq_mulVec_le B y
  have hstep : ‖N‖ ^ 2 * (z ⬝ᵥ z) ≤ ‖N‖ ^ 2 * (‖B‖ ^ 2 * (y ⬝ᵥ y)) :=
    mul_le_mul_of_nonneg_left hzle (sq_nonneg _)
  calc (D *ᵥ x) ⬝ᵥ (M⁻¹ *ᵥ (D *ᵥ x)) = (N *ᵥ z) ⬝ᵥ (N *ᵥ z) := by rw [hquadM, hwform]
    _ ≤ ‖N‖ ^ 2 * (z ⬝ᵥ z) := hwle
    _ ≤ ‖N‖ ^ 2 * (‖B‖ ^ 2 * (y ⬝ᵥ y)) := hstep
    _ = ‖matSqrt M⁻¹ * E * matSqrt M⁻¹‖ * ‖matSqrt E⁻¹ * D * matSqrt E⁻¹‖ ^ 2 *
          (x ⬝ᵥ (E *ᵥ x)) := by rw [hNnorm, hB, hyquad]; ring

/-! ## 2. `M_0 = diag(m, m^{-1})`: symmetry, positivity, and its inverse -/

omit [NeZero d] in
/-- A block-diagonal doubled block in `fromBlocks` form, the shape of `shear_full` in
`WeakEstimateAssembly.lean`. -/
private theorem blockDiag_full (A B : Mat d) :
    toFullBlockMat (⟨A, 0, 0, B⟩ : BlockMat d) = Matrix.fromBlocks A 0 0 B := by
  ext (i | i) (j | j) <;> rfl

omit [NeZero d] in
/-- `M_0 = diag(m, m^{-1})` is structurally symmetric when `m` is. -/
private theorem respM0_isSymm {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) :
    IsSymmetricBlockMat (respM0 F) := by
  have hsym : (explicitCanonicalMetric F)ᵀ = explicitCanonicalMetric F :=
    transpose_eq_of_psd hm.posSemidef
  have hsymi : ((explicitCanonicalMetric F)⁻¹)ᵀ = (explicitCanonicalMetric F)⁻¹ :=
    transpose_eq_of_psd hm.inv.posSemidef
  intro α β
  cases α <;> cases β <;>
    simp only [blockMatEntry, respM0, Matrix.zero_apply] <;>
    first
      | rfl
      | exact congrFun (congrFun hsym.symm _) _
      | exact congrFun (congrFun hsymi.symm _) _

omit [NeZero d] in
/-- The quadratic form of `M_0` splits into the two printed pieces, the form of
`respM0_qform_split_canonicalMetric`. -/
private theorem respM0_qform (F : BlockMat d) (Y : BlockVec d) :
    blockVecDot Y (blockMatVecMul (respM0 F) Y) =
      vecDot Y.1 (matVecMul (explicitCanonicalMetric F) Y.1) +
        vecDot Y.2 (matVecMul (explicitCanonicalMetric F)⁻¹ Y.2) := by
  simp [respM0, blockVecDot, blockMatVecMul, matVecMul, vecDot]

omit [NeZero d] in
/-- `M_0 = diag(m, m^{-1})` is positive definite as a doubled block. -/
private theorem respM0_blockPosDef {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) :
    Book.Ch02.BlockPosDef (respM0 F) := by
  intro Y hY
  rw [respM0_qform]
  have h1 : ∀ v : Vec d, v ≠ 0 → 0 < vecDot v (matVecMul (explicitCanonicalMetric F) v) := by
    intro v hv
    have := hm.dotProduct_mulVec_pos hv
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using this
  have h2 : ∀ v : Vec d, v ≠ 0 → 0 < vecDot v (matVecMul (explicitCanonicalMetric F)⁻¹ v) := by
    intro v hv
    have := (hm.inv).dotProduct_mulVec_pos hv
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using this
  have h1' : ∀ v : Vec d, 0 ≤ vecDot v (matVecMul (explicitCanonicalMetric F) v) := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp [vecDot, matVecMul]
    · exact (h1 v hv).le
  have h2' : ∀ v : Vec d, 0 ≤ vecDot v (matVecMul (explicitCanonicalMetric F)⁻¹ v) := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp [vecDot, matVecMul]
    · exact (h2 v hv).le
  rcases eq_or_ne Y.1 0 with h0 | h0
  · have h0' : Y.2 ≠ 0 := by
      intro h
      exact hY (Prod.ext h0 h)
    linarith only [h1' Y.1, h2 Y.2 h0']
  · linarith only [h2' Y.2, h1 Y.1 h0]

omit [NeZero d] in
/-- **`R M_0 R = M_0⁻¹`, in the flat picture**: the inverse of `M_0 = diag(m, m^{-1})` is
`diag(m^{-1}, m)`, which is exactly the block `blockVecDot_blockSwap_respM0`
(`DiagonalDefectCarriers.lean`) produces from the swap conjugation. -/
theorem respM0_inv {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) :
    (toFullBlockMat (respM0 F))⁻¹ =
      toFullBlockMat (⟨(explicitCanonicalMetric F)⁻¹, 0, 0, explicitCanonicalMetric F⟩ :
        BlockMat d) := by
  have hdet : IsUnit (explicitCanonicalMetric F).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hm.isUnit
  refine Matrix.inv_eq_right_inv ?_
  have hM : toFullBlockMat (respM0 F) =
      Matrix.fromBlocks (explicitCanonicalMetric F) 0 0 (explicitCanonicalMetric F)⁻¹ := by
    rw [respM0]; exact blockDiag_full _ _
  rw [hM, blockDiag_full, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet]
  exact Matrix.fromBlocks_one

/-! ## 3. `blockOpNorm` and `blockSpecBound` agree on a positive semidefinite block -/

omit [NeZero d] in
/-- The quadratic form of `blockScale c (blockIdentity d)`, the form of `b130_qform_blockScale` /
`qform_identity` in `WeakEstimateAssembly.lean`. -/
private theorem qform_scale_identity (c : ℝ) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c (Book.Ch02.blockIdentity d)) X) =
      c * (toFullBlockVec X ⬝ᵥ toFullBlockVec X) := by
  have hid : toFullBlockMat (Book.Ch02.blockIdentity d) = (1 : FullBlockMat d) := by
    ext (i | i) (j | j) <;>
      simp [toFullBlockMat, Book.Ch02.blockIdentity, Book.Ch02.blockDiag, Matrix.one_apply]
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul, toFullBlockMat_blockScale, hid,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

omit [NeZero d] in
/-- **`blockOpNorm N ≤ blockSpecBound N` on a positive semidefinite block.**  The converse of the
unconditional `blockSpecBound_le_blockOpNorm` (`WeakEstimateAssembly.lean`); this is the one
place where positive semidefiniteness is genuinely needed, and it is what identifies this tree's
`respK0Sq±` (a `blockSpecBound`) with the carrier `diagonalWeakMetricFactor ^ 2` (a `relSize`,
i.e. an operator norm). -/
theorem blockOpNorm_le_blockSpecBound (N : BlockMat d)
    (hN : (toFullBlockMat N).PosSemidef) : blockOpNorm N ≤ blockSpecBound N := by
  have hdot : ∀ c : ℝ, BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d)) →
      ∀ v : FullBlockVec d, v ⬝ᵥ (toFullBlockMat N *ᵥ v) ≤ c * (v ⬝ᵥ v) := by
    intro c hc v
    have hX := hc (ofFullBlockVec v)
    rw [qform_scale_identity] at hX
    have hL : blockVecDot (ofFullBlockVec v) (blockMatVecMul N (ofFullBlockVec v)) =
        toFullBlockVec (ofFullBlockVec v) ⬝ᵥ
          (toFullBlockMat N *ᵥ toFullBlockVec (ofFullBlockVec v)) := by
      rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
    rw [hL, toFullBlockVec_ofFullBlockVec] at hX
    linarith only [hX]
  have hne : ({c : ℝ | 0 ≤ c ∧
      BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))}).Nonempty := by
    refine ⟨blockOpNorm N, by rw [blockOpNorm]; exact norm_nonneg _, fun X => ?_⟩
    have h := psd_dot_le_opNorm hN (toFullBlockVec X)
    have hL : blockVecDot X (blockMatVecMul N X) =
        toFullBlockVec X ⬝ᵥ (toFullBlockMat N *ᵥ toFullBlockVec X) := by
      rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
    rw [hL, qform_scale_identity]
    have hB : blockOpNorm N = ‖toFullBlockMat N‖ := rfl
    rw [hB]
    linarith only [h]
  rw [blockSpecBound]
  refine le_csInf hne fun c hc => ?_
  exact opNorm_le_of_psd_dot_le hN hc.1 (hdot c hc.2)

/-! ## 4. The mean identity for the PLUS sign -/

/-- The mean identity for the recentred field `a_+` on the centred cell `U_t`: the plus twin of
`cellAverage_optimizerField_respCoeffMinus_eq` (`DiagonalDefectCarriers.lean`),
which the tree did not have.  The elliptic datum is the a.e.-representative one of
`exists_elliptic_representative_respCoeffPlus` (`EllipticRepresentativeInputs.lean`), so no
ellipticity
hypothesis is added. -/
theorem cellAverage_optimizerField_respCoeffPlus_eq
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffPlus F a) u) :
    cellAverage (HighContrast.adaptedCell q t) (optimizerField (respCoeffPlus F a) u) =
      blockResponseMean
        (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffPlus F a)) (-p, r) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  refine cellAverage_optimizerField_eq_blockResponseMean_of_aeEq
    (adaptedCell_isOpenBoundedConvexDomain q hq t) ?_ hEll hae p r u hu
  have hset : HighContrast.adaptedCell q t =
      translateSet 0 ((matVecMul q) '' (openCubeSet (originCube d t))) := by
    rw [← Annealed.adaptedCellTranslate_eq_cg_affine q t 0]
    simp [HighContrast.adaptedCellTranslate]
  rw [hset]; exact volume_affine_openCube_toReal_pos q hq t 0

/-! ## 5. THE PATHWISE RECENTRING BOUND -/

omit [NeZero d] in
/-- A normalized block of a positive semidefinite block is positive semidefinite, as in
`normalizedBlock_posSemidef_of_posSemidef_of_posDef` (`WeakEstimateAssembly.lean`), which lives
downstream of this
file. -/
private theorem normalizedBlock_posSemidef {A R : BlockMat d}
    (hA : (toFullBlockMat A).PosSemidef) (hR : (toFullBlockMat R).PosDef) :
    (toFullBlockMat (normalizedBlock A R)).PosSemidef := by
  have hs : (matSqrt (toFullBlockMat R)⁻¹).IsHermitian :=
    (matSqrt_inv_posDef_full hR).isHermitian
  have hp := hA.conjTranspose_mul_mul_same (matSqrt (toFullBlockMat R)⁻¹)
  rw [hs.eq] at hp
  rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
  exact hp

omit [NeZero d] in
/-- The quadratic form of `blockSqrt A` is the quadratic form of `A`.  Block-level `sqrt_form`
(`ResponseTransferHelpers.lean`). -/
private theorem blockVecDot_blockSqrt {A : BlockMat d}
    (hA : (toFullBlockMat A).PosSemidef) (w : BlockVec d) :
    blockVecDot (blockMatVecMul (blockSqrt A) w) (blockMatVecMul (blockSqrt A) w)
      = blockVecDot w (blockMatVecMul A w) := by
  rw [← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec,
    toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul]
  have hf : toFullBlockMat (blockSqrt A) = matSqrt (toFullBlockMat A) := by
    rw [blockSqrt, toFullBlockMat_ofFullBlockMat]
  rw [hf]
  exact sqrt_form hA _

omit [NeZero d] in
/-- **The generic pathwise recentring bound.**  With `x` the load vector, `Ehat` the annealed
block and `A` the pathwise block, the recentring vector `c = M_0^{1/2}(⟨X⟩ − Y)` obeys

`|c|² ≤ |M_0^{-1/2} Ehat M_0^{-1/2}| · ‖Ehat^{-1/2}(A − Ehat)Ehat^{-1/2}‖² · (x · Ehat x)`,

with the first factor replaced by its `blockSpecBound`, i.e. by `K_0²`.  This is the
`blockVecDot`/Bochner form of `metricBlockNormSq_responseAverage_sub_le`. -/
theorem blockResponseMean_sub_sq_le {F A Ehat : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (hEhat : (toFullBlockMat Ehat).PosDef)
    (x : BlockVec d) :
    blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockResponseMean A x - blockResponseMean Ehat x))
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockResponseMean A x - blockResponseMean Ehat x))
      ≤ blockSpecBound (normalizedBlock Ehat (respM0 F)) *
          blockOpNorm (normalizedBlock (blockSub A Ehat) Ehat) ^ 2 *
          blockVecDot x (blockMatVecMul Ehat x) := by
  have hM : (toFullBlockMat (respM0 F)).PosDef := respM0_full_posDef hm
  set D : BlockMat d := blockSub A Ehat with hD
  set y : BlockVec d := blockMatVecMul D x with hy
  -- Step A: the difference of the two means is the swap of the block defect applied to `x`
  have hstep1 : blockResponseMean A x - blockResponseMean Ehat x
      = blockMatVecMul (blockSwap d) y := blockResponseMean_sub_blockResponseMean A Ehat x
  -- Step B: `M_0^{1/2}` turns the length into the `M_0` quadratic form, and the swap inverts it
  have hstep2 : blockVecDot
      (blockMatVecMul (blockSqrt (respM0 F)) (blockMatVecMul (blockSwap d) y))
      (blockMatVecMul (blockSqrt (respM0 F)) (blockMatVecMul (blockSwap d) y))
      = blockVecDot y (blockMatVecMul
          (⟨(explicitCanonicalMetric F)⁻¹, 0, 0, explicitCanonicalMetric F⟩ : BlockMat d) y) := by
    rw [blockVecDot_blockSqrt hM.posSemidef, blockVecDot_blockSwap_respM0]
  -- Step C: flatten and apply the analytic core
  have hflat : blockVecDot y (blockMatVecMul
      (⟨(explicitCanonicalMetric F)⁻¹, 0, 0, explicitCanonicalMetric F⟩ : BlockMat d) y)
      = (toFullBlockMat D *ᵥ toFullBlockVec x) ⬝ᵥ
          ((toFullBlockMat (respM0 F))⁻¹ *ᵥ (toFullBlockMat D *ᵥ toFullBlockVec x)) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul, respM0_inv hm]
    simp only [hy, toFullBlockVec_blockMatVecMul]
  have hcore := centered_metric_quadratic_le_recentring (M := toFullBlockMat (respM0 F))
    (E := toFullBlockMat Ehat) (D := toFullBlockMat D) hM hEhat (toFullBlockVec x)
  -- Step D: read the three factors off the definitions
  have hK : ‖matSqrt (toFullBlockMat (respM0 F))⁻¹ * toFullBlockMat Ehat *
      matSqrt (toFullBlockMat (respM0 F))⁻¹‖
      = blockOpNorm (normalizedBlock Ehat (respM0 F)) := by
    rw [blockOpNorm, normalizedBlock, toFullBlockMat_ofFullBlockMat]
  have hB : ‖matSqrt (toFullBlockMat Ehat)⁻¹ * toFullBlockMat D *
      matSqrt (toFullBlockMat Ehat)⁻¹‖ = blockOpNorm (normalizedBlock D Ehat) := by
    rw [blockOpNorm, normalizedBlock, toFullBlockMat_ofFullBlockMat]
  have hL : toFullBlockVec x ⬝ᵥ (toFullBlockMat Ehat *ᵥ toFullBlockVec x)
      = blockVecDot x (blockMatVecMul Ehat x) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  rw [hK, hB, hL] at hcore
  -- Step E: `blockOpNorm ≤ blockSpecBound` on the positive semidefinite normalized block
  have hKle : blockOpNorm (normalizedBlock Ehat (respM0 F))
      ≤ blockSpecBound (normalizedBlock Ehat (respM0 F)) :=
    blockOpNorm_le_blockSpecBound _ (normalizedBlock_posSemidef hEhat.posSemidef hM)
  have hL0 : 0 ≤ blockVecDot x (blockMatVecMul Ehat x) := by
    rw [← hL]
    have := hEhat.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec x)
    simpa using this
  have hB0 : 0 ≤ blockOpNorm (normalizedBlock D Ehat) ^ 2 := sq_nonneg _
  rw [hstep1, hstep2, hflat]
  refine le_trans hcore ?_
  have hBL : 0 ≤ blockOpNorm (normalizedBlock D Ehat) ^ 2 *
      blockVecDot x (blockMatVecMul Ehat x) := mul_nonneg hB0 hL0
  calc blockOpNorm (normalizedBlock Ehat (respM0 F)) *
        blockOpNorm (normalizedBlock D Ehat) ^ 2 * blockVecDot x (blockMatVecMul Ehat x)
      = blockOpNorm (normalizedBlock Ehat (respM0 F)) *
          (blockOpNorm (normalizedBlock D Ehat) ^ 2 *
            blockVecDot x (blockMatVecMul Ehat x)) := by ring
    _ ≤ blockSpecBound (normalizedBlock Ehat (respM0 F)) *
          (blockOpNorm (normalizedBlock D Ehat) ^ 2 *
            blockVecDot x (blockMatVecMul Ehat x)) := mul_le_mul_of_nonneg_right hKle hBL
    _ = blockSpecBound (normalizedBlock Ehat (respM0 F)) *
          blockOpNorm (normalizedBlock D Ehat) ^ 2 *
            blockVecDot x (blockMatVecMul Ehat x) := by ring

/-! ## 6. The two response instances -/

/-- **The pathwise recentring bound, minus sign.**  Stated on the *body* of `respRecentreMinus`
(`WeakEstimateAssembly.lean`) and with `respK0SqMinus` (`WeakEstimateAssembly.lean`) spelled out,
because both live downstream of this file; at the consumer both are `rfl`. -/
theorem recentre_sq_le_minus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) (hq : IsUnit (respGrid jStar F)) (hm : (explicitCanonicalMetric F).PosDef)
    (hEhat : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (a : CoeffSpace d) (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u) :
    blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u) -
            respYMinus P jStar F t e))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u) -
            respYMinus P jStar F t e))
      ≤ blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)) *
          blockOpNorm (normalizedBlock
            (blockSub (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a))
              (respEhatMinus P jStar F t)) (respEhatMinus P jStar F t)) ^ 2 *
          respLsqMinus P jStar F t e := by
  have hmean : cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)
      = blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffMinus F a))
          (respxMinus P jStar F t e) :=
    cellAverage_optimizerField_respCoeffMinus_eq (respGrid jStar F) hq t F a
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) u hu
  have hY : respYMinus P jStar F t e =
      blockResponseMean (respEhatMinus P jStar F t) (respxMinus P jStar F t e) := rfl
  rw [hmean, hY]
  exact blockResponseMean_sub_sq_le hm hEhat (respxMinus P jStar F t e)

/-- **The pathwise recentring bound, plus sign.** -/
theorem recentre_sq_le_plus (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) (hq : IsUnit (respGrid jStar F)) (hm : (explicitCanonicalMetric F).PosDef)
    (hEhat : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (a : CoeffSpace d) (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u) :
    blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u) -
            respYPlus P jStar F t e))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u) -
            respYPlus P jStar F t e))
      ≤ blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)) *
          blockOpNorm (normalizedBlock
            (blockSub (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a))
              (respEhatPlus P jStar F t)) (respEhatPlus P jStar F t)) ^ 2 *
          respLsqPlus P jStar F t e := by
  have hmean : cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)
      = blockResponseMean (coarseBlockMatrix (respCell jStar F t) (respCoeffPlus F a))
          (respxPlus P jStar F t e) :=
    cellAverage_optimizerField_respCoeffPlus_eq (respGrid jStar F) hq t F a
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) u hu
  have hY : respYPlus P jStar F t e =
      blockResponseMean (respEhatPlus P jStar F t) (respxPlus P jStar F t e) := rfl
  rw [hmean, hY]
  exact blockResponseMean_sub_sq_le hm hEhat (respxPlus P jStar F t e)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The `weakCellSum` half of the recent head for the adjoint sample

This is the adjoint (`a_+ = aᵗ + g`) twin of the `weakCellSum` half of the recent-head
cell-defect estimate `e.response.weak.estimate`.  The normalized finite-cell root-mean-square
of the child-optimizer mean defects is the reflected coarse-block defect action of the adjoint
coefficient `a_+ = respCoeffPlus F a` at the adjoint load `x^+ = (-p, q^+)`; summing the
per-depth bound against the weights `3^{-n/2}` over the window `n ≤ H` produces exactly
`weakCellSum`, with the printed prefactor
`√‖M_0^{-1/2} Ê_+^t M_0^{-1/2}‖ · L^+`.

The only inputs that are specialised to the recentred (minus) carriers are the two mean
identities for the optimizer field; their adjoint counterparts are provided here.  Every
reflected-defect comparison it consumes is stated for a generic coefficient field, block and
load, and so applies to the adjoint sample unchanged.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter blockSub normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The adjoint optimizer-mean identities -/

/-- The adjoint twin of the optimizer-mean identity on an aligned adapted subcell: the cell
average of
the optimizer field for `a_+ = aᵗ + g` equals the block response mean of the coarse block matrix
at the adjoint loading `(-p, r)`.  The elliptic datum is the a.e.-representative one, so no
ellipticity hypothesis is added. -/
theorem cellAverage_optimizerField_respCoeffPlus_eq_at
    (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) (u : AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter q k w))
    (hu : IsResponseMaximizer (adaptedCellAtCenter q k w) p r (respCoeffPlus F a) u) :
    cellAverage (adaptedCellAtCenter q k w) (optimizerField (respCoeffPlus F a) u) =
      blockResponseMean
        (coarseBlockMatrix (adaptedCellAtCenter q k w) (respCoeffPlus F a)) (-p, r) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq k (adaptedCellCenter q k w) a
  have hEll' : IsEllipticFieldOn lam (2 * Lam + 2 * ‖respg F‖ ^ 2 / lam)
      (adaptedCellAtCenter q k w) (fun x => matTranspose (f x) + respg F) :=
    isEllipticFieldOn_transpose_add_skew hEll _ (respg_isSkew F)
  refine cellAverage_optimizerField_eq_blockResponseMean_of_aeEq
    (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w)
    (volume_adaptedCellAtCenter_toReal_pos q hq k w) hEll' ?_ p r u hu
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [hae] with x hx
  simp [respCoeffPlus, hx]

/-- The adjoint pointwise comparison identity: the child-cell minus parent-cell optimizer mean
difference for `a_+ = aᵗ + g` is exactly the reflected action of the coarse-block defect that
`weakCellDefect` normalizes. -/
theorem cellAverage_optimizerField_respCoeffPlus_sub_eq
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (k : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (v : AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter q k w))
    (hv : IsResponseMaximizer (adaptedCellAtCenter q k w) p r (respCoeffPlus F a) v)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffPlus F a) u) :
    cellAverage (adaptedCellAtCenter q k w) (optimizerField (respCoeffPlus F a) v) -
        cellAverage (HighContrast.adaptedCell q t) (optimizerField (respCoeffPlus F a) u) =
      blockMatVecMul (blockSwap d)
        (blockMatVecMul
          (blockSub (coarseBlockMatrix (adaptedCellAtCenter q k w) (respCoeffPlus F a))
            (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffPlus F a))) (-p, r)) := by
  rw [cellAverage_optimizerField_respCoeffPlus_eq_at q hq k w F a p r v hv,
    cellAverage_optimizerField_respCoeffPlus_eq q hq t F a p r u hu,
    blockResponseMean_sub_blockResponseMean]

/-! ## Adjoint child maximizer selection -/

/-- Nonemptiness of an aligned adapted subcell. -/
private theorem adaptedCellAtCenter_nonempty_of_isUnit (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) : (adaptedCellAtCenter q k w).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hpos := volume_adaptedCellAtCenter_toReal_pos q hq k w
  rw [h] at hpos
  simp at hpos

/-- Child response maximizers for the adjoint coefficient can be chosen simultaneously at every
depth and cell label. -/
theorem nonempty_childMaximizerFamily_plus
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) :
    Nonempty ((n : ℕ) → (w : Fin d → ℤ) →
      ScalarCanonicalMaximizer (adaptedCellAtCenter q (t - (n : ℤ)) w) p r
        (respCoeffPlus F a)) := by
  exact ⟨fun n w => Classical.choice
    (nonempty_scalarCanonicalMaximizer_respCoeffPlus_adaptedCellAtCenter q hq (t - (n : ℤ)) w F
      a p r)⟩

/-! ## The `weakCellSum` half for the adjoint sample -/

/-- **`e.response.weak.estimate`, `weakCellSum` half, at one depth, for `a_+`.**  The normalized
finite-cell root-mean-square of the depth-`n` child-optimizer mean defects, measured in `M_0`, is
bounded by `√K_0 · L^+ · weakCellDefect`, where `K_0 = ‖M_0^{-1/2} Ê_+^t M_0^{-1/2}‖` and
`(L^+)^2 = x^+ · Ê_+^t x^+`. -/
theorem childMean_defect_avsum_le_plus
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (n : ℕ)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u)
    (V : (w : Fin d → ℤ) →
      ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a))
    (hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffPlus F a)
                    ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffPlus F a)
                    ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u))))
      ≤ Real.sqrt ‖toFullBlockMat (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖ *
          Real.sqrt (respLsqPlus P jStar F t e) *
          weakCellDefect (respGrid jStar F) t n (respEhatPlus P jStar F t)
            (respCoeffPlus F a) := by
  have hstep : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffPlus F a)
                  ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
              cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffPlus F a)
                  ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
              cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
        = blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d)
                (blockMatVecMul
                  (blockSub
                    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (respCoeffPlus F a))
                    (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) t)
                      (respCoeffPlus F a)))
                  (respxPlus P jStar F t e))))
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d)
                (blockMatVecMul
                  (blockSub
                    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (respCoeffPlus F a))
                    (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) t)
                      (respCoeffPlus F a)))
                  (respxPlus P jStar F t e)))) := by
    intro w _
    simp only [respCell]
    rw [cellAverage_optimizerField_respCoeffPlus_sub_eq (respGrid jStar F) hgrid t
      (t - (n : ℤ)) w F a (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
      ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) (V w).isMaximizer u hu]
    rfl
  rw [Finset.sum_congr rfl hstep]
  exact weakCellDefect_avsum_le (respGrid jStar F) t n (respCoeffPlus F a) hE
    (respxPlus P jStar F t e)

/-- **`e.response.weak.estimate`, THE `weakCellSum` HALF OF THE RECENT HEAD, for `a_+`.**  For the
adjoint sample `a_+ = respCoeffPlus F a`, the adjoint response matrix
`E_+^t = respEhatPlus P jStar F t` and the adjoint load `x^+`, choosing the child maximizers
simultaneously and summing the per-depth bound against the weights `3^{-n/2}` over the window
`n ≤ H` produces exactly `weakCellSum`, with the printed prefactor
`√‖M_0^{-1/2} Ê_+^t M_0^{-1/2}‖ · L^+`. -/
theorem weakCellSum_half_le_plus
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (H : ℕ)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u)
    (hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a),
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffPlus F a) u))))
        ≤ Real.sqrt ‖toFullBlockMat (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖ *
            Real.sqrt (respLsqPlus P jStar F t e) *
            weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t) (respCoeffPlus F a) := by
  obtain ⟨V⟩ := nonempty_childMaximizerFamily_plus (respGrid jStar F) hgrid t F a
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
  refine ⟨V, ?_⟩
  set K : ℝ :=
    Real.sqrt ‖toFullBlockMat (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖ with hK
  set L : ℝ := Real.sqrt (respLsqPlus P jStar F t e) with hL
  have hterm : ∀ n ∈ Finset.range (H + 1),
      (3 : ℝ) ^ (-((n : ℝ) / 2)) *
          Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (optimizerField (respCoeffPlus F a)
                        ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                    cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (optimizerField (respCoeffPlus F a)
                        ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                    cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u))))
        ≤ K * L *
            ((3 : ℝ) ^ (-((n : ℝ) / 2)) *
              weakCellDefect (respGrid jStar F) t n (respEhatPlus P jStar F t)
                (respCoeffPlus F a)) := by
    intro n _
    have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-((n : ℝ) / 2)) := Real.rpow_nonneg (by norm_num) _
    have hcell := childMean_defect_avsum_le_plus P jStar F t e hgrid a n u hu (V n) hE
    calc (3 : ℝ) ^ (-((n : ℝ) / 2)) * _
        ≤ (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            (K * L *
              weakCellDefect (respGrid jStar F) t n (respEhatPlus P jStar F t)
                (respCoeffPlus F a)) := by
          exact mul_le_mul_of_nonneg_left hcell hw
      _ = K * L *
            ((3 : ℝ) ^ (-((n : ℝ) / 2)) *
              weakCellDefect (respGrid jStar F) t n (respEhatPlus P jStar F t)
                (respCoeffPlus F a)) := by ring
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [weakCellSum, Finset.mul_sum]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The plus twin of the per-scale analytic input

`scaleInput_of_analytic_plus` is the adjoint (`a_+`) twin of
`scaleInput_of_analytic` (`CoarseBlockPerCellInput.lean`): the per-scale input of
the cell-average lemma with the response sample replaced by `respEhatPlus`, `respLsqPlus` and
`respCoeffPlus`.  The algebraic spine `scaleInput_spine_le` is sign-free and is reused
unchanged, so the two analytic inputs keep exactly the same shape with the plus sample.
-/

open HCPolySupport.HighContrast (CoeffSpace normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The adjoint (`a_+`) twin of `scaleInput_of_analytic`.

The index set is `triadicIndexBox d n`, the root is `blockSqrt (respM0 F)`, and the scalars are
the plus ones: `√(blockSpecBound (normalizedBlock (respEhatPlus …) (respM0 F)))`, the all-scale
maximum factor `1 + √(respAllScaleMax …) · 3^{ρn/2}`, `√(respLsqPlus …)`, and the block size of
`weakAverageDefect … (respEhatPlus …) (respCoeffPlus …)`.  The per-cell hypothesis `hcell` and
the averaged energy hypothesis `henergy` are transported verbatim from the minus statement. -/
theorem scaleInput_of_analytic_plus
    (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (a : CoeffSpace d) (n : ℕ)
    (Y : (Fin d → ℤ) → Vec d → BlockVec d) (G : (Fin d → ℤ) → ℝ)
    (hLsq : 0 ≤ respLsqPlus P jStar F t e)
    (hcell : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
        ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
            * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2 * G w)
    (henergy : ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n, G w
      ≤ 2 * respLsqPlus P jStar F t e
          * ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
              (respEhatPlus P jStar F t) (respCoeffPlus F a))‖) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w))))
      ≤ Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) *
          Real.sqrt (respLsqPlus P jStar F t e) *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatPlus P jStar F t) (respCoeffPlus F a))‖ := by
  have hB : (0 : ℝ) ≤ 1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
      (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2) :=
    add_nonneg zero_le_one
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
  have hLsq' : Real.sqrt (respLsqPlus P jStar F t e) ^ 2 = respLsqPlus P jStar F t e :=
    Real.sq_sqrt hLsq
  refine scaleInput_spine_le (triadicIndexBox d n) (blockSqrt (respM0 F))
    (fun w => cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Y w)) G
    _ _ _ _ (Real.sqrt_nonneg _) hB (Real.sqrt_nonneg _) (norm_nonneg _) hcell ?_
  rw [hLsq']
  exact henergy

end

end HCPolySupport.HighContrast.Multiscale
end
