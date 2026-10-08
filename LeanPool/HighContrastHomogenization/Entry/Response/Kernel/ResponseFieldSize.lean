/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedLocality
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.SharpOrderEnergyMap
public import LeanPool.HighContrastHomogenization.Provider.Response.AlignedIdentities

/-!
# High-contrast homogenization: Entry.Response.Kernel.ResponseFieldSize

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The size of a recentred response field

This file bounds the metric size of a doubled cell average by the cell energy, given a doubled
response field `Y` and the two size hypotheses that relate it to the normalized block: it shows
the normalized block is Hermitian, bounds it by one plus the spectral bound, and controls the
metric of the recent-scale difference by the weighted all-scale maximum. It also compares the
pointwise selection `Nonempty.some` of a response maximizer with the Chapter-2 canonical
maximizer, showing their gradients, fluxes and subcell averages of the doubled state agree almost
everywhere, and records the measurability of the resulting coefficient carriers.

The results below are the response-field size, restriction and selection steps of the
response-transfer estimate `p.response.transfer`.
-/

section
/-!
## The response field of a recentred difference, and its size

`diagonalWeakNorm_primal_le` (`DiagonalWeakNormBound.lean`) is untouched: nothing here
restates, weakens or deletes any existing declaration.

## What this module supplies

The metric size of a doubled cell average is reduced to the cell energy
(`SharpOrderEnergyMap.lean`), given a doubled RESPONSE FIELD `Y` and two size
inequalities.  That reduction leaves open exactly two inputs:

1. the `Y` CONSTRUCTION for the recentred DIFFERENCE field, `isDoubledResponseField_grad_sub`;
  and
2. the RESPONSE-SIZE step, the `hsize` bound of `diagonalWeak_recent_average_bound`, fed by
   `sqrt_blockSize_adaptedResponse_le_of_maximum_finite`.

Both `isDoubledResponseField_grad_sub` and `exists_restrict_solution_adaptedCellAtCenter` are
supplied
here.

## The size inputs are Loewner bounds

`blockSize`, `adaptedResponse`, `metricBlockNormSq`, `relSize` and `blockSharp` are not defined
on this tree.  The block-size inequality `blockSize A E ≤ B²` is written here as the LOEWNER
inequality `toFullBlockMat A ≤ B² • toFullBlockMat E`, which is the shape the size input `hAE`
actually takes, and `blockExcess A E` is written as the block spectral bound
`blockSpecBound (blockSub (normalizedBlock A E) (blockIdentity d))` — the quantity
`respAllScaleMax` (`ResponseBlockObjects.lean`) is already built from.  That substitution removes
the
`blockSize_le_one_add_blockExcess` step altogether, and with it the
`blockSpecBound`-subadditivity obstruction recorded in
`RecentHeadDefectHalves.lean`: the recentring bound `N ≤ (1 + β) I` is read
straight off `blockMatLoewnerLE_blockScale_blockSpecBound_self` (`RecentScaleEnergyRoute.lean`),
with no
operator norm anywhere.

**This module introduces exactly ONE definition, `adaptedDomainAt`, and it selects no
constant**: it is the per-`w` Chapter-2 domain whose carrier is `adaptedCellAtCenter q (t-n) w`, and
its two structure obligations are discharged inside the definition itself from
`isOpenBoundedConvexDomain_adaptedCellAtCenter` (`DiagonalDefectCarriers.lean`) and
`volume_adaptedCellAtCenter_toReal_pos` (`…:293`).  Its satisfiability is nevertheless exhibited
as an
explicit `∃` before any consumer statement.  Every other declaration below is a `theorem`.

## The `cellAverage`/`averageVec` bridge is definitional

`cellAverage V X` (`ResponseBlockObjects.lean`) and the pair
`(Book.Ch02.averageVec U Y.potential, Book.Ch02.averageVec U Y.flux)` are the same term:
`volumeAverage` (CG `CoarseGraining/Definitions.lean`) and `Book.Ch02.average`
(CG `Book/Ch02/Response.lean`) have identical bodies.  Two `rfl` lemmas record this, so the
response-size step costs two lines, not a lemma.
-/

open HCPolySupport.HighContrast (CoeffSpace blockScale blockSub coarseBlock
  isSymmetricBlockMat_coarseBlockMatrix matSqrt matSqrt_spec normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open HCPolySupport.Book.Ch02 MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The doubled response field of a difference of solutions

The `Y` construction for the recentred difference field, stated on `CoarseGraining`'s
carriers. -/

/-! ## The carrier bridge is definitional -/

/-! ## The recentred-difference energy map on this tree's carriers -/

/-- **The recentred-difference energy map.**  The `R`-metric size of the cell average of the
doubled difference of two optimizers is controlled by the cell energy of that difference, with
constant `k · e` given the two size inputs.

Three deliberate strengthenings:

* the domain is an ARBITRARY `U : Domain d`, not `adaptedDomainAt hq k w`, so the statement
  carries no geometry at all (the child cell can be supplied when a consumer wants it);
* `diagonalWeakMetricFactor m E ^ 2 * blockSize (adaptedResponse q k w a) E` is replaced by the
  two Loewner inputs `hEM`, `hAE` with arbitrary positive `k`, `e` — a BOUND on the size, not the
  size, which is the shape a consumer owns;
* the `Solution.ofAEEq`/`exists_pointwise_coeffOn_family_aeeq` preamble is NOT reproduced: it
  moves the sample `a` to an elliptic representative `c`, and this tree already carries that move
  separately (`cellAverage_optimizerField_respCoeffMinus_eq_at`,
  `DiagonalDefectCarriers.lean`).  The statement below is at the representative, so
  the two moves compose without duplication. -/
theorem recent_difference_metric_le {U : Domain d} {a : CoeffOn U}
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (u v : Book.Ch02.Solution U a)
    {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef)
    {E : BlockMat d} (hE : (toFullBlockMat E).PosDef) {k e : ℝ} (hk : 0 < k) (he : 0 < e)
    (hEM : toFullBlockMat E ≤ k • toFullBlockMat (respM0 F))
    (hAE : toFullBlockMat (Book.Ch02.coarseBlockMatrix U a) ≤ e • toFullBlockMat E) :
    blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (U : Set (Vec d)) (fun x =>
            optimizerField a.toCoeffField u x - optimizerField a.toCoeffField v x)))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (U : Set (Vec d)) (fun x =>
            optimizerField a.toCoeffField u x - optimizerField a.toCoeffField v x)))
      ≤ (k * e) *
        Book.Ch02.average U (fun x =>
          blockVecDot
            (optimizerField a.toCoeffField u x - optimizerField a.toCoeffField v x)
            (blockMatVecMul (Book.Ch02.blockMatrixField a x)
              (optimizerField a.toCoeffField u x - optimizerField a.toCoeffField v x))) :=
  energy_map_respM0_le_coarseStarred a hEll
    (Response.isDoubledResponseField_grad_sub hEll u v) hm hE hk he hEM hAE

/-! ## The RESPONSE-SIZE step

The bound `blockSize (adaptedResponse q k w a) E ≤ B²`,
written as the Loewner inequality that the size input `hAE` actually takes. -/

private theorem r2a_toFullBlockMat_blockIdentity :
    toFullBlockMat (Book.Ch02.blockIdentity d) = (1 : FullBlockMat d) := by
  ext (i | i) (j | j) <;>
    simp [toFullBlockMat, Book.Ch02.blockIdentity, Book.Ch02.blockDiag, Matrix.one_apply]

private theorem r2a_toFullBlockMat_blockScale_identity (c : ℝ) :
    toFullBlockMat (blockScale c (Book.Ch02.blockIdentity d)) =
      c • (1 : FullBlockMat d) := by
  rw [toFullBlockMat_blockScale, r2a_toFullBlockMat_blockIdentity]

private theorem r2a_toFullBlockMat_blockCongr (G A : BlockMat d) :
    toFullBlockMat (blockCongr G A) =
      (toFullBlockMat G)ᵀ * toFullBlockMat A * toFullBlockMat G := by
  rw [blockCongr, toFullBlockMat_ofFullBlockMat]

private theorem r2a_normalizedBlock_flat (P Q : BlockMat d) :
    toFullBlockMat (normalizedBlock P Q) =
      matSqrt (toFullBlockMat Q)⁻¹ * toFullBlockMat P * matSqrt (toFullBlockMat Q)⁻¹ := by
  rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]

private theorem r2a_qform_flat (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul A X) =
      toFullBlockVec X ⬝ᵥ (toFullBlockMat A *ᵥ toFullBlockVec X) := by
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]

private theorem r2a_qform_blockScale (c : ℝ) (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c A) X) =
      c * blockVecDot X (blockMatVecMul A X) := by
  rw [r2a_qform_flat, r2a_qform_flat, toFullBlockMat_blockScale, Matrix.smul_mulVec,
    dotProduct_smul,
    smul_eq_mul]

private theorem r2a_qform_identity (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (Book.Ch02.blockIdentity d) X) =
      toFullBlockVec X ⬝ᵥ toFullBlockVec X := by
  rw [r2a_qform_flat, r2a_toFullBlockMat_blockIdentity, Matrix.one_mulVec]

private theorem r2a_blockVecDot_sub_right (X Y Z : BlockVec d) :
    blockVecDot X (Y - Z) = blockVecDot X Y - blockVecDot X Z := by
  simp only [blockVecDot, vecDot, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]
  ring

private theorem r2a_smul_one_mono {c c' : ℝ} (h : c ≤ c') :
    (c • (1 : FullBlockMat d)) ≤ (c' • (1 : FullBlockMat d)) := by
  rw [Matrix.le_iff]
  have hsub : c' • (1 : FullBlockMat d) - c • (1 : FullBlockMat d) =
      (c' - c) • (1 : FullBlockMat d) := by rw [sub_smul]
  rw [hsub]
  exact (Matrix.PosSemidef.one).smul (by linarith only [h])

/-- The normalized block of a Hermitian block by a positive definite reference is
Hermitian.  `E^{-1/2}` is symmetric, so the congruence preserves symmetry. -/
theorem isHermitian_normalizedBlock {P Q : BlockMat d}
    (hP : (toFullBlockMat P).IsHermitian) (hQ : (toFullBlockMat Q).PosDef) :
    (toFullBlockMat (normalizedBlock P Q)).IsHermitian := by
  have hSIsymm : (matSqrt (toFullBlockMat Q)⁻¹)ᵀ = matSqrt (toFullBlockMat Q)⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using!
      (matSqrt_spec hQ.inv.posSemidef).1.isHermitian
  rw [r2a_normalizedBlock_flat, Matrix.IsHermitian,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, Matrix.transpose_mul,
    hSIsymm,
    show (toFullBlockMat P)ᵀ = toFullBlockMat P by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using! hP,
    Matrix.mul_assoc]

/-- **The recentring step, with NO operator norm.**  A Hermitian doubled block is
dominated by `(1 + β) I`, where `β` is the spectral positive part of its recentring `N - I`:

`N ≤ (1 + β) · I_{2d}`,  `β = blockSpecBound (N - I)`.

This replaces `blockSize_le_one_add_blockExcess`, which goes through the norm and therefore needs
`blockSpecBound` subadditivity — the obstruction recorded at
`RecentHeadDefectHalves.lean`.  Here `blockMatLoewnerLE_blockScale_blockSpecBound_self`
(`RecentScaleEnergyRoute.lean`) gives the Loewner
bound on `N - I` directly and the identity is added back on quadratic forms, so no norm and no
subadditivity is used. -/
theorem normalizedBlock_le_one_add_specBound {N : BlockMat d}
    (hN : (toFullBlockMat N).IsHermitian) :
    toFullBlockMat N ≤
      (1 + blockSpecBound (blockSub N (Book.Ch02.blockIdentity d))) • (1 : FullBlockMat d) := by
  set b : ℝ := blockSpecBound (blockSub N (Book.Ch02.blockIdentity d)) with hb
  have hloew : BlockMatLoewnerLE N (blockScale (1 + b) (Book.Ch02.blockIdentity d)) := by
    intro X
    have h := blockMatLoewnerLE_blockScale_blockSpecBound_self (blockSub N
      (Book.Ch02.blockIdentity d)) X
    rw [r2a_qform_blockScale, r2a_qform_identity, ← hb] at h
    have hs : blockVecDot X (blockMatVecMul (blockSub N (Book.Ch02.blockIdentity d)) X)
        = blockVecDot X (blockMatVecMul N X) - toFullBlockVec X ⬝ᵥ toFullBlockVec X := by
      rw [Response.blockMatVecMul_blockSub, r2a_blockVecDot_sub_right, r2a_qform_identity]
    rw [hs] at h
    rw [r2a_qform_blockScale, r2a_qform_identity]
    linarith only [h]
  have hH : (toFullBlockMat (blockScale (1 + b) (Book.Ch02.blockIdentity d))).IsHermitian := by
    rw [r2a_toFullBlockMat_blockScale_identity]
    simp [Matrix.IsHermitian]
  have hres := Analysis.matrixOrder_of_blockMatLoewnerLE hN hH hloew
  rwa [r2a_toFullBlockMat_blockScale_identity] at hres

/-- A bound on the normalized block against the identity lifts back to a bound of the
block against its reference: `E^{-1/2} P E^{-1/2} ≤ c I  ⟹  P ≤ c E`.  This is the tail of
`SharpOrderEnergyMap.lean` with the operator norm replaced by an arbitrary
constant, which is what a consumer owning only a BOUND has. -/
theorem le_smul_of_normalizedBlock_le {P Q : BlockMat d} {c : ℝ}
    (hQ : (toFullBlockMat Q).PosDef)
    (hc : toFullBlockMat (normalizedBlock P Q) ≤ c • (1 : FullBlockMat d)) :
    toFullBlockMat P ≤ c • toFullBlockMat Q := by
  have hSsymm : (matSqrt (toFullBlockMat Q))ᵀ = matSqrt (toFullBlockMat Q) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using!
      (matSqrt_spec hQ.posSemidef).1.isHermitian
  have hSS : matSqrt (toFullBlockMat Q) * matSqrt (toFullBlockMat Q) = toFullBlockMat Q :=
    (matSqrt_spec hQ.posSemidef).2
  have hSSI : matSqrt (toFullBlockMat Q) * matSqrt (toFullBlockMat Q)⁻¹ = 1 :=
    HCPolySupport.HighContrast.matSqrt_mul_matSqrt_inv hQ
  have hSIS : matSqrt (toFullBlockMat Q)⁻¹ * matSqrt (toFullBlockMat Q) = 1 :=
    HCPolySupport.HighContrast.matSqrt_inv_mul_matSqrt hQ
  have hcongr := Analysis.matrix_congr_le hc (matSqrt (toFullBlockMat Q))
  rw [hSsymm] at hcongr
  have hleft : matSqrt (toFullBlockMat Q) * toFullBlockMat (normalizedBlock P Q) *
      matSqrt (toFullBlockMat Q) = toFullBlockMat P := by
    rw [r2a_normalizedBlock_flat]
    calc
      matSqrt (toFullBlockMat Q) *
            (matSqrt (toFullBlockMat Q)⁻¹ * toFullBlockMat P * matSqrt (toFullBlockMat Q)⁻¹) *
            matSqrt (toFullBlockMat Q)
          = matSqrt (toFullBlockMat Q) * matSqrt (toFullBlockMat Q)⁻¹ * toFullBlockMat P *
            (matSqrt (toFullBlockMat Q)⁻¹ * matSqrt (toFullBlockMat Q)) := by noncomm_ring
      _ = toFullBlockMat P := by rw [hSSI, hSIS, Matrix.one_mul, Matrix.mul_one]
  have hright : matSqrt (toFullBlockMat Q) * (c • (1 : FullBlockMat d)) *
      matSqrt (toFullBlockMat Q) = c • toFullBlockMat Q := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hSS]
  rwa [hleft, hright] at hcongr

/-- **The size step, carrier-free.**  `Z ≤ c E` as soon as `c` dominates
`1 + blockSpecBound (normalizedBlock Z E - I)`.  This is exactly the bound
`blockSize A E ≤ B²` once `blockSize` is read as a Loewner bound rather than as a norm. -/
theorem le_smul_of_specBound_le {Z E : BlockMat d} {c : ℝ}
    (hZ : (toFullBlockMat Z).IsHermitian) (hE : (toFullBlockMat E).PosDef)
    (hc : 1 + blockSpecBound (blockSub (normalizedBlock Z E) (Book.Ch02.blockIdentity d)) ≤ c) :
    toFullBlockMat Z ≤ c • toFullBlockMat E :=
  le_smul_of_normalizedBlock_le hE
    ((normalizedBlock_le_one_add_specBound
      (isHermitian_normalizedBlock hZ hE)).trans (r2a_smul_one_mono hc))

/-- `1 + x ≤ B²` whenever `√x ≤ B - 1`.  The squaring bookkeeping of the response-size
step, on bare reals. -/
theorem one_add_le_sq {x B : ℝ} (hx : 0 ≤ x) (hB : Real.sqrt x ≤ B - 1) :
    1 + x ≤ B ^ 2 := by
  have h0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hxs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  nlinarith only [hB, h0, hxs]

/-- **Congruence transfer of a Loewner size bound.**  `Z ≤ c E` gives
`GᵀZG ≤ c GᵀEG` for ANY `G`: no positive definiteness, no invertibility, no symmetry.

This is the step that carries a bound stated in the `respMean` picture, which is where
`respAllScaleMax` (`ResponseBlockObjects.lean`) lives, into the `respEhatMinus` picture, which is
where the size input `hAE` lives, since `respEhatMinus = blockCongr (respG F) (respMean …)`
(`ResponseBlockObjects.lean`).  The equality
`h6a_blockOpNorm_recentred_blockCongr_eq` CANNOT be
used for this transfer, because it is an equality of OPERATOR NORMS while `respAllScaleMax`
carries a `blockSpecBound`, and `blockSpecBound ≤ ‖·‖` points the wrong way. -/
theorem blockCongr_le_smul {Z E : BlockMat d} (G : BlockMat d) {c : ℝ}
    (h : toFullBlockMat Z ≤ c • toFullBlockMat E) :
    toFullBlockMat (blockCongr G Z) ≤ c • toFullBlockMat (blockCongr G E) := by
  have hc := Analysis.matrix_congr_le h (toFullBlockMat G)
  rw [r2a_toFullBlockMat_blockCongr, r2a_toFullBlockMat_blockCongr]
  have hsm : (toFullBlockMat G)ᵀ * (c • toFullBlockMat E) * toFullBlockMat G =
      c • ((toFullBlockMat G)ᵀ * toFullBlockMat E * toFullBlockMat G) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rwa [hsm] at hc

/-- Every weighted cell excess is bounded by the all-scale maximum, on the branch
where that supremum is finite.  This is `weighted_excess_le_diagonalWeakMaximum_toReal`, whose
finiteness hypothesis `hfinite : diagonalWeakMaximum … ≠ ⊤` is here the real-valued `BddAbove` of
the same set (this tree's `respAllScaleMax` is an `sSup` in `ℝ`, not in `ℝ≥0∞`). -/
theorem weighted_specBound_le_respAllScaleMax (P : Measure (CoeffSpace d))
    (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d) (n : ℕ) {w : Fin d → ℤ}
    (hw : w ∈ triadicIndexBox d n)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))}) :
    (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))
      ≤ respAllScaleMax P γ jStar F t a := by
  rw [respAllScaleMax]
  exact le_csSup hbdd ⟨n, w, hw, rfl⟩

/-! ## The response-size step, assembled on the tree's own carriers -/

/-- **THE RESPONSE-SIZE STEP, in the `respMean` picture.**  The coarse response of an
aligned child cell sits below the scale-`t` reference mean, dilated by the square of the printed
geometric weight:

`𝐀(z + U_{t-n}; a) ≤ (1 + √M · 3^{ρn/2})² · E_t`,  `M = respAllScaleMax P γ jStar F t a`.

This is the `hsize` bound of `diagonalWeak_recent_average_bound`, fed by
`sqrt_blockSize_adaptedResponse_le_of_maximum_finite`.  The bound
`blockSize (adaptedResponse q k w a) E` is the Loewner statement here; `blockExcess` is the
`blockSpecBound` of the recentred normalized block, the very quantity `respAllScaleMax`
(`ResponseBlockObjects.lean`) is built from, so no excess carrier is needed either.
`sqrt_le_sqrt_mul_rpow_of_weighted_le` (`RecentHeadDefectHalves.lean`) supplies
the geometric-weight arithmetic, already in this tree. -/
theorem coarseBlock_le_sq_smul_respMean (P : Measure (CoeffSpace d))
    (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d) (n : ℕ) {w : Fin d → ℤ}
    (hw : w ∈ triadicIndexBox d n)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (hE : (toFullBlockMat (respMean P jStar F t)).PosDef) :
    toFullBlockMat (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a)
      ≤ (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) ^ 2
        • toFullBlockMat (respMean P jStar F t) := by
  set Z : BlockMat d :=
    coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a with hZdef
  set b : ℝ := blockSpecBound (blockSub (normalizedBlock Z (respMean P jStar F t))
    (Book.Ch02.blockIdentity d)) with hbdef
  have hb0 : 0 ≤ b := blockSpecBound_nonneg _
  have hwt : (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) * b ≤ respAllScaleMax P γ jStar F t
    a :=
    weighted_specBound_le_respAllScaleMax P γ jStar F t a n hw hbdd
  have hfac0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hM0 : 0 ≤ respAllScaleMax P γ jStar F t a :=
    le_trans (mul_nonneg hfac0 hb0) hwt
  have hsq : Real.sqrt b ≤ Real.sqrt (respAllScaleMax P γ jStar F t a) *
      (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2) :=
    sqrt_le_sqrt_mul_rpow_of_weighted_le n hM0 hwt
  have hZherm : (toFullBlockMat Z).IsHermitian :=
    (Analysis.toFullBlockMat_isHermitian_iff Z).mpr
      (isSymmetricBlockMat_coarseBlockMatrix _ (⇑a.1))
  exact le_smul_of_specBound_le hZherm hE
    (one_add_le_sq hb0 (by linarith only [hsq]))

/-- **THE RESPONSE-SIZE STEP, in the `Ehat^-` picture.**  The previous bound,
conjugated by the shear `G(F)`, which is exactly the passage from `respMean` to
`respEhatMinus = blockCongr (respG F) (respMean …)` (`ResponseBlockObjects.lean`).

A consumer closes the size input `hAE` from this by identifying its numerator: the coarse block of
the recentred field, `Book.Ch02.coarseBlockMatrix U (respCoeffMinus F a)`, is
`blockCongr (respG F) (coarseBlock U a)` — the shear identity
`coarseBlockMatrix_sub_skew_eq_blockCongr`
(`HCPoly/Entry/Response/Core/SkewShearCongruence.lean`, and not restated here). -/
theorem coarseBlock_congr_le_sq_smul_respEhatMinus (P : Measure (CoeffSpace d))
    (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d) (n : ℕ) {w : Fin d → ℤ}
    (hw : w ∈ triadicIndexBox d n)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (hE : (toFullBlockMat (respMean P jStar F t)).PosDef) :
    toFullBlockMat (blockCongr (respG F)
        (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a))
      ≤ (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) ^ 2
        • toFullBlockMat (respEhatMinus P jStar F t) := by
  rw [respEhatMinus]
  exact blockCongr_le_smul (respG F)
    (coarseBlock_le_sq_smul_respMean P γ jStar F t a n hw hbdd hE)

/-! ## The restriction step, and the per-`w` child cell as a Chapter-2 domain

The restriction step supplies `exists_restrict_solution` and
`exists_restrict_solution_adaptedCellAtCenter`.  A consumer needs them to
produce the SECOND argument of the recentred-difference energy map: the parent optimizer,
restricted to the child cell. -/

/-- An aligned adapted cell is nonempty.  This is proved from the PUBLIC
`volume_adaptedCellAtCenter_toReal_pos` (`DiagonalDefectCarriers.lean`), mirroring the
`private` `adaptedCellAtCenter_nonempty` (`…:366`). -/
theorem adaptedCellAtCenter_nonempty_of_isUnit_of_neZero (q : Mat d) (hq : IsUnit q)
  (k : ℤ)
    (w : Fin d → ℤ) : (adaptedCellAtCenter q k w).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hpos := volume_adaptedCellAtCenter_toReal_pos q hq k w
  rw [h] at hpos
  simp at hpos

/-- **The ONLY definition in this module.**  The aligned adapted cell `z + q□_k` as a
Chapter-2 domain, the per-`w` twin of `adaptedDomain`.

This definition selects NO constant and carries no inequality of its own: its
two structure obligations are Props about the carrier `adaptedCellAtCenter q k w`, and both are
discharged inside the definition itself, from `isOpenBoundedConvexDomain_adaptedCellAtCenter`
(`DiagonalDefectCarriers.lean`, PUBLIC) and the nonemptiness proved above.  Its
satisfiability is therefore constructive; it is nevertheless exhibited as an explicit `∃`,
before any consumer. -/
@[expose]
def adaptedDomainAt (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ) :
    Book.Ch02.Domain d :=
  { carrier := adaptedCellAtCenter q k w
    isDomain := isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w
    nonempty := adaptedCellAtCenter_nonempty_of_isUnit_of_neZero q hq k w }

@[simp] theorem adaptedDomainAt_carrier (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) :
    ((adaptedDomainAt q hq k w : Book.Ch02.Domain d) : Set (Vec d)) = adaptedCellAtCenter q k w
      := rfl

/-- The parent optimizer restricts to an admissible solution on every aligned child
cell of the triadic subdivision.  This is `exists_restrict_solution_adaptedCellAtCenter`, whose
membership hypothesis `hmem : adaptedCellCenter q j w ∈ adaptedCell q p` is here the tree's own
indexing hypothesis `w ∈ triadicIndexBox d n`, through `adaptedCellAtCenter_subset_adaptedCell`
. -/
theorem exists_restrict_solution_adaptedCellAtCenter (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (n : ℕ) {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) {lam Lam : ℝ}
    {b : CoeffOn (adaptedDomain q hq t)}
    {c : CoeffOn (adaptedDomainAt q hq (t - (n : ℤ)) w)}
    (hrep : c.toCoeffField = b.toCoeffField)
    (hEll : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) c.toCoeffField)
    (u : Book.Ch02.Solution (adaptedDomain q hq t) b) :
    ∃ z : Book.Ch02.Solution (adaptedDomainAt q hq (t - (n : ℤ)) w) c,
      z.toH1.grad = u.toH1.grad :=
  Response.exists_restrict_solution hrep (adaptedCellAtCenter_subset_adaptedCell q t n hw) hEll u

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Canonical response-maximizer selection: comparison and carrier measurability

The pointwise `Nonempty.some` used by
`ResponseCutoffEstimate.lean` is not definitionally the Chapter-2 canonical maximizer.
Nevertheless,
Chapter 2 uniqueness shows that their gradients, fluxes, and every subcell average of the doubled
state agree almost everywhere.  The second part records, on the library's actual coefficient
carrier, the smooth entry-test measurability needed by the Galerkin selection construction.
-/

open HCPolySupport.HighContrast (CoeffSpace ae_abs_entry_le_of_aeUniformlyEllipticField
  coeffPairing)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The Chapter-2 canonical maximizer, repackaged on the scalar-response carrier of the entry
route. -/
@[expose]
def scalarCanonicalMaximizerOfCoeffOn {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U)
    (p q : Vec d) : ScalarCanonicalMaximizer (U : Set (Vec d)) p q a.toCoeffField where
  toAHarmonicFunctionMeanZero :=
    ⟨(Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U a) p q).toSolution,
      (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U a) p q).meanZero⟩
  isMaximizer := book_isResponseMaximizer_iff.mp
    (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U a) p q).isMaximizer

/-- The harmonic-function projection of the preceding canonical package. -/
@[expose]
def canonicalAHarmonicFunctionOfCoeffOn {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U)
    (p q : Vec d) : AHarmonicFunction a.toCoeffField (U : Set (Vec d)) :=
  (scalarCanonicalMaximizerOfCoeffOn a p q).toAHarmonicFunctionMeanZero.toAHarmonicFunction

/-- STEP ZERO.  An arbitrary scalar canonical maximizer (in particular the fresh
`Nonempty.some` in `ResponseCutoffEstimate.lean`) has the same gradient a.e. as the specific
Chapter-2
canonical family used by the measurable-selection construction. -/
theorem scalarCanonicalMaximizer_grad_ae_eq_canonicalOfCoeffOn
    {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U) (p q : Vec d)
    (v : ScalarCanonicalMaximizer (U : Set (Vec d)) p q a.toCoeffField) :
    (canonicalAHarmonicFunctionOfCoeffOn a p q).toH1.grad
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad := by
  exact Book.Ch02.canonicalMaximizer_sameGradientAE_of_isResponseMaximizer
    (book_isResponseMaximizer_iff.mpr v.isResponseMaximizer)

/-- Transport a specified scalar maximizer across an a.e. equality of coefficients.  Unlike the
existence-only bridge `nonempty_scalarCanonicalMaximizer_of_aeEq`
(`HCPoly/Entry/Response/Core/ScalarMaximizerExistence.lean`), this keeps the chosen object visible
for STEP ZERO. -/
@[expose]
def scalarCanonicalMaximizerOfAEEq {U : Set (Vec d)} {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn U] b) (p q : Vec d)
    (v : ScalarCanonicalMaximizer U p q a) : ScalarCanonicalMaximizer U p q b where
  toAHarmonicFunctionMeanZero :=
    ⟨Response.aHarmonicOfAEEq h
      v.toAHarmonicFunctionMeanZero.toAHarmonicFunction,
      v.toAHarmonicFunctionMeanZero.meanZero⟩
  isMaximizer := by
    intro w
    have key := v.isMaximizer (Response.aHarmonicOfAEEq h.symm w)
    have h1 : volumeAverage U (scalarResponseIntegrand U b p q w) =
        volumeAverage U (scalarResponseIntegrand U a p q
          (Response.aHarmonicOfAEEq h.symm w)) :=
      volumeAverage_scalarResponseIntegrand_congr h.symm p q w _ (fun _ => rfl)
    have h2 : volumeAverage U
          (scalarResponseIntegrand U a p q
            v.toAHarmonicFunctionMeanZero.toAHarmonicFunction) =
        volumeAverage U (scalarResponseIntegrand U b p q
          (Response.aHarmonicOfAEEq h
            v.toAHarmonicFunctionMeanZero.toAHarmonicFunction)) :=
      volumeAverage_scalarResponseIntegrand_congr h p q _ _ (fun _ => rfl)
    rw [h1, ← h2]
    exact key

/-- STEP ZERO on the actual coefficient shape.  If `b` only has a pointwise elliptic
representative `f`, the arbitrary `Nonempty.some` maximizer for `b` still agrees a.e. in gradient
with the Chapter-2 canonical maximizer for `f`, after the canonical null-set transport. -/
theorem scalarCanonicalMaximizer_grad_ae_eq_canonicalOfAEEq
    {U : Book.Ch02.Domain d} {b f : CoeffField d} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) f)
    (h : b =ᵐ[volumeMeasureOn (U : Set (Vec d))] f) (p q : Vec d)
    (v : ScalarCanonicalMaximizer (U : Set (Vec d)) p q b) :
    (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn hlam hle hEll) p q).toH1.grad
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad := by
  let vf : ScalarCanonicalMaximizer (U : Set (Vec d)) p q f :=
    scalarCanonicalMaximizerOfAEEq h p q v
  simpa [vf, scalarCanonicalMaximizerOfAEEq, Response.aHarmonicOfAEEq] using
    scalarCanonicalMaximizer_grad_ae_eq_canonicalOfCoeffOn
      (coeffOnOfIsEllipticFieldOn hlam hle hEll) p q vf

/-- The comparison includes the flux: the coefficient equality and gradient uniqueness identify
the complete doubled state on the parent cell. -/
theorem optimizerField_scalarCanonicalMaximizer_ae_eq_canonicalOfAEEq
    {U : Book.Ch02.Domain d} {b f : CoeffField d} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) f)
    (h : b =ᵐ[volumeMeasureOn (U : Set (Vec d))] f) (p q : Vec d)
    (v : ScalarCanonicalMaximizer (U : Set (Vec d)) p q b) :
    optimizerField f
        (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn hlam hle hEll) p q)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    optimizerField b v.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
  filter_upwards [scalarCanonicalMaximizer_grad_ae_eq_canonicalOfAEEq
    hlam hle hEll h p q v, h] with x hxg hxb
  simp only [optimizerField, hxg, ← hxb]

/-- In particular every strict subcell average (`n ≥ 1` as well as `n = 0`) of the ad hoc
maximizer is determined by the measurable canonical selection. -/
theorem cellAverage_scalarCanonicalMaximizer_eq_canonicalOfAEEq
    {U : Book.Ch02.Domain d} {V : Set (Vec d)} (hVU : V ⊆ (U : Set (Vec d)))
    {b f : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) f)
    (h : b =ᵐ[volumeMeasureOn (U : Set (Vec d))] f) (p q : Vec d)
    (v : ScalarCanonicalMaximizer (U : Set (Vec d)) p q b) :
    cellAverage V
        (optimizerField f
          (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn hlam hle hEll) p q)) =
      cellAverage V (optimizerField b v.toAHarmonicFunctionMeanZero.toAHarmonicFunction) :=
  cellAverage_congr_ae hVU
    (optimizerField_scalarCanonicalMaximizer_ae_eq_canonicalOfAEEq
      hlam hle hEll h p q v)

/-- The library's actual a.e.-quotient coefficient carrier, realized in CG's regular carrier. -/
@[expose]
def selectionRegCoeffField (a : CoeffSpace d) : RegCoeffField d where
  toFun := ⇑a.1
  entry_measurable := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp a.1.measurable)
  entry_locInt := by
    intro i j
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨M, -, hM⟩ := ae_abs_entry_le_of_aeUniformlyEllipticField a.2 hK.isBounded
    refine Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      ((continuous_id.matrix_elem i j).comp_aestronglyMeasurable a.1.aestronglyMeasurable) (M :=
        M) ?_
    filter_upwards [ae_restrict_of_ae hM, ae_restrict_mem hK.measurableSet] with x hx hxK
    simpa [Real.norm_eq_abs] using hx hxK i j

@[simp] theorem selectionRegCoeffField_toFun (a : CoeffSpace d) :
    (selectionRegCoeffField a).toFun = (⇑a.1 : CoeffField d) := rfl

/-- The `hEntry` obligation of the Galerkin selection chain is dischargeable from the
actual coefficient carrier and its global smooth-test sigma algebra; it is not an additional
law or `RawOutput` hypothesis. -/
theorem measurable_entryTest_selectionRegCoeffField (i j : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcpt : HasCompactSupport φ) :
    Measurable (fun a : CoeffSpace d ↦ entryTestR i j φ (selectionRegCoeffField a)) := by
  have heq : (fun a : CoeffSpace d ↦ entryTestR i j φ (selectionRegCoeffField a)) =
      coeffPairing (Pi.single j 1) (Pi.single i 1) φ := by
    funext a
    simp [entryTestR, coeffPairing, selectionRegCoeffField, vecDot_single_left,
      matVecMul_single]
  rw [heq]
  exact Annealed.measurable_coeffPairing_local (U := Set.univ) (Pi.single j 1) (Pi.single i 1)
    ⟨hφ, hcpt, Set.subset_univ _⟩

/-! ## The two response-coefficient transformations

The Galerkin selection API uses `RegCoeffField`, whereas the response argument is written on the
raw carrier as `a ↦ a - respg F` or `a ↦ aᵀ + respg F`.  The following carrier lifts make
the algebraic generator transport explicit. -/

/-- The regular-carrier lift of `respCoeffMinus F`. -/
@[expose]
def selectionRespCoeffMinusReg (F : BlockMat d) (a : CoeffSpace d) : RegCoeffField d :=
  selectionRegCoeffField a + (-1 : ℝ) • RegCoeffField.constRegCoeffField (respg F)

@[simp] theorem selectionRespCoeffMinusReg_toFun (F : BlockMat d) (a : CoeffSpace d) :
    (selectionRespCoeffMinusReg F a).toFun = respCoeffMinus F a := by
  funext x i j
  simp [selectionRespCoeffMinusReg, respCoeffMinus, sub_eq_add_neg]

/-- Smooth compactly-supported entry tests of `respCoeffMinus F` are measurable on the actual
coefficient carrier. -/
theorem measurable_entryTest_selectionRespCoeffMinusReg (F : BlockMat d) (i j : Fin d)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcpt : HasCompactSupport φ) :
    Measurable (fun a : CoeffSpace d ↦
      entryTestR i j φ (selectionRespCoeffMinusReg F a)) := by
  have hprobe : IsProbeR φ := IsProbeR.of_smooth hφ hcpt
  have heq : (fun a : CoeffSpace d ↦
      entryTestR i j φ (selectionRespCoeffMinusReg F a)) =
      fun a ↦ entryTestR i j φ (selectionRegCoeffField a) +
        (-1 : ℝ) * entryTestR i j φ (RegCoeffField.constRegCoeffField (respg F)) := by
    funext a
    rw [selectionRespCoeffMinusReg, entryTestR_add i j hprobe,
      entryTestR_smul]
  rw [heq]
  exact (measurable_entryTest_selectionRegCoeffField i j hφ hcpt).add measurable_const

/-- The regular-carrier lift of `respCoeffPlus F`. -/
@[expose]
def selectionRespCoeffPlusReg (F : BlockMat d) (a : CoeffSpace d) : RegCoeffField d :=
  adjointReg (selectionRegCoeffField a) + RegCoeffField.constRegCoeffField (respg F)

@[simp] theorem selectionRespCoeffPlusReg_toFun (F : BlockMat d) (a : CoeffSpace d) :
    (selectionRespCoeffPlusReg F a).toFun = respCoeffPlus F a := by
  funext x i j
  simp [selectionRespCoeffPlusReg, respCoeffPlus, matTranspose]

/-- Smooth compactly-supported entry tests of `respCoeffPlus F` are measurable on the actual
coefficient carrier; transpose merely swaps the tested indices. -/
theorem measurable_entryTest_selectionRespCoeffPlusReg (F : BlockMat d) (i j : Fin d)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcpt : HasCompactSupport φ) :
    Measurable (fun a : CoeffSpace d ↦
      entryTestR i j φ (selectionRespCoeffPlusReg F a)) := by
  have hprobe : IsProbeR φ := IsProbeR.of_smooth hφ hcpt
  have heq : (fun a : CoeffSpace d ↦
      entryTestR i j φ (selectionRespCoeffPlusReg F a)) =
      fun a ↦ entryTestR j i φ (selectionRegCoeffField a) +
        entryTestR i j φ (RegCoeffField.constRegCoeffField (respg F)) := by
    funext a
    rw [selectionRespCoeffPlusReg, entryTestR_add i j hprobe,
      entryTestR_adjointReg]
  rw [heq]
  exact (measurable_entryTest_selectionRegCoeffField j i hφ hcpt).add measurable_const

end

end HCPolySupport.HighContrast.Multiscale
end
