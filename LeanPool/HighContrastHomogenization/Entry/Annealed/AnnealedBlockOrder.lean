/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.ContrastOrder
public import LeanPool.HighContrastHomogenization.Entry.Analysis.PositiveGapSupport
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedCellFoundations
public import LeanPool.HighContrastHomogenization.Entry.Annealed.Normalization
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.Geometry.StandardCell
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.DriftAdvance
public import LeanPool.HighContrastHomogenization.Entry.Source.CoarseSubadditivity
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.DetTransport
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyRows
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import LeanPool.HighContrastHomogenization.Setup.LocalSigmaFields
public import LeanPool.HighContrastHomogenization.Setup.Response
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockMatrixProperties
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.CoarseBounds

/-!
# High-contrast homogenization: Entry.Annealed.AnnealedBlockOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Annealed Block Order

The order-theoretic comparisons of the annealed block that serve
`p.fixed.geometry.parent.child.recurrence`: Loewner monotonicity of the annealed mean
under refinement, antitonicity of the annealed contrast in the scale, and the induced
order of the full log-determinant.
-/

section
/-!
## Decreasing actual adapted means

`p.fixed.geometry.parent.child.recurrence`: finite aligned subadditivity, integer stationarity,
and genuine
finite entrywise expectations. No averaging, positive-gap, or recurrence
is used in this direction. Equality of generations is included.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  adaptedMean annealedBlock blockMatEntry_annealedBlock coarseBlock
  toFullBlockMat_eq_blockMatEntry)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate centeredCube
  standardCellCenter)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory Geometry Set

noncomputable section

/-- A finite adapted partition satisfies the actual full block inequality. -/
theorem coarseBlock_adapted_finite_partition {d : ℕ} [NeZero d]
    {ι : Type*} {s : Set ι} (hs : s.Finite)
    (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d)
    (qi : ι → Mat d) (hqi : ∀ i ∈ s, IsUnit (qi i)) (ji : ι → ℤ) (yi : ι → Vec d)
    (a : CoeffSpace d) :
    let W := adaptedCellTranslate q j y
    let U := fun i => adaptedCellTranslate (qi i) (ji i) (yi i)
    (∀ i ∈ s, U i ⊆ W) → s.PairwiseDisjoint U →
      volume (W \ ⋃ i ∈ s, U i) = 0 →
      BlockMatLoewnerLE (coarseBlock W a) (ofFullBlockMat (∑' i : s,
        ((volume (U i)).toReal / (volume W).toReal) • toFullBlockMat (coarseBlock (U i) a))) := by
  intro W U hsub hdisj hnull
  let := hs.fintype
  have hWfin : volume W ≠ ⊤ := Transport.volume_adaptedCellTranslate_ne_top q j y
  let : IsFiniteMeasure (volumeMeasureOn W) := ⟨by simpa [volumeMeasureOn] using hWfin.lt_top⟩
  have hWpos : 0 < volume W := by
    dsimp [W]
    rw [volume_adaptedCellTranslate]
    have hdet : q.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det q).mp hq).ne_zero
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (abs_pos.mpr hdet)).ne'
      (ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (by positivity)) d).ne'
  have hWvol : (volume W).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hWpos.ne', hWfin⟩
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_adapted q hq j y a
  apply Source.block_tsum_of_response_partition hs.countable (isOpen_adaptedCellTranslate hq j y)
    hWvol (fun i hi => isOpen_adaptedCellTranslate (hqi i hi) (ji i) (yi i))
    hsub hdisj hnull hEll (coarseBlock W a) (fun i => coarseBlock (U i) a) _ _ (hasSum_fintype
      _).summable
  · intro p r
    rw [← responseJ_congr_of_ae_eq (ae_restrict_of_ae hae)]
    exact responseJ_eq_coarseBlock_adapted q hq j y a p r
  · intro i hi p r
    rw [← responseJ_congr_of_ae_eq (ae_restrict_of_ae hae)]
    exact responseJ_eq_coarseBlock_adapted (qi i) (hqi i hi) (ji i) (yi i) a p r

/-- Pathwise aligned parent order with the literal finite equal-weight average. -/
theorem coarseBlock_aligned_parent_le {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (j : ℤ) (h : ℕ) (a : CoeffSpace d) :
    let s := {w : Fin d → ℤ | standardCellCenter j w ∈ centeredCube d (j + h)}
    let := (alignedCenterSet_finite_card d j h).1.fintype
    BlockMatLoewnerLE (coarseBlock (adaptedCell q (j + h)) a)
      (ofFullBlockMat (∑ w : s, ((3 : ℝ) ^ (d * h))⁻¹ •
        toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a))) := by
  intro s
  let := (alignedCenterSet_finite_card d j h).1.fintype
  have hW : adaptedCellTranslate q (j + h) 0 = adaptedCell q (j + h) := by
    simp [adaptedCellTranslate]
  obtain ⟨hsub, hdisj, hnull⟩ := aligned_adapted_partition q hq j h
  have hp := coarseBlock_adapted_finite_partition (alignedCenterSet_finite_card d j h).1
    q hq (j + h) 0 (fun _ => q) (fun _ _ => hq) (fun _ => j)
    (fun w => adaptedCellCenter q j w) a
  dsimp only at hp
  rw [hW] at hp
  have hp' := hp hsub hdisj hnull
  change BlockMatLoewnerLE _ (ofFullBlockMat (∑' w : s,
    ((volume (adaptedCellAtCenter q j w)).toReal / (volume (adaptedCell q (j + h))).toReal) •
      toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a))) at hp'
  simpa only [tsum_fintype, aligned_adapted_volume_ratio q hq j h] using hp'

/-- Integer stationarity identifies each aligned child's actual annealed matrix. -/
theorem annealedBlock_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ) :
    annealedBlock P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) =
      adaptedMean P (explicitRoundedGrid jStar m) j := by
  obtain ⟨z, hz⟩ := adaptedCellCenter_eq_intTranslation jStar m hj w
  have he := Source.annealedBlock_adapted_add_intTranslation P hstat
    (explicitRoundedGrid jStar m) (isUnit_roundedGrid hjStar hm) j 0 z
  simpa [adaptedCellAtCenter, hz, adaptedCellTranslate, adaptedMean, HighContrast.adaptedCell,
    HighContrast.centeredCube] using he

/-- Actual adapted annealed blocks decrease across every admissible pair, including j=k. -/
theorem adaptedMean_antitone (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j k : ℤ)
    (hj : (jStar : ℤ) ≤ j) (hjk : j ≤ k) :
    BlockMatLoewnerLE (adaptedMean P (explicitRoundedGrid jStar m) k)
      (adaptedMean P (explicitRoundedGrid jStar m) j) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨h, rfl⟩ : ∃ h : ℕ, k = j + h :=
    ⟨(k - j).toNat, by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
  let q := explicitRoundedGrid jStar m
  let s := {w : Fin d → ℤ | standardCellCenter j w ∈ centeredCube d (j + h)}
  let := (alignedCenterSet_finite_card d j h).1.fintype
  let ρ : ℝ := ((3 : ℝ) ^ (d * h))⁻¹
  let B : CoeffSpace d → BlockMat d := fun a =>
    ofFullBlockMat (∑ w : s, ρ • toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a))
  have hc (w : s) : SchattenMemLp P 1 (fun a => coarseBlock (adaptedCellAtCenter q j w) a) :=
    Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag
      jStar hjStar m hm j (adaptedCellCenter q j w) 1 le_rfl
  have hB : SchattenMemLp P 1 B := Source.memLqSchatten_finset_sum le_rfl
    Finset.univ (fun _ : s => ρ) (fun w a => coarseBlock (adaptedCellAtCenter q j w) a)
    (fun w _ => hc w)
  have hF : HasIntegrableCoarseBlock P (adaptedCell q (j + h)) := by
    simpa [adaptedCellTranslate] using hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S
      hstat hdag jStar hjStar m hm (j + h) 0
  have hentry (α β : BlockCoord d) : (∫ a, blockMatEntry (B a) α β ∂P) =
      blockMatEntry (adaptedMean P q j) α β := by
    have hw (w : s) : (∫ a, blockMatEntry (coarseBlock (adaptedCellAtCenter q j w) a) α β ∂P) =
        blockMatEntry (adaptedMean P q j) α β := by
      rw [← blockMatEntry_annealedBlock,
        annealedBlock_adaptedCellAtCenter P hstat jStar hjStar m hm j hj w]
    simp only [B, blockMatEntry_ofFullBlockMat, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, toFullBlockMat_eq_blockMatEntry]
    rw [integral_finsetSum _ (fun w _ => ((hc w).integrable_entry le_rfl α β).const_mul ρ)]
    simp only [integral_const_mul, hw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : Fintype.card s = 3 ^ (d * h) := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      exact (alignedCenterSet_finite_card d j h).2
    rw [hcard]
    dsimp [ρ]
    push_cast
    field_simp
  have ho := Analysis.blockMatLoewnerLE_integral hF (hB.integrable_entry le_rfl)
    (ae_of_all P fun a => coarseBlock_aligned_parent_le q (isUnit_roundedGrid hjStar hm) j h a)
  have hleft : ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (coarseBlock (adaptedCell q (j + h)) a) α β ∂P) =
      adaptedMean P q (j + h) := by
    rw [← ofFullBlockMat_toFullBlockMat (adaptedMean P q (j + h))]
    congr 1
    funext α β
    exact (blockMatEntry_annealedBlock P _ α β).symm
  have hright : ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (B a) α β ∂P) =
      adaptedMean P q j := by
    rw [← ofFullBlockMat_toFullBlockMat (adaptedMean P q j)]
    congr 1
    funext α β
    exact hentry α β
  rwa [hleft, hright] at ho

end

end HCPolySupport.HighContrast.Annealed
end

section
/-!
## Monotonicity of the annealed contrast in the scale

The Euclidean annealed contrast `Θ_m` of `e.Theta.m` is the intrinsic contrast of the
annealed block of the centered cube `□_m`.  Under the standing stationary law the annealed
blocks of the centered cubes decrease in the doubled Loewner order as the scale grows, and
the intrinsic contrast is monotone in that order.  Hence `Θ_m` is nonincreasing in `m` beyond
the rounding scale: a contrast bound at one scale is a contrast bound at every larger scale,
which is the form in which `t.polynomial.entry` is consumed.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean annealedContrast blockContrast)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory

noncomputable section

/-- Positivity of the flattened doubled matrix is positivity of the doubled quadratic
form. -/
private theorem blockPosDef_of_toFullBlockMat_posDef {d : ℕ} {A : BlockMat d}
    (hA : (toFullBlockMat A).PosDef) : Book.Ch02.BlockPosDef A := by
  intro X hX
  have hvec : toFullBlockVec X ≠ 0 := by
    intro h
    apply hX
    have h' := congrArg ofFullBlockVec h
    rw [ofFullBlockVec_toFullBlockVec] at h'
    simpa using! h'
  have hq := hA.dotProduct_mulVec_pos hvec
  have hstar : star (toFullBlockVec X) = toFullBlockVec X := rfl
  rw [hstar, ← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec] at hq
  exact hq

/-- The Euclidean annealed contrast is the intrinsic contrast of the adapted mean at the
identity metric: the adapted cell of the identity grid is the centered cube. -/
private theorem annealedContrast_eq_blockContrast_adaptedMean {d : ℕ}
    (P : Measure (CoeffSpace d)) (m : ℤ) :
    annealedContrast P m = blockContrast (adaptedMean P (1 : Mat d) m) := by
  rw [annealedContrast, adaptedMean, Geometry.adaptedCell_one,
    ← Geometry.centeredCube_eq_standardCell]

/-- **The annealed contrast is nonincreasing in the scale.**  Under the standing stationary
law, `Θ_k ≤ Θ_j` whenever `j ≤ k` are at least the rounding scale: the annealed block of
`□_k` lies below that of `□_j` in the doubled Loewner order, and the intrinsic contrast
of `e.Theta.m` is monotone in that order. -/
theorem annealedContrast_antitone (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (j k : ℤ)
    (hj : (jStar : ℤ) ≤ j) (hjk : j ≤ k) :
    annealedContrast P k ≤ annealedContrast P j := by
  let : NeZero d := ⟨by omega⟩
  have hle : BlockMatLoewnerLE (adaptedMean P (1 : Mat d) k) (adaptedMean P (1 : Mat d) j) := by
    simpa [Geometry.explicitRoundedGrid_one (d := d) jStar] using
      adaptedMean_antitone d hd P γ E Ψ K S hstat hdag jStar hjStar
        (1 : Mat d) (Geometry.one_posDef d) j k hj hjk
  have hpos : Book.Ch02.BlockPosDef (adaptedMean P (1 : Mat d) k) := by
    have h := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar
      (1 : Mat d) (Geometry.one_posDef d) k
    rw [Geometry.explicitRoundedGrid_one] at h
    exact blockPosDef_of_toFullBlockMat_posDef h
  rw [annealedContrast_eq_blockContrast_adaptedMean, annealedContrast_eq_blockContrast_adaptedMean]
  exact blockContrast_le_of_blockMatLoewnerLE (isSymmetricBlockMat_annealedBlock P _) hpos
    (isSymmetricBlockMat_annealedBlock P _) hle

end

end HCPolySupport.HighContrast.Annealed
end

section
/-!
## Ordered means and the coefficient-one determinant loss

`p.fixed.geometry.parent.child.recurrence`. Full doubled matrices are normalized without a
commutation assumption. The determinant is the full 2d determinant, with no root.
-/

open HCPolySupport.HighContrast (CoeffSpace blockLogDet blockSub blockTrace matSqrt
  normalizedBlock)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory Geometry
open scoped MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-- Full matrix order and the CG quadratic block order agree on symmetric blocks. -/
theorem fullBlock_le_iff {d : ℕ} {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian) :
    toFullBlockMat A ≤ toFullBlockMat B ↔ BlockMatLoewnerLE A B := by
  constructor
  · intro h X
    have hn := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg (toFullBlockVec X)
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hn
    have heA := dotProduct_toFullBlockVec X (blockMatVecMul A X)
    have heB := dotProduct_toFullBlockVec X (blockMatVecMul B X)
    rw [toFullBlockVec_blockMatVecMul] at heA heB
    rw [heA, heB] at hn
    exact mul_le_mul_of_nonneg_left (sub_nonneg.mp hn) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · intro h
    apply Matrix.le_iff.mpr
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_
    intro x
    have hx := h (ofFullBlockVec x)
    simp only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockVec_ofFullBlockVec] at hx
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    linarith only [hx]

/-- The operator norm above identity is bounded by one plus the full trace excess. -/
theorem blockOpNorm_le_one_add_trace {d : ℕ} (M : BlockMat d)
    (hM : (toFullBlockMat M).IsHermitian)
    (hIM : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) M) :
    blockOpNorm M ≤ 1 + blockTrace (blockSub M (Book.Ch02.blockIdentity d)) := by
  have hI : toFullBlockMat (Book.Ch02.blockIdentity d) = 1 := by
    ext α β
    cases α <;> cases β <;>
      simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat, Matrix.one_apply]
  have hIP : (1 : FullBlockMat d) ≤ toFullBlockMat M := by
    rw [← hI]
    exact (fullBlock_le_iff (by rw [hI]; exact Matrix.isHermitian_one) hM).2 hIM
  have hsub : toFullBlockMat (blockSub M (Book.Ch02.blockIdentity d)) = toFullBlockMat M - 1 := by
    rw [← hI]
    ext α β
    cases α <;> cases β <;> rfl
  have hp : (toFullBlockMat (blockSub M (Book.Ch02.blockIdentity d))).PosSemidef := by
    rw [hsub]
    exact Matrix.le_iff.mp hIP
  have hnorm : ‖toFullBlockMat (blockSub M (Book.Ch02.blockIdentity d))‖ ≤
      blockTrace (blockSub M (Book.Ch02.blockIdentity d)) :=
    (Analysis.blockOpNorm_le_absSchattenNorm hp.isHermitian le_rfl).trans
      (Analysis.absSchattenNorm_le_blockTrace hp le_rfl)
  calc
    blockOpNorm M = ‖(toFullBlockMat M - 1) + 1‖ := by simp only [sub_add_cancel, blockOpNorm]
    _ ≤ ‖toFullBlockMat M - 1‖ + ‖(1 : FullBlockMat d)‖ := norm_add_le _ _
    _ ≤ blockTrace (blockSub M (Book.Ch02.blockIdentity d)) + 1 := by
      rw [← hsub]
      apply add_le_add hnorm
      rcases isEmpty_or_nonempty (BlockCoord d) with hi | hi
      · let := hi
        have he : (1 : FullBlockMat d) = 0 := Subsingleton.elim _ _
        rw [he, norm_zero]
        norm_num
      · let := hi
        simp
    _ = _ := add_comm _ _

/-- The full determinant controls normalized order, loss, operator norm, trace and O7. -/
theorem normalizedBlock_order_consequences {d : ℕ} (Q : ℕ) (F G : BlockMat d)
    (hF : (toFullBlockMat F).PosDef) (hG : (toFullBlockMat G).PosDef)
    (hGF : BlockMatLoewnerLE G F) :
    BlockMatLoewnerLE (Book.Ch02.blockIdentity d) (normalizedBlock F G) ∧
      0 ≤ blockLogDet F - blockLogDet G ∧
      (toFullBlockMat (normalizedBlock F G)).det = Real.exp (blockLogDet F - blockLogDet G) ∧
      blockOpNorm (normalizedBlock F G) ≤ Real.exp (blockLogDet F - blockLogDet G) ∧
      blockTrace (blockSub (normalizedBlock F G) (Book.Ch02.blockIdentity d)) ≤
        Real.exp (blockLogDet F - blockLogDet G) - 1 ∧
      0 ≤ meanPenalty Q (normalizedBlock F G) := by
  let M := normalizedBlock F G
  have hS := Multiscale.matSqrt_inv_posDef_full hG
  have hp : (toFullBlockMat M).PosSemidef := by
    simpa only [M, normalizedBlock, toFullBlockMat_ofFullBlockMat, hS.isHermitian.eq] using
      hF.posSemidef.conjTranspose_mul_mul_same (matSqrt (toFullBlockMat G)⁻¹)
  have hIP : (1 : FullBlockMat d) ≤ toFullBlockMat M := by
    simpa only [M, normalizedBlock, toFullBlockMat_ofFullBlockMat] using
      Recurrence.one_le_normalize hG ((fullBlock_le_iff hG.isHermitian hF.isHermitian).2 hGF)
  have hI : toFullBlockMat (Book.Ch02.blockIdentity d) = 1 := by
    ext α β
    cases α <;> cases β <;>
      simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat, Matrix.one_apply]
  have hIM : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) M := by
    apply (fullBlock_le_iff (by rw [hI]; exact Matrix.isHermitian_one) hp.isHermitian).1
    simpa only [hI] using hIP
  have hsym : IsSymmetricBlockMat M := (Analysis.toFullBlockMat_isHermitian_iff M).1 hp.isHermitian
  have htrace := Multiscale.normalizedMean_trace_sub_identity_le F G hF hG hGF
  have hnonneg := Analysis.blockTrace_identity_sub_nonneg M hsym hIM
  have hloss : 0 ≤ blockLogDet F - blockLogDet G := by
    apply Real.one_le_exp_iff.mp
    linarith only [htrace, hnonneg]
  have hdet := Multiscale.det_normalizedBlock_eq_exp F G hF hG
  have hnorm : blockOpNorm M ≤ Real.exp (blockLogDet F - blockLogDet G) := by
    have hb := blockOpNorm_le_one_add_trace M hp.isHermitian hIM
    linarith only [hb, htrace]
  exact ⟨hIM, hloss, hdet, hnorm, htrace, Analysis.meanPenalty_nonneg Q M hsym hIM⟩

/-- The complete ordered-mean consequences with all stochastic guards discharged. -/
theorem adaptedMean_order_consequences (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j k : ℤ)
    (hj : (jStar : ℤ) ≤ j) (hjk : j ≤ k) :
    let q := explicitRoundedGrid jStar m
    BlockMatLoewnerLE (Book.Ch02.blockIdentity d) (relMean P q j k) ∧
      0 ≤ detIncrement P q j k ∧
      (toFullBlockMat (relMean P q j k)).det = Real.exp (detIncrement P q j k) ∧
      blockOpNorm (relMean P q j k) ≤ Real.exp (detIncrement P q j k) ∧
      blockTrace (blockSub (relMean P q j k) (Book.Ch02.blockIdentity d)) ≤
        Real.exp (detIncrement P q j k) - 1 ∧
      0 ≤ meanPenalty (bigQ d γ) (relMean P q j k) := by
  exact normalizedBlock_order_consequences (bigQ d γ) _ _
    (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm j)
    (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm k)
    (adaptedMean_antitone d hd P γ E Ψ K S hstat hdag jStar hjStar m hm j k hj hjk)

/-- O2 for every pair of admissible generations in the actual rounded grid. -/
theorem logDetLoss_nonneg (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j k : ℤ)
    (hj : (jStar : ℤ) ≤ j) (hjk : j ≤ k) :
    0 ≤ detIncrement P (explicitRoundedGrid jStar m) j k :=
  (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hjStar m hm j k hj hjk).2.1

end

end HCPolySupport.HighContrast.Annealed
end
