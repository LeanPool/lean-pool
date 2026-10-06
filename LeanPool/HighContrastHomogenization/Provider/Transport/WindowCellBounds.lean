/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.CellDomination
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationSize

/-!
# High-contrast homogenization: Provider.Transport.WindowCellBounds

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The window multiplier on one cell, in both orientations

`e.source.adapted.bound` opens with a pathwise bound that every later
estimate of the source-control subsection reads: on an arbitrary translate
`V = y + ⋄_a^{\mathbf s}` of an adapted cell of a deterministic rounded grid
inside the window, the coarse response is below `B_{\mathbf s}Y_P3^{g(j_*-a)_+}`
times the reference block, and the sharp adjoint response is below the same
multiple of the dual reference block.  Both halves are fields of the window
multiplier, and this file puts them in the form the estimates consume.

The two orientations are one statement.  The sharp adjoint response
`𝐀_*^{-1}(V)`, the dual of the coarse block, is the block reflection of the
response, the dual reference block `𝐄_*^{-1}` is the block reflection of the
reference block,
and the reflection is a congruence by an involution, so it preserves the Loewner
order in both directions and commutes with scalar dilation.  The adjoint bound
is therefore the reflection of the primal bound, and the scalar normalizations
attached to the two are the same number.

Two arithmetic facts are recorded because the shape of the printed constants
needs them.  The boundary constant `B_{\mathbf q} = C_d𝔢_{\mathbf q}ζ_g` is
nonnegative whenever the dimensional constant is, the geometric series `ζ_g`
being positive for `g < 1`; and the burn discount `3^{g(j_*-a)_+}` is positive
always and equal to one at or above the alignment scale.  Without the first, the
`ℝ≥0∞` coefficients of the moment clauses would collapse to zero and the printed
estimates would be false as written.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The reflection dictionary -/

/-- The sharp adjoint response, the dual of the coarse block, is the block
reflection of the coarse response. -/
theorem coarseStarInv_eq_blockReflect (U : Set (Vec d)) (a : CoeffSpace d) :
    coarseStarInv U a = blockReflect (coarseBlock U a) :=
  rfl

/-- The block reflection commutes with scalar dilation. -/
theorem blockScale_blockReflect (c : ℝ) (A : BlockMat d) :
    blockScale c (blockReflect A) = blockReflect (blockScale c A) :=
  rfl

/-- **The block reflection preserves the Loewner order.**  It is a congruence by
an involution, so the quadratic form of the reflection at a doubled vector is the
quadratic form of the block at the swapped vector. -/
theorem blockMatLoewnerLE_blockReflect {A B : BlockMat d} (h : BlockMatLoewnerLE A B) :
    BlockMatLoewnerLE (blockReflect A) (blockReflect B) := by
  intro X
  rw [blockVecDot_blockMatVecMul_blockReflect, blockVecDot_blockMatVecMul_blockReflect]
  exact h _

/-- **The block reflection is an order isomorphism.**  It is its own inverse, so
the order it preserves it also reflects. -/
theorem blockMatLoewnerLE_blockReflect_iff {A B : BlockMat d} :
    BlockMatLoewnerLE (blockReflect A) (blockReflect B) ↔ BlockMatLoewnerLE A B := by
  refine ⟨fun h => ?_, blockMatLoewnerLE_blockReflect⟩
  have h2 := blockMatLoewnerLE_blockReflect h
  rwa [blockReflect_blockReflect, blockReflect_blockReflect] at h2

/-- The block reflection preserves positive definiteness: swapping the halves of
a doubled vector detects vanishing. -/
theorem blockPosDef_blockReflect {A : BlockMat d} (h : Book.Ch02.BlockPosDef A) :
    Book.Ch02.BlockPosDef (blockReflect A) := by
  intro X hX
  rw [blockVecDot_blockMatVecMul_blockReflect]
  exact h _ fun hc => hX (Prod.ext (congrArg Prod.snd hc) (congrArg Prod.fst hc))

/-- The sharp adjoint response is symmetric at every sample. -/
theorem isSymmetricBlockMat_coarseStarInv (U : Set (Vec d)) (a : CoeffSpace d) :
    IsSymmetricBlockMat (coarseStarInv U a) :=
  isSymmetricBlockMat_blockReflect (isSymmetricBlockMat_coarseBlock U a)

/-! ## An arbitrary translate of an adapted cell is a domain -/

/-- **A translate of an adapted cell is a bounded open convex domain.**  The
translation is a homeomorphism, an affine map and a bounded displacement. -/
theorem isOpenBoundedConvexDomain_adaptedCellTranslate {q : Mat d} (hq : q.PosDef)
    (j : ℤ) (y : Vec d) : IsOpenBoundedConvexDomain (adaptedCellTranslate q j y) := by
  have hU := Recurrence.isOpenBoundedConvexDomain_adaptedCell hq j
  refine ⟨?_, ?_, hU.convex.translate y⟩
  · show IsOpen ((fun x => y + x) '' adaptedCell q j)
    rw [Set.image_add_left]
    exact hU.isOpen.preimage (continuous_const.add continuous_id)
  · obtain ⟨R, hR, hRU⟩ := hU.isBoundedDomain
    have hy : (0 : ℝ) ≤ ∑ i : Fin d, |y i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨R + ∑ i : Fin d, |y i|, by linarith only [hR, hy], ?_⟩
    rintro x ⟨z, hz, rfl⟩ i
    have hzi : |z i| ≤ R := hRU z hz i
    have hyi : |y i| ≤ ∑ i : Fin d, |y i| :=
      Finset.single_le_sum (f := fun i : Fin d => |y i|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have hsum : |y i + z i| ≤ |y i| + |z i| := abs_add_le _ _
    show |y i + z i| ≤ R + ∑ i : Fin d, |y i|
    linarith only [hsum, hzi, hyi]

/-- A translate of an adapted cell is nonempty. -/
theorem adaptedCellTranslate_nonempty (q : Mat d) (j : ℤ) (y : Vec d) :
    (adaptedCellTranslate q j y).Nonempty :=
  (Recurrence.adaptedCell_nonempty q j).image _

/-- **The coarse response on a translate of an adapted cell is positive
definite**, pathwise in the coefficient field. -/
theorem blockPosDef_coarseBlock_adaptedCellTranslate {q : Mat d} (hq : q.PosDef)
    (j : ℤ) (y : Vec d) (a : CoeffSpace d) :
    Book.Ch02.BlockPosDef (coarseBlock (adaptedCellTranslate q j y) a) :=
  Recurrence.blockPosDef_coarseBlock_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_adaptedCellTranslate hq j y)
    (adaptedCellTranslate_nonempty q j y) a

/-- A translate of an adapted cell has the volume of the cell it translates. -/
theorem volume_adaptedCellTranslate_eq_volume_adaptedCell (q : Mat d) (j : ℤ) (y : Vec d) :
    MeasureTheory.volume (adaptedCellTranslate q j y) =
      MeasureTheory.volume (adaptedCell q j) := by
  show MeasureTheory.volume ((fun x => y + x) '' adaptedCell q j) = _
  rw [Set.image_add_left]
  exact measure_preimage_add MeasureTheory.volume _ _

/-- **The coarse response on a translate of an adapted cell is measurable in the
coefficient field**, for every law at once. -/
theorem hasMeasurableCoarseBlock_adaptedCellTranslate (P : Measure (CoeffSpace d))
    {q : Mat d} (hq : q.PosDef) (j : ℤ) (y : Vec d) :
    HasMeasurableCoarseBlock P (adaptedCellTranslate q j y) := by
  refine Recurrence.hasMeasurableCoarseBlock_of_isBoundedDomain P
    (isOpenBoundedConvexDomain_adaptedCellTranslate hq j y).isOpen
    (isOpenBoundedConvexDomain_adaptedCellTranslate hq j y).isBoundedDomain ?_
  rw [volume_adaptedCellTranslate_eq_volume_adaptedCell]
  exact Recurrence.toReal_volume_adaptedCell_pos hq j

/-! ## The two printed scalar factors -/

/-- The geometric series `ζ_g = (1 - 3^{-(1-g)})^{-1}` is positive below the
critical exponent. -/
theorem zero_lt_zetaG {g : ℝ} (hg : g < 1) : 0 < zetaG g := by
  have hlt : (3 : ℝ) ^ (-(1 - g)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hg])
  exact inv_pos.mpr (by linarith only [hlt])

/-- The boundary constant `B_{\mathbf q} = C_d𝔢_{\mathbf q}ζ_g` of the moment
bound for the coarse block on an adapted cell is nonnegative: the witness
eccentricity is a square root and the geometric series is positive. -/
theorem zero_le_boundaryConst {Cd g : ℝ} (hCd : 0 ≤ Cd) (hg : g < 1) (m : Mat d) :
    0 ≤ boundaryConst Cd g m :=
  mul_nonneg (mul_nonneg hCd (Real.sqrt_nonneg _)) (zero_lt_zetaG hg).le

/-- The burn discount `3^{g(j_*-a)_+}` of `e.source.adapted.bound` is
positive. -/
theorem zero_lt_burnDiscount (g : ℝ) (jStar r : ℤ) : 0 < burnDiscount g jStar r :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- The burn discount is one at or above the alignment scale. -/
theorem burnDiscount_eq_one (g : ℝ) {jStar r : ℤ} (hr : jStar ≤ r) :
    burnDiscount g jStar r = 1 := by
  have hle : ((jStar : ℝ) - (r : ℝ)) ≤ 0 := by
    have hc : (jStar : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith only [hc]
  rw [burnDiscount, max_eq_right hle, mul_zero, Real.rpow_zero]

/-- The product of the two printed factors is nonnegative. -/
theorem zero_le_boundaryConst_mul_burnDiscount {Cd g : ℝ} (hCd : 0 ≤ Cd) (hg : g < 1)
    (m : Mat d) (jStar r : ℤ) :
    0 ≤ boundaryConst Cd g m * burnDiscount g jStar r :=
  mul_nonneg (zero_le_boundaryConst hCd hg m) (zero_lt_burnDiscount g jStar r).le

/-! ## The pathwise cell bounds -/

variable {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
  {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-- **The primal cell bound**, `e.source.adapted.bound` on an arbitrary
translate of an adapted cell inside the window, with the two printed factors
collected in front of the multiplier. -/
theorem ae_blockMatLoewnerLE_coarseBlock_adaptedCellTranslate
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (r : ℤ) (y : Vec d)
    (hcont : adaptedCellTranslate (roundedGrid jStar nu) r y ⊆ centeredCube d M) :
    ∀ᵐ a ∂P, BlockMatLoewnerLE
      (coarseBlock (adaptedCellTranslate (roundedGrid jStar nu) r y) a)
      (blockScale (boundaryConst Cd g nu * burnDiscount g jStar r * Y a) E) := by
  filter_upwards [hY.adapted_primal] with a ha
  have h := ha nu hnu r y hcont
  rwa [show boundaryConst Cd g nu * Y a * burnDiscount g jStar r =
    boundaryConst Cd g nu * burnDiscount g jStar r * Y a from mul_right_comm _ _ _] at h

/-- **The adjoint cell bound**, the same display for the sharp adjoint response
against the dual reference block `𝐄_*^{-1}`. -/
theorem ae_blockMatLoewnerLE_coarseStarInv_adaptedCellTranslate
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (r : ℤ) (y : Vec d)
    (hcont : adaptedCellTranslate (roundedGrid jStar nu) r y ⊆ centeredCube d M) :
    ∀ᵐ a ∂P, BlockMatLoewnerLE
      (coarseStarInv (adaptedCellTranslate (roundedGrid jStar nu) r y) a)
      (blockScale (boundaryConst Cd g nu * burnDiscount g jStar r * Y a)
        (blockReflect E)) := by
  filter_upwards [hY.adapted_adjoint] with a ha
  have h := ha nu hnu r y hcont
  rwa [show boundaryConst Cd g nu * Y a * burnDiscount g jStar r =
    boundaryConst Cd g nu * burnDiscount g jStar r * Y a from mul_right_comm _ _ _] at h

/-! ## The pathwise scalar bounds -/

/-- A nonnegative Loewner bound against a positive reference block is a bound on
the scalar size, the lower Loewner constraint being vacuous on a positive
semidefinite numerator. -/
theorem blockSize_le_of_blockMatLoewnerLE_blockScale {H F : BlockMat d}
    (hH : IsSymmetricBlockMat H) (hHps : (toFullBlockMat H).PosSemidef)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) {c : ℝ} (hc : 0 ≤ c)
    (hle : BlockMatLoewnerLE H (blockScale c F)) : blockSize H F ≤ c := by
  have hFfull : (toFullBlockMat F).PosDef := posDef_toFullBlockMat hF hFpd
  refine PortableHistory.blockSize_le_of_sandwich hH hF hFpd hc ?_ (Matrix.le_iff.mpr ?_)
  · have h := le_of_blockMatLoewnerLE hH (isSymmetricBlockMat_blockScale c hF) hle
    rwa [toFullBlockMat_blockScale] at h
  · have hrw : toFullBlockMat H - (-c) • toFullBlockMat F =
        toFullBlockMat H + c • toFullBlockMat F := by
      rw [neg_smul, sub_neg_eq_add]
    rw [hrw]
    exact hHps.add (hFfull.posSemidef.smul hc)

/-- **The primal cell moment, pathwise**: the scalar normalization
`|𝐄^{-1/2}𝐀(V)𝐄^{-1/2}|` of a cell of the window is below
`B_{\mathbf s}Y_P3^{g(j_*-a)_+}`. -/
theorem ae_blockSize_coarseBlock_adaptedCellTranslate_le (hCd : 0 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) (r : ℤ) (y : Vec d)
    (hcont : adaptedCellTranslate (roundedGrid jStar nu) r y ⊆ centeredCube d M) :
    ∀ᵐ a ∂P, blockSize
        (coarseBlock (adaptedCellTranslate (roundedGrid jStar nu) r y) a) E ≤
      boundaryConst Cd g nu * burnDiscount g jStar r * Y a := by
  filter_upwards [ae_blockMatLoewnerLE_coarseBlock_adaptedCellTranslate hY hnu r y hcont]
    with a ha
  refine blockSize_le_of_blockMatLoewnerLE_blockScale
    (isSymmetricBlockMat_coarseBlock _ a) ?_ hE hEpd ?_ ha
  · exact (posDef_toFullBlockMat (isSymmetricBlockMat_coarseBlock _ a)
      (blockPosDef_coarseBlock_adaptedCellTranslate
        (Recurrence.posDef_of_isRoundedGrid hq) r y a)).posSemidef
  · exact mul_nonneg (zero_le_boundaryConst_mul_burnDiscount hCd hg nu jStar r)
      (le_trans zero_le_one (hY.one_le a))

/-- **The adjoint cell moment, pathwise**: the same bound for
`|𝐄_*^{1/2}𝐀_*^{-1}(V)𝐄_*^{1/2}|`, the sharp adjoint normalization in the
moment bound for the dual block on an adapted cell. -/
theorem ae_blockSize_coarseStarInv_adaptedCellTranslate_le (hCd : 0 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) (r : ℤ) (y : Vec d)
    (hcont : adaptedCellTranslate (roundedGrid jStar nu) r y ⊆ centeredCube d M) :
    ∀ᵐ a ∂P, blockSize
        (coarseStarInv (adaptedCellTranslate (roundedGrid jStar nu) r y) a)
        (blockReflect E) ≤
      boundaryConst Cd g nu * burnDiscount g jStar r * Y a := by
  filter_upwards
    [ae_blockMatLoewnerLE_coarseStarInv_adaptedCellTranslate hY hnu r y hcont] with a ha
  refine blockSize_le_of_blockMatLoewnerLE_blockScale
    (isSymmetricBlockMat_coarseStarInv _ a) ?_ (isSymmetricBlockMat_blockReflect hE)
    (blockPosDef_blockReflect hEpd) ?_ ha
  · exact (posDef_toFullBlockMat (isSymmetricBlockMat_coarseStarInv _ a)
      (blockPosDef_blockReflect (blockPosDef_coarseBlock_adaptedCellTranslate
        (Recurrence.posDef_of_isRoundedGrid hq) r y a))).posSemidef
  · exact mul_nonneg (zero_le_boundaryConst_mul_burnDiscount hCd hg nu jStar r)
      (le_trans zero_le_one (hY.one_le a))

end

end Transport
end HighContrast
end HCPolySupport
