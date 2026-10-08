/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.TransportMeanDomination
public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowTerminalNormalization
public import LeanPool.HighContrastHomogenization.Provider.Transport.DiscreteConvolution
public import LeanPool.HighContrastHomogenization.Provider.Transport.TransportCoefficients

/-!
# High-contrast homogenization: Provider.Transport.AnnealedRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The pathwise majorant of a target cell

`e.two.grid.whitney.average` is consumed against a majorant, not summed: its
hypothesis is that a block dominates every finite partial double sum of the
filling's rows.  The printed majorant
`Σ_{r=j_*}^{n}Σ_{V∈𝒱_r}(|V|/|W|)𝐀(V) + G_W^{<j_*}` is exhibited here with the
below-start term in closed form, and the hypothesis is discharged.

The rows below the alignment are paid by one geometric series: the cross-grid row
of `e.two.grid.whitney.volumes` weights a scale-`r` row by `3^{r-j}`,
the window multiplier's own cell bound carries the burn discount `3^{g(j_*-r)}`,
and the product is `3^{j_*-j}3^{-(1-g)(j_*-r)}`, whose total over the scales
below the alignment is `3^{j_*-j}ζ_g` -- the same geometric series that the
boundary constant `B_{\mathbf q}` already names.  Nothing of the filling is
discarded: the rows at or above the alignment are kept whole, as the printed
right side keeps them.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Elementary transport of symmetry, positivity and quadratic forms -/

/-- A finite sum of positive semidefinite matrices is positive semidefinite. -/
private theorem posSemidef_finsetSum {ι : Type*} {s : Finset ι} {A : ι → FullBlockMat d}
    (h : ∀ i ∈ s, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- The doubled quadratic form of a nonnegative block is nonnegative. -/
private theorem zero_le_blockQuadratic_of_posSemidef {A : BlockMat d}
    (hA : (toFullBlockMat A).PosSemidef) (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul A X) := by
  have hx := hA.dotProduct_mulVec_nonneg (toFullBlockVec X)
  rw [blockVecDot_blockMatVecMul_eq_dotProduct]
  simpa using hx

/-- The doubled quadratic form of a flattened weighted double sum. -/
private theorem blockQuadratic_ofFullBlockMat_double_sum (X : BlockVec d) (R : Finset ℤ)
    (Zf : ℤ → Finset (Fin d → ℤ)) (c : ℤ → (Fin d → ℤ) → ℝ)
    (A : ℤ → (Fin d → ℤ) → BlockMat d) (G : BlockMat d) :
    blockVecDot X (blockMatVecMul (ofFullBlockMat
      ((∑ r ∈ R, ∑ w ∈ Zf r, c r w • toFullBlockMat (A r w)) + toFullBlockMat G)) X) =
      (∑ r ∈ R, ∑ w ∈ Zf r, c r w * blockVecDot X (blockMatVecMul (A r w) X)) +
        blockVecDot X (blockMatVecMul G X) := by
  rw [blockVecDot_blockMatVecMul_eq_dotProduct, toFullBlockMat_ofFullBlockMat,
    Matrix.add_mulVec, dotProduct_add, Matrix.sum_mulVec, dotProduct_sum,
    blockVecDot_blockMatVecMul_eq_dotProduct]
  refine congrArg (· + _) (Finset.sum_congr rfl fun r _ => ?_)
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    blockVecDot_blockMatVecMul_eq_dotProduct]

/-- **The majorant read through its quadratic form.**  The exhaustion compares
finite partial double sums against the half quadratic form of the majorant; this
is that form, resolved into the rows and the remainder. -/
private theorem half_blockQuadratic_majorant (X : BlockVec d) (R : Finset ℤ)
    (Zf : ℤ → Finset (Fin d → ℤ)) (c : ℤ → (Fin d → ℤ) → ℝ)
    (A : ℤ → (Fin d → ℤ) → BlockMat d) (cb : ℝ) (G : BlockMat d) :
    1 / 2 * blockVecDot X (blockMatVecMul (ofFullBlockMat
        ((∑ r ∈ R, ∑ w ∈ Zf r, c r w • toFullBlockMat (A r w)) +
          cb • toFullBlockMat G)) X) =
      (∑ r ∈ R, ∑ w ∈ Zf r,
          c r w * (1 / 2 * blockVecDot X (blockMatVecMul (A r w) X))) +
        1 / 2 * (cb * blockVecDot X (blockMatVecMul G X)) := by
  rw [show cb • toFullBlockMat G = toFullBlockMat (blockScale cb G) from
      (toFullBlockMat_blockScale cb G).symm,
    blockQuadratic_ofFullBlockMat_double_sum,
    Sharp.blockVecDot_blockMatVecMul_blockScale, mul_add, Finset.mul_sum]
  refine congrArg (· + _) (Finset.sum_congr rfl fun r _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

/-- **The printed split of the exhaustion hypothesis.**  A quantity dominating
every below-start partial sum, added to the finite part from the alignment scale
up, dominates every finite partial sum of the whole family.  This is the shape in
which `e.two.grid.whitney.average` is consumed. -/
private theorem sum_Icc_le_of_belowStart {jStar n : ℤ} (hjn : jStar ≤ n) {row : ℤ → ℝ}
    {G : ℝ} (hrow0 : ∀ r, 0 ≤ row r) (hG0 : 0 ≤ G)
    (hbelow : ∀ J' : ℤ, ∑ r ∈ Finset.Ico J' jStar, row r ≤ G) (J : ℤ) :
    ∑ r ∈ Finset.Icc J n, row r ≤ (∑ r ∈ Finset.Icc jStar n, row r) + G := by
  rcases le_or_gt jStar J with hle | hlt
  · have hmono := Finset.sum_le_sum_of_subset_of_nonneg
      (f := row) (Finset.Icc_subset_Icc hle (le_refl n)) fun i _ _ => hrow0 i
    linarith only [hmono, hG0]
  · have hdisj : Disjoint (Finset.Ico J jStar) (Finset.Icc jStar n) := by
      refine Finset.disjoint_left.mpr fun i hi hi' => ?_
      rw [Finset.mem_Ico] at hi
      rw [Finset.mem_Icc] at hi'
      omega
    have hsplit : Finset.Icc J n = Finset.Ico J jStar ∪ Finset.Icc jStar n := by
      change Finset.Ico J (n + 1) = Finset.Ico J jStar ∪ Finset.Ico jStar (n + 1)
      exact (Finset.Ico_union_Ico_eq_Ico hlt.le (by omega)).symm
    have hbJ := hbelow J
    rw [hsplit, Finset.sum_union hdisj]
    linarith only [hbJ]

/-! ## The two scalar steps of the below-start series -/

/-- **The below-start weight in closed form.**  Below the alignment scale the
cross-grid row weight `3^{r-j}` and the burn discount `3^{g(j_*-r)}` combine into
`3^{j_*-j}3^{-(1-g)(j_*-r)}`: the burn is paid by the part of the row decay that
the exponent `1-g` leaves over. -/
theorem zpow_mul_burnDiscount_eq {g : ℝ} {jStar r j : ℤ} (hr : r ≤ jStar) :
    (3 : ℝ) ^ (r - j) * burnDiscount g jStar r =
      (3 : ℝ) ^ (jStar - j) * (3 : ℝ) ^ (-(1 - g) * ((jStar : ℝ) - (r : ℝ))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hrR : (r : ℝ) ≤ (jStar : ℝ) := by exact_mod_cast hr
  have hmax : max ((jStar : ℝ) - (r : ℝ)) 0 = (jStar : ℝ) - (r : ℝ) :=
    max_eq_left (by linarith only [hrR])
  rw [burnDiscount, hmax, ← Real.rpow_intCast (3 : ℝ) (r - j),
    ← Real.rpow_intCast (3 : ℝ) (jStar - j), ← Real.rpow_add h3, ← Real.rpow_add h3]
  congr 1
  push_cast
  ring

/-- **The total below-start weight.**  The scales strictly below the alignment
carry total weight at most `3^{j_*-j}ζ_g`, the geometric series of ratio
`3^{-(1-g)}`. -/
theorem sum_belowStart_weight_le {g : ℝ} (hg : g < 1) (jStar j J : ℤ) :
    ∑ r ∈ Finset.Ico J jStar, (3 : ℝ) ^ (r - j) * burnDiscount g jStar r ≤
      (3 : ℝ) ^ (jStar - j) * zetaG g := by
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (jStar - j) := by positivity
  have hseries := sum_geom_below_le (show (0 : ℝ) < 1 - g by linarith only [hg]) jStar
    (Finset.Ico J jStar) fun r hr => le_of_lt (Finset.mem_Ico.mp hr).2
  have hrw : ∑ r ∈ Finset.Ico J jStar, (3 : ℝ) ^ (r - j) * burnDiscount g jStar r =
      (3 : ℝ) ^ (jStar - j) *
        ∑ r ∈ Finset.Ico J jStar, (3 : ℝ) ^ (-(1 - g) * ((jStar : ℝ) - (r : ℝ))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r hr =>
      zpow_mul_burnDiscount_eq (le_of_lt (Finset.mem_Ico.mp hr).2)
  rw [hrw, zetaG, ← one_div]
  exact mul_le_mul_of_nonneg_left hseries hpow.le

/-! ## The pathwise majorant -/

section Pathwise

variable {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
  {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-- **The pathwise majorant of `e.two.grid.whitney.average`, exhibited.**
The coarse response of a target cell of the new grid is below the weighted rows
of the old grid's filling from the alignment scale up to the starting scale, plus
the closed-form below-start term `C_dK_{hop}B_{\mathbf q}ζ_g3^{j_*-j}Y_P𝐄`.

Every partial double sum of the filling is split at the alignment: the rows at or
above it form a subsum of the printed finite part, and the rows below it are paid
by the geometric series of the previous display, each cell being controlled by the
window multiplier's own cell bound. -/
theorem coarseBlock_le_filling_rows_add_belowStart [NeZero d] (hd : 1 ≤ d)
    (hCd : 0 ≤ Cd) (hg : g < 1) (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {p : Mat d} (hp : p.PosDef)
    {Khop : ℝ} (hK : gridRatio (roundedGrid jStar nu) p ≤ Khop)
    {n j : ℤ} (hjn : jStar ≤ n) {y : Vec d} {Z : ℤ → Finset (Fin d → ℤ)}
    (hZ : ∀ r, ↑(Z r) =
      fillingIndex (roundedGrid jStar nu) n (adaptedCellTranslate p j y) r)
    (hcont : ∀ r : ℤ, r < jStar → ∀ w ∈ Z r,
      adaptedCellAt (roundedGrid jStar nu) r w ⊆ centeredCube d M) :
    ∀ᵐ a ∂P, toFullBlockMat (coarseBlock (adaptedCellTranslate p j y) a) ≤
      (∑ r ∈ Finset.Icc jStar n, ∑ w ∈ Z r,
        ((volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAt (roundedGrid jStar nu) r w) a)) +
        (6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g nu * zetaG g *
          (3 : ℝ) ^ (jStar - j) * Y a) • toFullBlockMat E := by
  classical
  have hqpd : (roundedGrid jStar nu).PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hEfull : (toFullBlockMat E).PosDef := posDef_toFullBlockMat hE hEpd
  have hB0 : 0 ≤ boundaryConst Cd g nu := zero_le_boundaryConst hCd hg nu
  have hzeta : 0 < zetaG g := zero_lt_zetaG hg
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (jStar - j) := by positivity
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hchop : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d * Khop := by
    have h1 : (1 : ℝ) ≤ gridRatio (roundedGrid jStar nu) p := one_le_gridRatio _ _
    have hKh : (0 : ℝ) ≤ Khop := by linarith only [h1, hK]
    have hs : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
    have h6 : (0 : ℝ) ≤ 6 * (d : ℝ) := by linarith only [hdR]
    exact mul_nonneg (mul_nonneg h6 hs) hKh
  have hcell0 : ∀ (r : ℤ) (w : Fin d → ℤ),
      (0 : ℝ) ≤ (volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
        (volume (adaptedCellTranslate p j y)).toReal := fun _ _ =>
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  filter_upwards [hY.adapted_primal] with a ha
  have hY0 : (0 : ℝ) ≤ Y a := le_trans zero_le_one (hY.one_le a)
  have hcellps : ∀ (r : ℤ) (w : Fin d → ℤ),
      (toFullBlockMat
        (coarseBlock (adaptedCellAt (roundedGrid jStar nu) r w) a)).PosSemidef :=
    fun r w => posSemidef_toFullBlockMat_coarseBlock
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hqpd r w)
      (Recurrence.volume_adaptedCellAt_pos hqpd r w).ne' a
  set cbel : ℝ := 6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g nu * zetaG g *
    (3 : ℝ) ^ (jStar - j) * Y a with hcbel
  have hcbel0 : 0 ≤ cbel := by
    rw [hcbel]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hchop hB0) hzeta.le) hpow.le) hY0
  set Mm : FullBlockMat d :=
    (∑ r ∈ Finset.Icc jStar n, ∑ w ∈ Z r,
      ((volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
          (volume (adaptedCellTranslate p j y)).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellAt (roundedGrid jStar nu) r w) a)) +
      cbel • toFullBlockMat E with hMm
  have hMps : Mm.PosSemidef := by
    rw [hMm]
    refine Matrix.PosSemidef.add (posSemidef_finsetSum fun r _ => ?_)
      (hEfull.posSemidef.smul hcbel0)
    exact posSemidef_finsetSum fun w _ => (hcellps r w).smul (hcell0 r w)
  have hMsym : IsSymmetricBlockMat (ofFullBlockMat Mm) := by
    refine isSymmetricBlockMat_of_posSemidef ?_
    rwa [toFullBlockMat_ofFullBlockMat]
  -- the exhaustion hypothesis, split at the alignment scale
  have hT : ∀ (X : BlockVec d) (J : ℤ), J ≤ n →
      (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
        (volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt (roundedGrid jStar nu) r w) a)
              X))) ≤
        1 / 2 * blockVecDot X (blockMatVecMul (ofFullBlockMat Mm) X) := by
    intro X J _
    have hqE0 : (0 : ℝ) ≤ 1 / 2 * blockVecDot X (blockMatVecMul E X) := by
      have h := zero_le_blockQuadratic_of_posSemidef hEfull.posSemidef X
      linarith only [h]
    have hrow0 : ∀ r : ℤ, (0 : ℝ) ≤ ∑ w ∈ Z r,
        (volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt (roundedGrid jStar nu) r w) a)
              X)) := fun r =>
      Finset.sum_nonneg fun w _ => mul_nonneg (hcell0 r w) (by
        have h := zero_le_blockQuadratic_of_posSemidef (hcellps r w) X
        linarith only [h])
    have hG0 : (0 : ℝ) ≤ 1 / 2 *
        (cbel * blockVecDot X (blockMatVecMul E X)) := by
      have h := zero_le_blockQuadratic_of_posSemidef hEfull.posSemidef X
      have hm : (0 : ℝ) ≤ cbel * blockVecDot X (blockMatVecMul E X) :=
        mul_nonneg hcbel0 h
      linarith only [hm]
    have hbelow : ∀ J' : ℤ, (∑ r ∈ Finset.Ico J' jStar, ∑ w ∈ Z r,
        (volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt (roundedGrid jStar nu) r w) a)
              X))) ≤ 1 / 2 * (cbel * blockVecDot X (blockMatVecMul E X)) := by
      intro J'
      have hstep : ∀ r ∈ Finset.Ico J' jStar, (∑ w ∈ Z r,
          (volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
              (volume (adaptedCellTranslate p j y)).toReal *
            (1 / 2 * blockVecDot X
              (blockMatVecMul (coarseBlock (adaptedCellAt (roundedGrid jStar nu) r w) a)
                X))) ≤
          6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g nu * Y a *
              (1 / 2 * blockVecDot X (blockMatVecMul E X)) *
            ((3 : ℝ) ^ (r - j) * burnDiscount g jStar r) := by
        intro r hr
        have hrlt : r < jStar := (Finset.mem_Ico.mp hr).2
        have hkap : (0 : ℝ) ≤ boundaryConst Cd g nu * Y a * burnDiscount g jStar r :=
          mul_nonneg (mul_nonneg hB0 hY0) (zero_lt_burnDiscount g jStar r).le
        have hcellbd : ∀ w ∈ Z r,
            (volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
                (volume (adaptedCellTranslate p j y)).toReal *
              (1 / 2 * blockVecDot X
                (blockMatVecMul
                  (coarseBlock (adaptedCellAt (roundedGrid jStar nu) r w) a) X)) ≤
              (volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
                  (volume (adaptedCellTranslate p j y)).toReal *
                ((boundaryConst Cd g nu * Y a * burnDiscount g jStar r) *
                  (1 / 2 * blockVecDot X (blockMatVecMul E X))) := by
          intro w hw
          refine mul_le_mul_of_nonneg_left ?_ (hcell0 r w)
          have hlo := ha nu hnu r (adaptedCellCenter (roundedGrid jStar nu) r w)
            (hcont r hrlt w hw) X
          rw [Sharp.blockVecDot_blockMatVecMul_blockScale,
            ← adaptedCellAt_eq_adaptedCellTranslate] at hlo
          linarith only [hlo]
        have hsum := Finset.sum_le_sum hcellbd
        rw [← Finset.sum_mul] at hsum
        have hvol := sum_relative_volume_row_le_hop hd hp hqpd (by omega : r < n) (hZ r) hK
        have hfin := mul_le_mul_of_nonneg_right hvol (mul_nonneg hkap hqE0)
        refine hsum.trans (hfin.trans (le_of_eq ?_))
        ring
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.mul_sum, hcbel]
      have hfac : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d * Khop *
          boundaryConst Cd g nu * Y a *
          (1 / 2 * blockVecDot X (blockMatVecMul E X)) :=
        mul_nonneg (mul_nonneg (mul_nonneg hchop hB0) hY0) hqE0
      refine (mul_le_mul_of_nonneg_left (sum_belowStart_weight_le hg jStar j J') hfac).trans
        (le_of_eq ?_)
      ring
    rw [hMm, half_blockQuadratic_majorant]
    exact sum_Icc_le_of_belowStart hjn hrow0 hG0 hbelow J
  have hfinal := le_of_blockMatLoewnerLE
    (isSymmetricBlockMat_coarseBlock (adaptedCellTranslate p j y) a) hMsym
    fun X => blockQuadratic_coarseBlock_le_of_forall_filling_rows hp hqpd hZ a X (hT X)
  rwa [toFullBlockMat_ofFullBlockMat] at hfinal

end Pathwise

end

end Transport
end HighContrast
end HCPolySupport
