/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AveragedEntries

/-!
# High-contrast homogenization: Provider.Recurrence.FiniteRangeAveraging

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# `l.fixed.geometry.matrix.averaging`

The finite-range matrix averaging estimate: the mixed norm of the centred average
of the responses of a family of distinct aligned adapted cells is smaller than
the mixed norm of a single response by the square root of the number of cells.

The proof is the printed one.  The scalarization display of
`l.fixed.geometry.matrix.averaging` reduces the matrix estimate to the `4d²`
scalar estimates carried by the colour split and the independent-sum inequality,
and reassembling them costs the factor `2d` the printed proof records.  The
average contributes the weight `M^{-1}`, which together with the square root
`M^{1/2}` produced by the independent sums is the gain `M^{-1/2}`.

The estimate is stated in the `ℝ≥0∞` carrier the fixed-grid moments are written
in, so an infinite single-cell moment makes the bound vacuous rather than false.
The equal-weight form recorded here is the one the averaging step of
`p.fixed.geometry.parent.child.recurrence` consumes; its last form replaces the single-cell
moment by the centred moment `v_j^q` at the origin, the two being equal because
each aligned cell is an integer translate of the cell at the origin.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Reassembling the `4d²` entries -/

/-- The `ℓ²` combination of the `4d²` entrywise bounds costs the factor `2d` of
the printed proof. -/
private theorem rpow_sum_sq_le {x : ℝ≥0∞} {y : BlockCoord d → BlockCoord d → ℝ≥0∞}
    (h : ∀ α β, y α β ≤ x) :
    (∑ α : BlockCoord d, ∑ β : BlockCoord d, y α β ^ (2 : ℝ)) ^ (2⁻¹ : ℝ)
      ≤ ENNReal.ofReal (2 * (d : ℝ)) * x := by
  have hsq : ∀ z : ℝ≥0∞, z ^ (2 : ℝ) = z * z := fun z => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, pow_two]
  have hcard : (Finset.univ : Finset (BlockCoord d)).card = 2 * d := by
    simp [Finset.card_univ, Fintype.card_sum, two_mul]
  have hc : ENNReal.ofReal (2 * (d : ℝ)) = ((2 * d : ℕ) : ℝ≥0∞) := by
    rw [show (2 * (d : ℝ)) = ((2 * d : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  have heq : (∑ _α : BlockCoord d, ∑ _β : BlockCoord d, x ^ (2 : ℝ))
      = (((2 * d : ℕ) : ℝ≥0∞) * x) ^ (2 : ℝ) := by
    rw [Finset.sum_const, Finset.sum_const, hcard, nsmul_eq_mul, nsmul_eq_mul, hsq, hsq]
    ring
  have hle : (∑ α : BlockCoord d, ∑ β : BlockCoord d, y α β ^ (2 : ℝ))
      ≤ (((2 * d : ℕ) : ℝ≥0∞) * x) ^ (2 : ℝ) :=
    le_trans (Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ =>
      ENNReal.rpow_le_rpow (h α β) (by norm_num)) (le_of_eq heq)
  calc (∑ α : BlockCoord d, ∑ β : BlockCoord d, y α β ^ (2 : ℝ)) ^ (2⁻¹ : ℝ)
      ≤ ((((2 * d : ℕ) : ℝ≥0∞) * x) ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) :=
        ENNReal.rpow_le_rpow hle (by norm_num)
    _ = ENNReal.ofReal (2 * (d : ℝ)) * x := by
        rw [← ENNReal.rpow_mul, hc]
        norm_num

/-- The `ℝ≥0∞` bookkeeping that collects the reassembly factor, the constant of
the independent-sum estimate and the gain into a single coefficient. -/
private theorem ofReal_two_mul_natCast_mul {B S G : ℝ} (hB : 0 ≤ B) (hS : 0 ≤ S) (hG : 0 ≤ G)
    {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    ENNReal.ofReal (2 * (d : ℝ)) * ENNReal.ofReal (B * (S * G * x.toReal))
      = ENNReal.ofReal (2 * (d : ℝ) * (B * S) * G) * x := by
  have h1 : ENNReal.ofReal (2 * (d : ℝ)) * ENNReal.ofReal (B * (S * G * x.toReal))
      = ENNReal.ofReal (2 * (d : ℝ) * (B * S) * G) * ENNReal.ofReal x.toReal := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [h1, ENNReal.ofReal_toReal hx]

/-! ## Symmetry and measurability of the centred aligned average -/

/-- The aligned average of the coarse responses is symmetric. -/
theorem isSymmetricBlockMat_alignedAverage {q : Mat d} {j : ℤ} (Z : Finset (Fin d → ℤ))
    (a : CoeffSpace d) :
    IsSymmetricBlockMat (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
      ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a))) := by
  have hterm : ∀ w : Fin d → ℤ, (toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)).IsSymm :=
    fun w => isSymm_toFullBlockMat
      (isSymmetricBlockMat_coarseBlockMatrix (adaptedCellAt q j w) (⇑a.1))
  refine isSymmetricBlockMat_of_isSymm ?_
  ext γ δ
  simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  exact congrArg _ (Finset.sum_congr rfl fun w _ => (hterm w).apply γ δ)

/-! ## The estimate at an explicit constant -/

/-- **`l.fixed.geometry.matrix.averaging`, equal weights, entrywise binder.**
The mixed norm of the centred aligned average is at most an explicit constant
times `M^{-1/2}` times the uniform bound on the `L^Q` norms of the entries of the
normalized centred responses. -/
theorem lqSchattenSize_alignedAverage_le_of_lqNorm_le {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hPs : HCPoly.Frozen.IsStationaryLaw P)
    (hP : HCPoly.Frozen.IsUnitRangeLaw P) {Q : ℝ} (hQ : 2 ≤ Q) {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {j : ℤ} (hj : l ≤ j) (hint : HasFiniteAdaptedMean P q j)
    (F : BlockMat d) {v : ℝ≥0∞} (hv : v ≠ ⊤) {Z : Finset (Fin d → ℤ)} (hZ : Z.Nonempty)
    (hbd : ∀ w ∈ Z, ∀ α β : BlockCoord d, lqNorm P Q (fun a => toFullBlockMat (normalizedBlock
      (blockSub (coarseBlock (adaptedCellAt q j w) a) (adaptedMean P q j)) F) α β) ≤ v) :
    lqSchattenSize P Q (fun a => blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
        ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a))) (adaptedMean P q j)) F
      ≤ ENNReal.ofReal (2 * (d : ℝ)) *
          ENNReal.ofReal
            ((2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q) *
              (Real.sqrt ((3 : ℝ) ^ d) * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹) * v.toReal)) := by
  have hMpos : (0 : ℝ) < (Z.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hZ
  have hsym : ∀ a : CoeffSpace d, IsSymmetricBlockMat (blockSub (ofFullBlockMat
      ((Z.card : ℝ)⁻¹ • ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
      (adaptedMean P q j)) := fun a =>
    isSymmetricBlockMat_blockSub (isSymmetricBlockMat_alignedAverage Z a)
      (isSymmetricBlockMat_adaptedMean P q j)
  have hentry : ∀ α β : BlockCoord d,
      (fun a : CoeffSpace d => toFullBlockMat (normalizedBlock (blockSub (ofFullBlockMat
          ((Z.card : ℝ)⁻¹ • ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
          (adaptedMean P q j)) F) α β)
        = (Z.card : ℝ)⁻¹ • fun a : CoeffSpace d => ∑ w ∈ Z, toFullBlockMat (normalizedBlock
            (blockSub (coarseBlock (adaptedCellAt q j w) a) (adaptedMean P q j)) F) α β := by
    intro α β
    funext a
    exact toFullBlockMat_normalizedBlock_blockSub_average_apply hZ
      (fun w => coarseBlock (adaptedCellAt q j w) a) (adaptedMean P q j) F α β
  have hmeasw : ∀ (w : Fin d → ℤ) (α β : BlockCoord d),
      AEStronglyMeasurable (fun a : CoeffSpace d => toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (adaptedCellAt q j w) a) (adaptedMean P q j)) F) α β) P :=
    fun w α β => aestronglyMeasurable_toFullBlockMat_normalizedBlock_blockSub
      (hasMeasurableCoarseBlock_adaptedCellAt P (posDef_of_isRoundedGrid hq) j w) _ F α β
  have hmeas : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun a : CoeffSpace d => toFullBlockMat (normalizedBlock
        (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
          ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
          (adaptedMean P q j)) F) α β) P := by
    intro α β
    rw [hentry α β]
    have hsum := Finset.aestronglyMeasurable_sum Z fun w (_ : w ∈ Z) => hmeasw w α β
    exact ((hsum.congr (_root_.Filter.Eventually.of_forall fun a => by
      simp only [Finset.sum_apply])).const_smul _)
  have harith : (Z.card : ℝ)⁻¹ *
      ((2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q) *
        (Real.sqrt ((3 : ℝ) ^ d) * Real.sqrt (Z.card : ℝ) * v.toReal))
      = (2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q) *
        (Real.sqrt ((3 : ℝ) ^ d) * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹) * v.toReal) := by
    have hM : (Z.card : ℝ)⁻¹ * Real.sqrt (Z.card : ℝ) = (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one (Z.card : ℝ), ← Real.rpow_add hMpos]
      norm_num
    rw [← hM]
    ring
  have hbound : ∀ α β : BlockCoord d,
      lqNorm P Q (fun a : CoeffSpace d => toFullBlockMat (normalizedBlock
        (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
          ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
          (adaptedMean P q j)) F) α β)
        ≤ ENNReal.ofReal
            ((2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q) *
              (Real.sqrt ((3 : ℝ) ^ d) * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹) * v.toReal)) := by
    intro α β
    have hscale : lqNorm P Q (fun a : CoeffSpace d => toFullBlockMat (normalizedBlock
        (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
          ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
          (adaptedMean P q j)) F) α β)
        = ENNReal.ofReal ((Z.card : ℝ)⁻¹) *
          lqNorm P Q (fun a : CoeffSpace d => ∑ w ∈ Z, toFullBlockMat (normalizedBlock
            (blockSub (coarseBlock (adaptedCellAt q j w) a) (adaptedMean P q j)) F) α β) := by
      rw [lqNorm, lqNorm, hentry α β, eLpNorm_const_smul]
      congr 1
      rw [← ofReal_norm, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hMpos))]
    rw [hscale, ← harith, ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hMpos))]
    exact mul_le_mul' le_rfl (lqNorm_sum_aligned_le hPs hP hQ hq hj hint F hv Z α β
      fun w hw => hbd w hw α β)
  exact le_trans (lqSchattenSize_le P hQ F hsym hmeas) (rpow_sum_sq_le hbound)

/-! ## The printed display -/

/-- **`l.fixed.geometry.matrix.averaging`**, equal weights: there is a constant
`C(d, Q)` such that the mixed norm of the centred average of the responses over
`M` distinct aligned adapted cells is at most `C(d, Q) M^{-1/2}` times a uniform
bound on the mixed norms of the centred single-cell responses. -/
theorem finite_range_matrix_averaging (d : ℕ) (hd : 0 < d) {Q : ℝ} (hQ : 2 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)), IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P → HCPoly.Frozen.IsUnitRangeLaw P →
        ∀ (l : ℤ) (q : Mat d), IsRoundedGrid l q → ∀ j : ℤ, l ≤ j →
          HasFiniteAdaptedMean P q j → ∀ (F : BlockMat d) (v : ℝ≥0∞)
            (Z : Finset (Fin d → ℤ)), Z.Nonempty →
            (∀ w ∈ Z, lqSchattenSize P Q
              (fun a => blockSub (coarseBlock (adaptedCellAt q j w) a) (adaptedMean P q j))
              F ≤ v) →
            lqSchattenSize P Q (fun a => blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
                ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
                (adaptedMean P q j)) F
              ≤ ENNReal.ofReal (C * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹)) * v := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_two hQ
  have hconst : (0 : ℝ) ≤ IndependentSums.rosenthalBennettIntegralConst := by
    simp only [IndependentSums.rosenthalBennettIntegralConst]
    positivity
  have hB : (0 : ℝ) ≤
      2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q := by
    positivity
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  refine ⟨2 * (d : ℝ) *
    ((2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q) *
      Real.sqrt ((3 : ℝ) ^ d)), by positivity, ?_⟩
  intro P hPprob hPs hP l q hq j hj hint F v Z hZ hbd
  have := hPprob
  have hMpos : (0 : ℝ) < (Z.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hZ
  have hgain : (0 : ℝ) < (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹) := Real.rpow_pos_of_pos hMpos _
  rcases eq_or_ne v ⊤ with rfl | hv
  · rw [ENNReal.mul_top (by
      simpa using (ENNReal.ofReal_pos.mpr (by positivity)).ne')]
    exact le_top
  have hentrybd : ∀ w ∈ Z, ∀ α β : BlockCoord d,
      lqNorm P Q (fun a => toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (adaptedCellAt q j w) a) (adaptedMean P q j)) F) α β) ≤ v :=
    fun w hw α β => le_trans
      (lqNorm_normalizedBlock_le_lqSchattenSize P hQ0
        (fun a => isSymmetricBlockMat_coarseBlock_sub a (isSymmetricBlockMat_adaptedMean P q j))
        F α β (aestronglyMeasurable_toFullBlockMat_normalizedBlock_blockSub
          (hasMeasurableCoarseBlock_adaptedCellAt P (posDef_of_isRoundedGrid hq) j w) _ F α β))
      (hbd w hw)
  exact le_trans (lqSchattenSize_alignedAverage_le_of_lqNorm_le hPs hP hQ hq hj hint F hv hZ
      hentrybd)
    (le_of_eq (ofReal_two_mul_natCast_mul hB (Real.sqrt_nonneg _) hgain.le hv))

/-! ## The form the fixed-grid recurrence consumes -/

/-- **The entries of the normalized centred response have the same `L^Q` norm at
every aligned adapted cell.**  Each aligned cell is an integer translate of the
cell at the origin, and under stationarity of the coefficient law the
translation preserves the law. -/
theorem lqNorm_normalizedBlock_adaptedCellAt_eq {P : Measure (CoeffSpace d)}
    (hPs : HCPoly.Frozen.IsStationaryLaw P) {Q : ℝ} {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {j : ℤ} (hj : l ≤ j) (E F : BlockMat d) (w : Fin d → ℤ)
    (α β : BlockCoord d) :
    lqNorm P Q (fun a => toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (adaptedCellAt q j w) a) E) F) α β)
      = lqNorm P Q (fun a => toFullBlockMat (normalizedBlock
          (blockSub (coarseBlock (adaptedCell q j) a) E) F) α β) := by
  obtain ⟨z, hz⟩ := exists_intVec_adaptedCellCenter hq hj w
  have hcell : ∀ a : CoeffSpace d, coarseBlock (adaptedCellAt q j w) a
      = coarseBlock (adaptedCell q j) (translateCoeff z a) :=
    fun a => adaptedResponse_eq_coarseBlock_translateCoeff hz a
  have hfun : (fun a : CoeffSpace d => toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (adaptedCellAt q j w) a) E) F) α β)
      = (fun a : CoeffSpace d => toFullBlockMat (normalizedBlock
          (blockSub (coarseBlock (adaptedCell q j) a) E) F) α β) ∘ translateCoeff z := by
    funext a
    rw [Function.comp_apply, hcell a]
  rw [lqNorm, lqNorm, hfun]
  exact eLpNorm_comp_measurePreserving
    (aestronglyMeasurable_toFullBlockMat_normalizedBlock_blockSub
      (hasMeasurableCoarseBlock_adaptedCell P (posDef_of_isRoundedGrid hq) j) E F α β)
    (measurePreserving_translateCoeff hPs z)

/-- The entries of the normalized centred response of an aligned adapted cell are
bounded in `L^Q` by the centred moment `v_j^q` at the origin. -/
theorem lqNorm_normalizedBlock_adaptedCellAt_le_centeredMoment {P : Measure (CoeffSpace d)}
    (hPs : HCPoly.Frozen.IsStationaryLaw P) {Q : ℝ} (hQ : 0 < Q) {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {j : ℤ} (hj : l ≤ j) (w : Fin d → ℤ) (α β : BlockCoord d) :
    lqNorm P Q (fun a => toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (adaptedCellAt q j w) a) (adaptedMean P q j))
        (adaptedMean P q j)) α β)
      ≤ centeredMoment P Q q j := by
  rw [lqNorm_normalizedBlock_adaptedCellAt_eq hPs hq hj (adaptedMean P q j)
    (adaptedMean P q j) w α β]
  exact lqNorm_normalizedBlock_le_lqSchattenSize P hQ
    (fun a => isSymmetricBlockMat_coarseBlock_sub a (isSymmetricBlockMat_adaptedMean P q j))
    (adaptedMean P q j) α β (aestronglyMeasurable_toFullBlockMat_normalizedBlock_blockSub
      (hasMeasurableCoarseBlock_adaptedCell P (posDef_of_isRoundedGrid hq) j) _ _ α β)

/-- **The averaging step of `p.fixed.geometry.parent.child.recurrence`.**  The mixed norm of
the centred average of the responses over the `M` aligned scale-`j` cells is at
most `C(d, Q) M^{-1/2}` times the centred moment `v_j^q`. -/
theorem lqSchattenSize_alignedAverage_le_centeredMoment {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hPs : HCPoly.Frozen.IsStationaryLaw P)
    (hP : HCPoly.Frozen.IsUnitRangeLaw P) {Q : ℝ} (hQ : 2 ≤ Q) {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {j : ℤ} (hj : l ≤ j) (hint : HasFiniteAdaptedMean P q j)
    (hfin : centeredMoment P Q q j ≠ ⊤) {Z : Finset (Fin d → ℤ)} (hZ : Z.Nonempty) :
    lqSchattenSize P Q (fun a => blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
        ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a))) (adaptedMean P q j))
        (adaptedMean P q j)
      ≤ ENNReal.ofReal (2 * (d : ℝ) *
          ((2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q) *
            Real.sqrt ((3 : ℝ) ^ d)) * (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹)) *
        centeredMoment P Q q j := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_two hQ
  have hconst : (0 : ℝ) ≤ IndependentSums.rosenthalBennettIntegralConst := by
    simp only [IndependentSums.rosenthalBennettIntegralConst]
    positivity
  have hB : (0 : ℝ) ≤
      2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q := by
    positivity
  have hMpos : (0 : ℝ) < (Z.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hZ
  have hgain : (0 : ℝ) < (Z.card : ℝ) ^ (-(2 : ℝ)⁻¹) := Real.rpow_pos_of_pos hMpos _
  exact le_trans (lqSchattenSize_alignedAverage_le_of_lqNorm_le hPs hP hQ hq hj hint
      (adaptedMean P q j) hfin hZ fun w _ α β =>
      lqNorm_normalizedBlock_adaptedCellAt_le_centeredMoment hPs hQ0 hq hj w α β)
    (le_of_eq (ofReal_two_mul_natCast_mul hB (Real.sqrt_nonneg _) hgain.le hfin))

end

end Recurrence
end HighContrast
end HCPolySupport
