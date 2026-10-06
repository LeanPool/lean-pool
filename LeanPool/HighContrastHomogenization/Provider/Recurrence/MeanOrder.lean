/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.AnnealedBlockBridge
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedSubadditivity
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.DetTransport
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.SchattenIdeal
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.StationarityTransport

/-!
# High-contrast homogenization: Provider.Recurrence.MeanOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed mean order of the fixed-grid recurrence

The averaging step of `p.fixed.geometry.parent.child.recurrence` opens with the aligned
subdivision of the parent cell `⋄_p^q` into its `3^{d(p-j)}` scale-`j` children,
and with the three displays

`0 ≤ A_p(0) ≤ G`, `E[A_p(0)] = E_p`, `E[G] = E_j`,

where `G` is the average of the children's responses.  Averaging the pathwise
order under the law and reading the two expectations gives the mean order
`E_p ≤ E_j`, which is the hypothesis every later step of the recurrence uses.

The pathwise order is the subadditivity among the coarse-block properties taken
from HC over the aligned subdivision, together with the pathwise positivity
clause.  The two expectations are the entrywise Bochner integral of the
response, read through the translation clause: each child is an integer
translate of the cell at the origin, so under stationarity of the coefficient
law its annealed block is `E_j` and the average
of the children's annealed blocks is `E_j` again.  Averaging is monotone for the
Loewner order because the positive semidefinite cone is closed, which is the
content the ambient integral layer supplies.

The consequences the recurrence's later steps read off the mean order are the
determinant identities for the parent-child normalization: the
relative mean `P_{j,p} = E_p^{-1/2}E_jE_p^{-1/2}` lies above the identity, its
determinant is `e^{Δ_{j,p}}`, the increment `Δ_{j,p}` is nonnegative, the
spectral size of `P_{j,p}` is at most `e^{Δ_{j,p}}`, and the trace gap
`b = tr(P_{j,p} - I)` is at most `e^{Δ_{j,p}} - 1`.  All five are the matrix
analysis of a positive definite pair in the Loewner order, applied at the adapted
means.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## The pathwise order `0 ≤ A_p^q(0) ≤ G` -/

/-! ## The two expectations `E[A_p^q(0)] = E_p^q` and `E[G] = E_j^q` -/

/-- **`E[A_r^q(0)] = E_r^q`.**  The adapted mean is the Bochner integral of the
flattened response, which is what makes the mean order an integral inequality. -/
theorem toFullBlockMat_adaptedMean_eq_integral {P : Measure (CoeffSpace d)} {q : Mat d}
    {r : ℤ} (hint : HasFiniteAdaptedMean P q r) :
    toFullBlockMat (adaptedMean P q r) =
      ∫ a, toFullBlockMat (coarseBlock (adaptedCell q r) a) ∂P :=
  toFullBlockMat_annealedBlock hint

/-- The flattened response over an aligned child cell is Bochner integrable: the
finiteness guard at the origin transports along the integer translation. -/
theorem integrable_toFullBlockMat_coarseBlock_adaptedCellAt {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    {j : ℤ} (hlj : l ≤ j) (hint : HasFiniteAdaptedMean P q j) (w : Fin d → ℤ) :
    Integrable (fun a => toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)) P :=
  integrable_toFullBlockMat (hasIntegrableCoarseBlock_adaptedCellAt hP hq hlj hint w)

/-- **`E[G] = E_j^q`.**  The expectation of the average of the responses over a
nonempty family of aligned scale-`j` cells is the adapted mean at scale `j`: each
cell is an integer translate of the cell at the origin, so stationarity of the
coefficient law gives every summand the same expectation. -/
theorem integral_alignedAverage_eq_adaptedMean {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    {j : ℤ} (hlj : l ≤ j) (hint : HasFiniteAdaptedMean P q j)
    {Z : Finset (Fin d → ℤ)} (hZ : Z.Nonempty) :
    ∫ a, (Z.card : ℝ)⁻¹ • ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) ∂P =
      toFullBlockMat (adaptedMean P q j) := by
  have hmeas : HasMeasurableCoarseBlock P (adaptedCell q j) :=
    fun α β => (hint α β).aestronglyMeasurable
  have hterm : ∀ w ∈ Z,
      Integrable (fun a => toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)) P :=
    fun w _ => integrable_toFullBlockMat_coarseBlock_adaptedCellAt hP hq hlj hint w
  have hcell : ∀ w ∈ Z, ∫ a, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) ∂P =
      toFullBlockMat (adaptedMean P q j) := by
    intro w _
    rw [← toFullBlockMat_annealedBlock
      (hasIntegrableCoarseBlock_adaptedCellAt hP hq hlj hint w),
      annealedBlock_adaptedCellAt_eq_adaptedMean hP hq hlj hmeas w]
  have hcard : (0 : ℝ) < (Z.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hZ
  -- The generic finite-sum integral lemma resolves its ambient norm on the
  -- flattened carrier through the operator-norm scope, while the coarse
  -- response's own integrability comes from the entrywise one; the two
  -- interfaces are bridged entry by entry rather than at the matrix level.
  have hentry : ∀ w ∈ Z, ∀ α β : BlockCoord d,
      Integrable (fun a => toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) α β) P :=
    fun w _ α β => (hasIntegrableCoarseBlock_adaptedCellAt hP hq hlj hint w α β).congr
      (_root_.Filter.Eventually.of_forall fun a =>
        (toFullBlockMat_eq_blockMatEntry (coarseBlock (adaptedCellAt q j w) a) α β).symm)
  have hsumint : Integrable
      (fun a => ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)) P :=
    integrable_of_entries fun α β => by
      simpa only [Matrix.sum_apply] using integrable_finsetSum Z fun w hw => hentry w hw α β
  have hsumeq : ∫ a, ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) ∂P =
      ∑ w ∈ Z, ∫ a, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) ∂P := by
    ext α β
    have hL : (∫ a, ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) ∂P) α β =
        ∑ w ∈ Z, ∫ a, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) α β ∂P := by
      rw [entry_integral hsumint α β]
      simp only [Matrix.sum_apply]
      exact integral_finsetSum Z fun w hw => hentry w hw α β
    have hR : (∑ w ∈ Z, ∫ a, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) ∂P) α β =
        ∑ w ∈ Z, ∫ a, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) α β ∂P := by
      simp only [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun w hw => entry_integral (hterm w hw) α β
    rw [hL, hR]
  rw [integral_smul, hsumeq, Finset.sum_congr rfl hcell,
    Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ hcard.ne', one_smul]

/-! ## The mean order `E_p^q ≤ E_j^q` -/

/-- **`E_p^q ≤ E_j^q`.**  The annealed mean order of `p.fixed.geometry.parent.child.recurrence`,
on the flattened carrier: averaging the pathwise subadditivity of the aligned
subdivision under the law and reading both expectations through
stationarity of the coefficient law leaves the adapted mean at the child scale
on the right. -/
theorem toFullBlockMat_adaptedMean_le [NeZero d] {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    {j p : ℤ} (hlj : l ≤ j) (hjp : j ≤ p) (hintj : HasFiniteAdaptedMean P q j)
    (hintp : HasFiniteAdaptedMean P q p) :
    toFullBlockMat (adaptedMean P q p) ≤ toFullBlockMat (adaptedMean P q j) := by
  obtain ⟨Z, hZ, hcard, -, -, -, -⟩ := aligned_subdivision hq hlj hjp
  have hZne : Z.Nonempty := by
    rw [← Finset.card_pos, hcard]
    positivity
  have hle : ∀ a : CoeffSpace d,
      toFullBlockMat (coarseBlock (adaptedCell q p) a) ≤
        (Z.card : ℝ)⁻¹ • ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) :=
    fun a => toFullBlockMat_coarseBlock_adaptedCell_le_average
      (posDef_of_isRoundedGrid hq) hjp hZ a
  -- As in `integral_alignedAverage_eq_adaptedMean`, the sum's integrability is
  -- bridged from the entrywise interface rather than the matrix-level one.
  have hentry : ∀ w ∈ Z, ∀ α β : BlockCoord d,
      Integrable (fun a => toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) α β) P :=
    fun w _ α β => (hasIntegrableCoarseBlock_adaptedCellAt hP hq hlj hintj w α β).congr
      (_root_.Filter.Eventually.of_forall fun a =>
        (toFullBlockMat_eq_blockMatEntry (coarseBlock (adaptedCellAt q j w) a) α β).symm)
  have hsum : Integrable
      (fun a => ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)) P :=
    integrable_of_entries fun α β => by
      simpa only [Matrix.sum_apply] using integrable_finsetSum Z fun w hw => hentry w hw α β
  have hgint : Integrable
      (fun a => (Z.card : ℝ)⁻¹ •
        ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)) P :=
    integrable_of_entries fun α β => by
      simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
      exact (integrable_finsetSum Z fun w hw => hentry w hw α β).const_mul _
  have hmono := integral_mono' (integrable_toFullBlockMat hintp) hgint
    (_root_.Filter.Eventually.of_forall hle)
  rw [integral_alignedAverage_eq_adaptedMean hP hq hlj hintj hZne] at hmono
  rwa [toFullBlockMat_adaptedMean_eq_integral hintp]

/-- **`E_p^q ≤ E_j^q`**, in the structural dialect of the doubled block. -/
theorem adaptedMean_le [NeZero d] {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    {j p : ℤ} (hlj : l ≤ j) (hjp : j ≤ p) (hintj : HasFiniteAdaptedMean P q j)
    (hintp : HasFiniteAdaptedMean P q p) :
    BlockMatLoewnerLE (adaptedMean P q p) (adaptedMean P q j) :=
  blockMatLoewnerLE_of_le (toFullBlockMat_adaptedMean_le hP hq hlj hjp hintj hintp)

/-! ## The relative mean and the determinant increment -/

/-- The adapted mean of a rounded adapted grid is a positive definite matrix on
the flattened carrier as soon as it is finite. -/
theorem posDef_toFullBlockMat_adaptedMean {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q) (r : ℤ)
    (hint : HasFiniteAdaptedMean P q r) : (toFullBlockMat (adaptedMean P q r)).PosDef :=
  posDef_toFullBlockMat (isSymmetricBlockMat_adaptedMean P q r)
    (blockPosDef_adaptedMean_of_isRoundedGrid hq r hint)

/-- The relative mean `P_{j,T}^q` is the literal congruence of the child mean by
the inverse square root of the parent mean. -/
theorem toFullBlockMat_relMean (P : Measure (CoeffSpace d)) (q : Mat d) (j T : ℤ) :
    toFullBlockMat (relMean P q j T) =
      matSqrt (toFullBlockMat (adaptedMean P q T))⁻¹ * toFullBlockMat (adaptedMean P q j) *
        matSqrt (toFullBlockMat (adaptedMean P q T))⁻¹ :=
  toFullBlockMat_normalizedBlock _ _

/-- The determinant increment `Δ_{j,T}^q` is the difference of the logarithms of
the determinants of the two flattened means. -/
theorem detIncrement_eq_log_det_sub (P : Measure (CoeffSpace d)) (q : Mat d) (j T : ℤ) :
    detIncrement P q j T =
      Real.log (toFullBlockMat (adaptedMean P q j)).det -
        Real.log (toFullBlockMat (adaptedMean P q T)).det :=
  rfl

/-- **`I ≤ P_{j,p}^q`.**  The relative mean of the fixed-grid recurrence lies
above the identity; this is the mean order conjugated by `(E_p^q)^{-1/2}`. -/
theorem blockMatLoewnerLE_blockIdentity_relMean [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hP : HCPoly.Frozen.IsStationaryLaw P) {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {j p : ℤ} (hlj : l ≤ j) (hjp : j ≤ p)
    (hintj : HasFiniteAdaptedMean P q j) (hintp : HasFiniteAdaptedMean P q p) :
    BlockMatLoewnerLE (Book.Ch02.blockIdentity d) (relMean P q j p) := by
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_blockIdentity, toFullBlockMat_relMean]
  exact one_le_normalize (posDef_toFullBlockMat_adaptedMean hq p hintp)
    (toFullBlockMat_adaptedMean_le hP hq hlj hjp hintj hintp)

/-- **`Δ_{j,p}^q ≥ 0`.**  The determinant increment of the fixed-grid recurrence
is nonnegative: the determinant is monotone for the Loewner order on positive
definite matrices, and the mean order puts the parent mean below the child. -/
theorem detIncrement_nonneg [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hP : HCPoly.Frozen.IsStationaryLaw P) {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {j p : ℤ} (hlj : l ≤ j) (hjp : j ≤ p)
    (hintj : HasFiniteAdaptedMean P q j) (hintp : HasFiniteAdaptedMean P q p) :
    0 ≤ detIncrement P q j p :=
  (determinant_transport (posDef_toFullBlockMat_adaptedMean hq j hintj)
    (posDef_toFullBlockMat_adaptedMean hq p hintp)
    (toFullBlockMat_adaptedMean_le hP hq hlj hjp hintj hintp)).2.1

/-- **The determinant identities for the parent-child normalization**, at the
adapted means: the relative
mean lies above the identity, the determinant increment is nonnegative, the
determinant of the relative mean is `e^{Δ_{j,p}}`, its spectral size is at most
`e^{Δ_{j,p}}`, and its trace gap `b = tr(P_{j,p} - I)` is at most
`e^{Δ_{j,p}} - 1`. -/
theorem determinant_transport_adaptedMean [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hP : HCPoly.Frozen.IsStationaryLaw P) {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {j p : ℤ} (hlj : l ≤ j) (hjp : j ≤ p)
    (hintj : HasFiniteAdaptedMean P q j) (hintp : HasFiniteAdaptedMean P q p) :
    BlockMatLoewnerLE (Book.Ch02.blockIdentity d) (relMean P q j p) ∧
      0 ≤ detIncrement P q j p ∧
        (toFullBlockMat (relMean P q j p)).det = Real.exp (detIncrement P q j p) ∧
          ‖toFullBlockMat (relMean P q j p)‖ ≤ Real.exp (detIncrement P q j p) ∧
            blockTrace (relMean P q j p) - 2 * (d : ℝ) ≤
              Real.exp (detIncrement P q j p) - 1 := by
  obtain ⟨-, hincr, hdet, hnorm, htr⟩ :=
    determinant_transport (posDef_toFullBlockMat_adaptedMean hq j hintj)
      (posDef_toFullBlockMat_adaptedMean hq p hintp)
      (toFullBlockMat_adaptedMean_le hP hq hlj hjp hintj hintp)
  have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
    simp [Fintype.card_sum, two_mul]
  rw [← toFullBlockMat_relMean] at hdet hnorm htr
  rw [Matrix.trace_sub, Matrix.trace_one, hcard] at htr
  exact ⟨blockMatLoewnerLE_blockIdentity_relMean hP hq hlj hjp hintj hintp, hincr, hdet,
    hnorm, htr⟩

end

end Recurrence
end HighContrast
end HCPolySupport
