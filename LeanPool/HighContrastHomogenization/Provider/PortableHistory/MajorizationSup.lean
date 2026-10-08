/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationIndex

/-!
# High-contrast homogenization: Provider.PortableHistory.MajorizationSup

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The centered maximum as a statistic

Three facts about the supremum in `e.scale.selection.fluctuation.history` are used by
the majorization argument of `p.fixed.geometry.one.grid.propagation`, and none of them depends
on which range of scales or which family of cells the supremum runs over.

*Maximum to sum.*  The `Q`-th power of a maximum over a finite family is at most
the sum of the `Q`-th powers.  This is the step the printed proof calls
"max-to-sum", and it is what converts a maximum over the `3^{d(T-b)}` children
of the terminal cell into a sum with the counting factor in front.

*Measurability.*  The supremum runs over countably many scales and countably
many aligned centers, and each term is a continuous function of the entries of
the coarse response; the measurability of the variational coarse block
therefore makes the whole maximum a measurable statistic, which is what allows
the sum to be integrated term by term.

*Change of variables.*  Under stationarity of the coefficient law an integer translation
preserves the law, so the lower integral of any statistic is unchanged when the
sample is translated.

The last statement recorded here is the centered moment `v_j^q` of
`p.fixed.geometry.one.grid.propagation` written as the lower integral of the `Q`-th power of
the Schatten size, which is the form in which the scales above the checkpoint
are summed.
-/

namespace HCPolySupport
namespace HighContrast
namespace PortableHistory

open MeasureTheory

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix ENNReal

noncomputable section

/-! ## Maximum to sum -/

/-- **Max-to-sum.**  The `Q`-th power of a maximum over a finite family is at
most the sum of the `Q`-th powers. -/
theorem iSup_finset_rpow_le_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) {Q : ℝ}
    (hQ : 0 < Q) : (⨆ i ∈ s, f i) ^ Q ≤ ∑ i ∈ s, f i ^ Q := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [ENNReal.zero_rpow_of_pos hQ]
  | cons c s hc ih =>
      rw [Finset.sum_cons]
      have hsup : (⨆ i ∈ Finset.cons c s hc, f i) = max (f c) (⨆ i ∈ s, f i) := by
        rw [← Finset.sup_eq_iSup, ← Finset.sup_eq_iSup, Finset.sup_cons]
      rw [hsup]
      rcases le_total (f c) (⨆ i ∈ s, f i) with h | h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_of_le zero_le ih
      · rw [max_eq_left h]
        exact le_add_of_le_of_nonneg le_rfl zero_le

/-- **The admissibility `a ≤ Qρ_max - d` absorbs the counting factor.**  The
weight of a scale gap `u`, raised to the power `Q` and multiplied by the number
`3^{du}` of cells of that gap, is at most the weight `3^{-au}` times whatever
dominates the `Q`-th power of the renormalization cost. -/
theorem three_rpow_admissible_le {Q a rhoMax dd u lam g : ℝ} (hadm : a ≤ Q * rhoMax - dd)
    (hu : 0 ≤ u) (hlam : 0 ≤ lam) (hlamg : lam ^ Q ≤ g) :
    ((3 : ℝ) ^ (-rhoMax * u) * lam) ^ Q * (3 : ℝ) ^ (dd * u) ≤ (3 : ℝ) ^ (-a * u) * g := by
  have hprod : ((3 : ℝ) ^ (-rhoMax * u) * lam) ^ Q * (3 : ℝ) ^ (dd * u) =
      (3 : ℝ) ^ (-rhoMax * u * Q + dd * u) * lam ^ Q := by
    rw [Real.mul_rpow (by positivity) hlam, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring
  have hexp : -rhoMax * u * Q + dd * u ≤ -a * u := by
    have h := mul_le_mul_of_nonneg_right hadm hu
    linarith only [h]
  rw [hprod]
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) hlamg
    (Real.rpow_nonneg hlam Q) (Real.rpow_nonneg (by norm_num) _)

section Statistic

variable {d : ℕ}

/-! ## The centered maximum is measurable -/

/-- **The centered maximum is a measurable statistic.**  Countably many scales,
countably many aligned centers, and a scalar size that is a continuous function
of the entries of the response. -/
theorem aemeasurable_adaptedSup {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    {F : BlockMat d} (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F)
    (g : ℤ → ℝ) (jlo jhi : ℤ) (S : Set (Vec d)) :
    AEMeasurable (fun x => ⨆ (j : ℤ) (_ : jlo ≤ j) (_ : j ≤ jhi) (w : Fin d → ℤ)
        (_ : adaptedCellCenter q j w ∈ S),
      ENNReal.ofReal (g j *
        blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j)) F)) P := by
  have hbase : ∀ (j : ℤ) (w : Fin d → ℤ), AEMeasurable (fun x : CoeffSpace d =>
      ENNReal.ofReal (g j *
        blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j)) F)) P := by
    intro j w
    have hmeas := aemeasurable_blockSize_coarseBlock_sub
      (Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P hq j w)
      (Recurrence.isSymmetricBlockMat_adaptedMean P q j) hF hFpd
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hmeas.const_mul (g j))
  exact AEMeasurable.iSup fun j => AEMeasurable.iSup fun _ => AEMeasurable.iSup fun _ =>
    AEMeasurable.iSup fun w => AEMeasurable.iSup fun _ => hbase j w

/-- **The centered maximum over the aligned cells of one scale is a measurable
statistic.** -/
theorem aemeasurable_adaptedCellSup {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    {F : BlockMat d} (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F)
    (c : ℝ) (j : ℤ) (S : Set (Vec d)) :
    AEMeasurable (fun x => ⨆ (w : Fin d → ℤ) (_ : adaptedCellCenter q j w ∈ S),
      ENNReal.ofReal (c *
        blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j)) F)) P := by
  have hbase : ∀ w : Fin d → ℤ, AEMeasurable (fun x : CoeffSpace d =>
      ENNReal.ofReal (c *
        blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j)) F)) P := by
    intro w
    have hmeas := aemeasurable_blockSize_coarseBlock_sub
      (Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P hq j w)
      (Recurrence.isSymmetricBlockMat_adaptedMean P q j) hF hFpd
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hmeas.const_mul c)
  exact AEMeasurable.iSup fun w => AEMeasurable.iSup fun _ => hbase w

/-! ## Change of variables along an integer translation -/

/-- **An integer translation does not move a lower integral.**  This is
stationarity of the coefficient law read through the change of variables. -/
theorem lintegral_comp_translateCoeff {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {f : CoeffSpace d → ℝ≥0∞} (hf : AEMeasurable f P)
    (z : Fin d → ℤ) : ∫⁻ x, f (translateCoeff z x) ∂P = ∫⁻ x, f x ∂P := by
  have hmap : AEMeasurable f (Measure.map (translateCoeff z) P) := by rwa [hP z]
  have h := lintegral_map' hmap (measurable_translateCoeff z).aemeasurable
  rw [← h, hP z]

/-- **Max-to-sum over the children of a cell.**  A maximum over a finite family
of translates is integrated term by term, and every term contributes the same
lower integral by stationarity of the coefficient law; only the cardinality survives. -/
theorem lintegral_iSup_translate_le {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {Q : ℝ} (hQ : 0 < Q)
    {F : CoeffSpace d → ℝ≥0∞} (hF : AEMeasurable F P) (Z : Finset (Fin d → ℤ))
    (v : (Fin d → ℤ) → Fin d → ℤ) :
    ∫⁻ x, (⨆ (y : Fin d → ℤ) (_ : y ∈ Z), F (translateCoeff (v y) x)) ^ Q ∂P ≤
      (Z.card : ℝ≥0∞) * ∫⁻ x, F x ^ Q ∂P := by
  have hFQ : AEMeasurable (fun z => F z ^ Q) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hF
  have hmeas : ∀ y : Fin d → ℤ,
      AEMeasurable (fun x => F (translateCoeff (v y) x) ^ Q) P := by
    intro y
    have hmap : AEMeasurable (fun z => F z ^ Q) (Measure.map (translateCoeff (v y)) P) := by
      rwa [hP (v y)]
    exact hmap.comp_aemeasurable (measurable_translateCoeff (v y)).aemeasurable
  calc ∫⁻ x, (⨆ (y : Fin d → ℤ) (_ : y ∈ Z), F (translateCoeff (v y) x)) ^ Q ∂P
      ≤ ∫⁻ x, ∑ y ∈ Z, F (translateCoeff (v y) x) ^ Q ∂P :=
        lintegral_mono fun x => iSup_finset_rpow_le_sum Z _ hQ
    _ = ∑ y ∈ Z, ∫⁻ x, F (translateCoeff (v y) x) ^ Q ∂P :=
        lintegral_finsetSum' Z fun y _ => hmeas y
    _ = ∑ _y ∈ Z, ∫⁻ x, F x ^ Q ∂P :=
        Finset.sum_congr rfl fun y _ => lintegral_comp_translateCoeff hP hFQ (v y)
    _ = (Z.card : ℝ≥0∞) * ∫⁻ x, F x ^ Q ∂P := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ## The centered moment as a lower integral -/

/-- **The `Q`-th power of the centered moment `v_j^q` is the lower integral of
the `Q`-th power of the Schatten size.** -/
theorem centeredMoment_rpow (P : Measure (CoeffSpace d)) {Q : ℝ} (hQ : 0 < Q) (q : Mat d)
    (j : ℤ)
    (hmeas : AEStronglyMeasurable (fun x => schattenSize Q
      (blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
      (adaptedMean P q j)) P) :
    centeredMoment P Q q j ^ Q =
      ∫⁻ x, ENNReal.ofReal (schattenSize Q
        (blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
        (adaptedMean P q j)) ^ Q ∂P := by
  have hne : ENNReal.ofReal Q ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hQ
  have htoReal : (ENNReal.ofReal Q).toReal = Q := ENNReal.toReal_ofReal hQ.le
  have hnn : ∀ x : CoeffSpace d, (0 : ℝ) ≤ schattenSize Q
      (blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
      (adaptedMean P q j) :=
    fun x => Recurrence.zero_le_schattenNorm (isSymmetricBlockMat_normalizedBlock
      (isSymmetricBlockMat_blockSub (isSymmetricBlockMat_coarseBlock _ x)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q j))) Q
  rw [centeredMoment, lqSchattenSize,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hne (by simp) hmeas, htoReal, one_div,
    ENNReal.rpow_inv_rpow hQ.ne']
  exact lintegral_congr fun x => by rw [Real.enorm_eq_ofReal (hnn x)]

end Statistic

end

end PortableHistory
end HighContrast
end HCPolySupport
