/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.ColourClassAveraging

/-!
# High-contrast homogenization: Provider.Recurrence.AveragedEntries

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The entries of the centred aligned average

The averaging step of `p.fixed.geometry.parent.child.recurrence` applies
`l.fixed.geometry.matrix.averaging` to the average
`G = M^{-1}Σ_z 𝐀_j(z)` of the responses of the aligned scale-`j` children of the
parent cell.  This file carries that average down to the scalar level.

Two things happen.  First, normalization and centring are a fixed real-linear
map of the entries of a doubled block, so an entry of the normalized centred
average is the average of the entries of the normalized centred responses.
Second, the family of children splits into at most `3^d` colour classes, each of
which carries the independent-sum estimate; summing the classes and applying
Cauchy–Schwarz to the at most `3^d` resulting terms leaves a single square root
of the total cardinality, which is the `M^{-1/2}` gain of the printed proof once
the average is normalized.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Linearity of the normalized centred entry -/

/-- Interchange of a double sum over the block coordinates with a sum over a
finite index set, in the shape the entries of a normalized block take. -/
private theorem sum_mul_sum_mul_comm {ι : Type*} (s : Finset ι) (c : ℝ)
    (x y : BlockCoord d → ℝ) (u : ι → BlockCoord d → BlockCoord d → ℝ) :
    ∑ γ : BlockCoord d, ∑ δ : BlockCoord d, x δ * (c * ∑ w ∈ s, u w δ γ) * y γ
      = c * ∑ w ∈ s, ∑ γ : BlockCoord d, ∑ δ : BlockCoord d, x δ * u w δ γ * y γ := by
  have h1 : ∀ γ δ : BlockCoord d, x δ * (c * ∑ w ∈ s, u w δ γ) * y γ
      = ∑ w ∈ s, c * (x δ * u w δ γ * y γ) := by
    intro γ δ
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun w _ => by ring
  calc ∑ γ : BlockCoord d, ∑ δ : BlockCoord d, x δ * (c * ∑ w ∈ s, u w δ γ) * y γ
      = ∑ γ : BlockCoord d, ∑ δ : BlockCoord d, ∑ w ∈ s, c * (x δ * u w δ γ * y γ) :=
        Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => h1 γ δ
    _ = ∑ γ : BlockCoord d, ∑ w ∈ s, ∑ δ : BlockCoord d, c * (x δ * u w δ γ * y γ) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ w ∈ s, ∑ γ : BlockCoord d, ∑ δ : BlockCoord d, c * (x δ * u w δ γ * y γ) :=
        Finset.sum_comm
    _ = c * ∑ w ∈ s, ∑ γ : BlockCoord d, ∑ δ : BlockCoord d, x δ * u w δ γ * y γ := by
        simp only [Finset.mul_sum]

/-- **An entry of the normalized centred average is the average of the entries of
the normalized centred summands.**  Normalization and centring by deterministic
blocks are a fixed real-linear map of the entries, and the centring survives the
average because the weights sum to one. -/
theorem toFullBlockMat_normalizedBlock_blockSub_average_apply {ι : Type*} {Z : Finset ι}
    (hZ : Z.Nonempty) (A : ι → BlockMat d) (E F : BlockMat d) (α β : BlockCoord d) :
    toFullBlockMat (normalizedBlock
        (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ • ∑ w ∈ Z, toFullBlockMat (A w))) E) F) α β
      = (Z.card : ℝ)⁻¹ *
          ∑ w ∈ Z, toFullBlockMat (normalizedBlock (blockSub (A w) E) F) α β := by
  have hcard : (Z.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hZ)
  have hentry : ∀ δ γ : BlockCoord d,
      toFullBlockMat (blockSub
          (ofFullBlockMat ((Z.card : ℝ)⁻¹ • ∑ w ∈ Z, toFullBlockMat (A w))) E) δ γ
        = (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (toFullBlockMat (A w) δ γ - toFullBlockMat E δ γ) := by
    intro δ γ
    have hL : toFullBlockMat (blockSub
          (ofFullBlockMat ((Z.card : ℝ)⁻¹ • ∑ w ∈ Z, toFullBlockMat (A w))) E) δ γ
        = (Z.card : ℝ)⁻¹ * (∑ w ∈ Z, toFullBlockMat (A w) δ γ) - toFullBlockMat E δ γ := by
      rw [toFullBlockMat_blockSub_apply, toFullBlockMat_ofFullBlockMat, Matrix.smul_apply,
        smul_eq_mul, Matrix.sum_apply]
    have hR : (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, (toFullBlockMat (A w) δ γ - toFullBlockMat E δ γ)
        = (Z.card : ℝ)⁻¹ * (∑ w ∈ Z, toFullBlockMat (A w) δ γ) - toFullBlockMat E δ γ := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_sub, ← mul_assoc,
        inv_mul_cancel₀ hcard, one_mul]
    rw [hL, hR]
  have hRsum : ∑ w ∈ Z, toFullBlockMat (normalizedBlock (blockSub (A w) E) F) α β
      = ∑ w ∈ Z, ∑ γ : BlockCoord d, ∑ δ : BlockCoord d,
          matSqrt ((toFullBlockMat F)⁻¹) α δ *
            (toFullBlockMat (A w) δ γ - toFullBlockMat E δ γ) *
            matSqrt ((toFullBlockMat F)⁻¹) γ β := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [toFullBlockMat_normalizedBlock_apply]
    exact Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => by
      rw [toFullBlockMat_blockSub_apply]
  rw [toFullBlockMat_normalizedBlock_apply, hRsum]
  simp only [hentry]
  exact sum_mul_sum_mul_comm Z (Z.card : ℝ)⁻¹
    (fun δ => matSqrt ((toFullBlockMat F)⁻¹) α δ)
    (fun γ => matSqrt ((toFullBlockMat F)⁻¹) γ β)
    fun w δ γ => toFullBlockMat (A w) δ γ - toFullBlockMat E δ γ

/-! ## Summing the colour classes -/

/-- **The scalar estimate of `l.fixed.geometry.matrix.averaging` on a whole
family of aligned adapted cells.**  The family splits into at most `3^d` colour
classes, the independent-sum estimate applies to each, and Cauchy–Schwarz on the
at most `3^d` resulting square roots leaves the square root of the total
cardinality. -/
theorem lqNorm_sum_aligned_le {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hPs : HCPoly.Frozen.IsStationaryLaw P) (hP : HCPoly.Frozen.IsUnitRangeLaw P) {Q : ℝ}
    (hQ : 2 ≤ Q) {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q) {j : ℤ} (hj : l ≤ j)
    (hint : HasFiniteAdaptedMean P q j) (F : BlockMat d) {v : ℝ≥0∞} (hv : v ≠ ⊤)
    (Z : Finset (Fin d → ℤ)) (α β : BlockCoord d)
    (hbd : ∀ w ∈ Z, lqNorm P Q (fun a => toFullBlockMat (normalizedBlock
      (blockSub (coarseBlock (adaptedCellAt q j w) a) (adaptedMean P q j)) F) α β) ≤ v) :
    lqNorm P Q (fun a => ∑ w ∈ Z, toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (adaptedCellAt q j w) a) (adaptedMean P q j)) F) α β)
      ≤ ENNReal.ofReal
          ((2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q) *
            (Real.sqrt ((3 : ℝ) ^ d) * Real.sqrt (Z.card : ℝ) * v.toReal)) := by
  classical
  set cols : Finset (Fin d → ZMod 3) := Z.image fun w i => ((w i : ZMod 3)) with hcols
  set cls : (Fin d → ZMod 3) → Finset (Fin d → ℤ) :=
    fun c => Z.filter fun u => (fun i => ((u i : ZMod 3))) = c with hcls
  set Y : (Fin d → ℤ) → CoeffSpace d → ℝ := fun w a => toFullBlockMat (normalizedBlock
    (blockSub (coarseBlock (adaptedCellAt q j w) a) (adaptedMean P q j)) F) α β with hY
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_two hQ
  have hK0 : (0 : ℝ) ≤ v.toReal := ENNReal.toReal_nonneg
  have hconst : (0 : ℝ) ≤ 2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst *
      Real.sqrt Q := by
    have : (0 : ℝ) ≤ IndependentSums.rosenthalBennettIntegralConst := by
      simp only [IndependentSums.rosenthalBennettIntegralConst]
      positivity
    positivity
  have hdisj := pairwiseDisjoint_filter_intCast (d := d) Z
  have hunion := biUnion_filter_intCast_eq (d := d) Z
  have hsplit : (fun a : CoeffSpace d => ∑ w ∈ Z, Y w a)
      = ∑ c ∈ cols, fun a : CoeffSpace d => ∑ w ∈ cls c, Y w a := by
    funext a
    rw [Finset.sum_apply, ← hunion, Finset.sum_biUnion hdisj]
  have hmeasc : ∀ c ∈ cols,
      AEStronglyMeasurable (fun a : CoeffSpace d => ∑ w ∈ cls c, Y w a) P := by
    intro c _
    have hsum := Finset.aestronglyMeasurable_sum (cls c)
      fun w (_ : w ∈ cls c) => aestronglyMeasurable_toFullBlockMat_normalizedBlock_blockSub
        (hasMeasurableCoarseBlock_adaptedCellAt P (posDef_of_isRoundedGrid hq) j w)
        (adaptedMean P q j) F α β
    exact hsum.congr (Filter.Eventually.of_forall fun a => by
      simp only [hY, Finset.sum_apply])
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Q := by
    rw [ENNReal.one_le_ofReal]
    linarith only [hQ]
  have htri : lqNorm P Q (fun a => ∑ w ∈ Z, Y w a)
      ≤ ∑ c ∈ cols, lqNorm P Q (fun a => ∑ w ∈ cls c, Y w a) := by
    rw [hsplit]
    exact eLpNorm_sum_le hone
  have hclass : ∀ c ∈ cols, lqNorm P Q (fun a => ∑ w ∈ cls c, Y w a)
      ≤ ENNReal.ofReal
          ((2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q) *
            (Real.sqrt ((cls c).card : ℝ) * v.toReal)) :=
    fun c _ => lqNorm_sum_colourClass_le hPs hP hQ hq hj hint F hv Z c α β hbd
  have hsumcls : ∑ c ∈ cols, ((cls c).card : ℝ) = (Z.card : ℝ) := by
    have hcard : ∑ c ∈ cols, (cls c).card = Z.card := by
      rw [← Finset.card_biUnion fun c hc c' hc' hcc =>
        hdisj (Finset.mem_coe.mpr hc) (Finset.mem_coe.mpr hc') hcc, hunion]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcard
  have hsqrtsum : ∑ c ∈ cols, Real.sqrt ((cls c).card : ℝ)
      ≤ Real.sqrt ((3 : ℝ) ^ d) * Real.sqrt (Z.card : ℝ) := by
    have hnn : (0 : ℝ) ≤ ∑ c ∈ cols, Real.sqrt ((cls c).card : ℝ) :=
      Finset.sum_nonneg fun c _ => Real.sqrt_nonneg _
    have hcs : (∑ c ∈ cols, Real.sqrt ((cls c).card : ℝ)) ^ 2
        ≤ (3 : ℝ) ^ d * (Z.card : ℝ) := by
      have h1 : (∑ c ∈ cols, Real.sqrt ((cls c).card : ℝ)) ^ 2
          ≤ (cols.card : ℝ) * ∑ c ∈ cols, Real.sqrt ((cls c).card : ℝ) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      have h2 : ∑ c ∈ cols, Real.sqrt ((cls c).card : ℝ) ^ 2 = (Z.card : ℝ) := by
        rw [← hsumcls]
        exact Finset.sum_congr rfl fun c _ => Real.sq_sqrt (Nat.cast_nonneg _)
      have h3 : (cols.card : ℝ) ≤ (3 : ℝ) ^ d := by
        have := card_image_intCast_le (d := d) Z
        calc (cols.card : ℝ) ≤ ((3 ^ d : ℕ) : ℝ) := by exact_mod_cast this
          _ = (3 : ℝ) ^ d := by push_cast; ring
      rw [h2] at h1
      exact le_trans h1 (mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _))
    have hroot := Real.sqrt_le_sqrt hcs
    rw [Real.sqrt_sq hnn, Real.sqrt_mul (by positivity)] at hroot
    exact hroot
  refine le_trans htri (le_trans (Finset.sum_le_sum hclass) ?_)
  rw [← ENNReal.ofReal_sum_of_nonneg fun c _ => by positivity, ← Finset.mul_sum]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsqrtsum hK0) hconst

end

end Recurrence
end HighContrast
end HCPolySupport
