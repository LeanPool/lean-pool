/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedResponseSubadditivity

/-!
# High-contrast homogenization: Provider.Window.CountableSubadditivity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Countable subadditivity over an almost-everywhere partition

The response functional is subadditive over a countable disjoint family of
bounded convex cells when the weighted cell quadratic forms are summable.
-/

namespace HCPolySupport
namespace HighContrast
namespace Window

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The parent and a countable disjoint covering by subsets agree almost
everywhere when the uncovered part is null. -/
theorem ae_eq_iUnion_of_countable_aePartition {ι : Type*} {U : Set (Vec d)}
    {c : ι → Set (Vec d)} (hsub : ∀ i, c i ⊆ U)
    (hnull : volume (U \ ⋃ i, c i) = 0) : U =ᵐ[volume] ⋃ i, c i := by
  refine ae_eq_set.mpr ⟨hnull, ?_⟩
  rw [Set.sdiff_eq_empty.mpr (Set.iUnion_subset hsub), measure_empty]

/-- The weights of a countable almost-everywhere partition sum to one. -/
theorem tsum_weight_eq_one_of_countable_aePartition {ι : Type*} [Countable ι]
    {U : Set (Vec d)} {c : ι → Set (Vec d)}
    (hmeas : ∀ i, MeasurableSet (c i)) (hsub : ∀ i, c i ⊆ U)
    (hdisj : Pairwise fun i j => Disjoint (c i) (c j))
    (hnull : volume (U \ ⋃ i, c i) = 0)
    (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ⊤) :
    ∑' i, (volume (c i)).toReal / (volume U).toReal = 1 := by
  have hmeasure : volume U = ∑' i, volume (c i) := by
    calc
      volume U = volume (⋃ i, c i) :=
        measure_congr (ae_eq_iUnion_of_countable_aePartition hsub hnull)
      _ = ∑' i, volume (c i) := measure_iUnion hdisj hmeas
  have hcelltop : ∀ i, volume (c i) ≠ ⊤ := fun i =>
    Recurrence.measure_cell_ne_top_of_subset hUtop (hsub i)
  have htoReal : (volume U).toReal = ∑' i, (volume (c i)).toReal := by
    rw [hmeasure, ENNReal.tsum_toReal_eq hcelltop]
  rw [tsum_div_const, ← htoReal,
    div_self (ENNReal.toReal_pos hU0 hUtop).ne']

/-- The volume average over a countable almost-everywhere partition is the
weighted sum of the cell averages. -/
theorem volumeAverage_eq_tsum_weight_of_countable_aePartition
    {ι : Type*} [Countable ι] {U : Set (Vec d)} {c : ι → Set (Vec d)}
    {f : Vec d → ℝ} (hmeas : ∀ i, MeasurableSet (c i))
    (hsub : ∀ i, c i ⊆ U)
    (hdisj : Pairwise fun i j => Disjoint (c i) (c j))
    (hnull : volume (U \ ⋃ i, c i) = 0) (hint : IntegrableOn f U volume)
    (hcell0 : ∀ i, volume (c i) ≠ 0) (hUtop : volume U ≠ ⊤) :
    volumeAverage U f =
      ∑' i, (volume (c i)).toReal / (volume U).toReal * volumeAverage (c i) f := by
  have hUnionSub : (⋃ i, c i) ⊆ U := Set.iUnion_subset hsub
  have hIntegral : ∫ x in U, f x = ∑' i, ∫ x in c i, f x := by
    calc
      ∫ x in U, f x = ∫ x in ⋃ i, c i, f x := by
        rw [Measure.restrict_congr_set
          (ae_eq_iUnion_of_countable_aePartition hsub hnull)]
      _ = ∑' i, ∫ x in c i, f x :=
        integral_iUnion hmeas hdisj (hint.mono_set hUnionSub)
  have hcellIntegral : ∀ i,
      ∫ x in c i, f x = (volume (c i)).toReal * volumeAverage (c i) f := by
    intro i
    have hpos : 0 < (volume (c i)).toReal :=
      ENNReal.toReal_pos (hcell0 i)
        (Recurrence.measure_cell_ne_top_of_subset hUtop (hsub i))
    rw [volumeAverage, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  rw [volumeAverage, hIntegral]
  simp_rw [hcellIntegral]
  rw [← tsum_mul_left]
  exact tsum_congr fun i => by ring

/-- The weighted cell averages over a countable measurable partition form a
summable family whenever the integrand is integrable on the parent. -/
theorem summable_weight_mul_volumeAverage_of_countable_aePartition
    {ι : Type*} [Countable ι] {U : Set (Vec d)} {c : ι → Set (Vec d)}
    {f : Vec d → ℝ} (hmeas : ∀ i, MeasurableSet (c i))
    (hsub : ∀ i, c i ⊆ U)
    (hdisj : Pairwise fun i j => Disjoint (c i) (c j))
    (hint : IntegrableOn f U volume) (hcell0 : ∀ i, volume (c i) ≠ 0)
    (hUtop : volume U ≠ ⊤) :
    Summable fun i =>
      (volume (c i)).toReal / (volume U).toReal * volumeAverage (c i) f := by
  have hUnionSub : (⋃ i, c i) ⊆ U := Set.iUnion_subset hsub
  have hIntegralSummable : Summable fun i => ∫ x in c i, f x :=
    (hasSum_integral_iUnion hmeas hdisj (hint.mono_set hUnionSub)).summable
  have hrewrite : (fun i =>
      (volume (c i)).toReal / (volume U).toReal * volumeAverage (c i) f) =
      fun i => (volume U).toReal⁻¹ * ∫ x in c i, f x := by
    funext i
    have hcellReal : (volume (c i)).toReal ≠ 0 :=
      (ENNReal.toReal_pos (hcell0 i)
        (Recurrence.measure_cell_ne_top_of_subset hUtop (hsub i))).ne'
    rw [volumeAverage, div_eq_mul_inv]
    calc
      (volume (c i)).toReal * (volume U).toReal⁻¹ *
            ((volume (c i)).toReal⁻¹ * ∫ x in c i, f x) =
          ((volume (c i)).toReal * (volume (c i)).toReal⁻¹) *
            ((volume U).toReal⁻¹ * ∫ x in c i, f x) := by ring
      _ = (volume U).toReal⁻¹ * ∫ x in c i, f x := by
        rw [mul_inv_cancel₀ hcellReal, one_mul]
  rw [hrewrite]
  exact hIntegralSummable.mul_left _

/-- Countable subadditivity of the coarse response in quadratic-form order.
The summability premise is a convergence condition, not an estimate: callers
prove it from their quantitative row bound. -/
theorem blockQuadratic_le_tsum_weight_of_countable_aePartition [NeZero d]
    {ι : Type*} [Countable ι] {U : Set (Vec d)} {c : ι → Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hU0 : volume U ≠ 0) (a : CoeffSpace d)
    (hc : ∀ i, IsOpenBoundedConvexDomain (c i)) (hsub : ∀ i, c i ⊆ U)
    (hdisj : Pairwise fun i j => Disjoint (c i) (c j))
    (hnull : volume (U \ ⋃ i, c i) = 0)
    (hcell0 : ∀ i, volume (c i) ≠ 0) (X : BlockVec d)
    (hsum : Summable fun i =>
      (volume (c i)).toReal / (volume U).toReal *
        (1 / 2 * blockVecDot X (blockMatVecMul (coarseBlock (c i) a) X))) :
    1 / 2 * blockVecDot X (blockMatVecMul (coarseBlock U a) X) ≤
      ∑' i, (volume (c i)).toReal / (volume U).toReal *
        (1 / 2 * blockVecDot X (blockMatVecMul (coarseBlock (c i) a) X)) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hfm, hfell, hae⟩ :=
    exists_pointwise_elliptic_representative a.2 hU.isBoundedDomain.isBounded
  have hrep : ∀ V : Set (Vec d), coarseBlock V a = coarseBlockMatrix V f :=
    fun V => coarseBlock_eq_of_ae_eq a hae
  have hEll : IsEllipticFieldOn lam Lam U f :=
    Recurrence.isEllipticFieldOn_of_measurable hfm hfell hU.isOpen.measurableSet
  have hUtop : volume U ≠ ⊤ := hU.volume_lt_top.ne
  have : IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  have hweights := tsum_weight_eq_one_of_countable_aePartition
    (fun i => (hc i).isOpen.measurableSet) hsub hdisj hnull hU0 hUtop
  set p : Vec d := -X.1 with hp
  set q : Vec d := X.2 with hq
  have hX : ((-p, q) : BlockVec d) = X := by rw [hp, hq, neg_neg]
  have hparent : 1 / 2 * blockVecDot X (blockMatVecMul (coarseBlock U a) X) =
      ResponseJ U p q f + vecDot p q := by
    rw [hrep, Recurrence.responseJ_eq_blockQuadratic hU hEll
      (ENNReal.toReal_pos hU0 hUtop) p q, hX]
    ring
  have hcell : ∀ i,
      1 / 2 * blockVecDot X (blockMatVecMul (coarseBlock (c i) a) X) =
        ResponseJ (c i) p q f + vecDot p q := by
    intro i
    have hElli : IsEllipticFieldOn lam Lam (c i) f :=
      IsEllipticFieldOn.mono hEll (hc i).isOpen.measurableSet (hsub i)
    have htopi := Recurrence.measure_cell_ne_top_of_subset hUtop (hsub i)
    rw [hrep, Recurrence.responseJ_eq_blockQuadratic (hc i) hElli
      (ENNReal.toReal_pos (hcell0 i) htopi) p q, hX]
    ring
  have hweightSummable : Summable fun i =>
      (volume (c i)).toReal / (volume U).toReal := by
    by_contra hnot
    have hzero := tsum_eq_zero_of_not_summable hnot
    rw [hweights] at hzero
    norm_num at hzero
  have hrespSummable : Summable fun i =>
      (volume (c i)).toReal / (volume U).toReal * ResponseJ (c i) p q f := by
    have hrewrite : (fun i =>
        (volume (c i)).toReal / (volume U).toReal * ResponseJ (c i) p q f) =
      (fun i => (volume (c i)).toReal / (volume U).toReal *
          (1 / 2 * blockVecDot X (blockMatVecMul (coarseBlock (c i) a) X))) -
      (fun i => (volume (c i)).toReal / (volume U).toReal * vecDot p q) := by
      funext i
      simp only [Pi.sub_apply]
      rw [hcell i]
      ring
    rw [hrewrite]
    exact hsum.sub (hweightSummable.mul_right _)
  have hJ : ResponseJ U p q f ≤
      ∑' i, (volume (c i)).toReal / (volume U).toReal * ResponseJ (c i) p q f := by
    refine csSup_le (responseJValueSet_nonempty U p q f) ?_
    rintro m ⟨u, rfl⟩
    have hint : IntegrableOn (scalarResponseIntegrand U f p q u) U volume :=
      scalarResponseIntegrand_integrableOn_of_isEllipticFieldOn hEll p q u
    have havgSummable :=
      summable_weight_mul_volumeAverage_of_countable_aePartition
        (fun i => (hc i).isOpen.measurableSet) hsub hdisj hint hcell0 hUtop
    rw [volumeAverage_eq_tsum_weight_of_countable_aePartition
      (fun i => (hc i).isOpen.measurableSet) hsub hdisj hnull hint hcell0 hUtop]
    refine havgSummable.tsum_le_tsum (fun i => ?_) hrespSummable
    have : IsFiniteMeasure (volumeMeasureOn (c i)) := by
      simpa [volumeMeasureOn] using (hc i).isFiniteMeasure_restrict_volume
    have hElli : IsEllipticFieldOn lam Lam (c i) f :=
      IsEllipticFieldOn.mono hEll (hc i).isOpen.measurableSet (hsub i)
    have hvol : (volume (c i)).toReal ≠ 0 :=
      (ENNReal.toReal_pos (hcell0 i)
        (Recurrence.measure_cell_ne_top_of_subset hUtop (hsub i))).ne'
    have hcongr : scalarResponseIntegrand U f p q u =
        scalarResponseIntegrand (c i) f p q
          (u.restrictOfIsEllipticFieldOn hU.isOpen (hc i).isOpen (hsub i) hElli) := rfl
    refine mul_le_mul_of_nonneg_left ?_
      (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    rw [hcongr]
    exact le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn hElli hvol p q
      (responseJValueSet_mem (c i) p q f _)
  rw [hparent]
  have hseries :
      (∑' i, (volume (c i)).toReal / (volume U).toReal *
        (1 / 2 * blockVecDot X (blockMatVecMul (coarseBlock (c i) a) X))) =
      (∑' i, (volume (c i)).toReal / (volume U).toReal *
        ResponseJ (c i) p q f) + vecDot p q := by
    simp_rw [hcell, mul_add]
    rw [Summable.tsum_add hrespSummable (hweightSummable.mul_right _), tsum_mul_right,
      hweights, one_mul]
  rw [hseries]
  linarith only [hJ]

end

end Window
end HighContrast
end HCPolySupport
