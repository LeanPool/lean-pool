/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.OptimizerReadoutMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormState
public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNorm
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewCoefficient
public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffBasic

/-!
# High-contrast homogenization: Provider.Response.LocalizedOptimizerObservables

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Localized observables of the doubled optimizer state

The weak-norm estimates for the optimizer state read the doubled optimizer state
of a parent cell through localized averages: an average of one doubled coordinate
over an aligned child cell, and a localized oscillation average against the
pre-Young cutoff.  Both are weighted coordinate readouts of the optimizer state
of the parent cell, with a weight supported in the child cell, so both are
measurable functions of the sample.

The constant skew shift of the coefficient field acts on the coefficient space by
translating each generating linear statistic by a constant, so it is measurable
and the observables of the shifted sample are measurable as well.
-/

namespace HCPolySupport
namespace HighContrast
namespace Selection

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The constant skew shift is measurable -/

/-- A generating linear statistic of a constant skew shift is the statistic of
the sample, translated by a constant. -/
theorem coeffPairing_subSkew (e e' : Vec d) {V : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsLocalTest V φ) (g : Mat d) (hg : IsSkewMat g) (a : CoeffSpace d) :
    coeffPairing e e' φ (a.subSkew g hg) =
      coeffPairing e e' φ a - vecDot e' (matVecMul g e) * ∫ x, φ x ∂volume := by
  have hcoe : ((a.subSkew g hg).1 : Vec d → Mat d) =ᵐ[volume]
      fun x => (a.1 x : Mat d) - g :=
    MeasureTheory.AEEqFun.coeFn_mk _ _
  have hint1 : Integrable (fun x => vecDot e' (matVecMul (a.1 x) e) * φ x) volume :=
    integrable_coeffPairing_integrand e e' hφ a
  have hφint : Integrable φ volume :=
    (hφ.contDiff.continuous).integrable_of_hasCompactSupport hφ.hasCompactSupport
  have hint2 : Integrable (fun x => vecDot e' (matVecMul g e) * φ x) volume :=
    hφint.const_mul _
  have hpt : ∀ᵐ x ∂volume,
      vecDot e' (matVecMul (((a.subSkew g hg).1 : Vec d → Mat d) x) e) * φ x =
        vecDot e' (matVecMul (a.1 x) e) * φ x -
          vecDot e' (matVecMul g e) * φ x := by
    filter_upwards [hcoe] with x hx
    rw [hx]
    simp [vecDot, matVecMul, Finset.sum_sub_distrib, mul_sub, mul_comm]
  calc
    coeffPairing e e' φ (a.subSkew g hg)
        = ∫ x, (vecDot e' (matVecMul (a.1 x) e) * φ x -
            vecDot e' (matVecMul g e) * φ x) ∂volume :=
          integral_congr_ae hpt
    _ = coeffPairing e e' φ a -
          ∫ x, vecDot e' (matVecMul g e) * φ x ∂volume := integral_sub hint1 hint2
    _ = coeffPairing e e' φ a - vecDot e' (matVecMul g e) * ∫ x, φ x ∂volume := by
          rw [integral_const_mul]

/-- **The constant skew shift is measurable** on the coefficient space: it pulls
each generating linear statistic back to a translate of itself. -/
theorem measurable_subSkew (g : Mat d) (hg : IsSkewMat g) :
    Measurable fun a : CoeffSpace d => a.subSkew g hg := by
  change @Measurable (CoeffSpace d) (CoeffSpace d) (coeffSigma d Set.univ)
    (MeasurableSpace.generateFrom
      {s | ∃ (e e' : Vec d) (φ : Vec d → ℝ), IsLocalTest Set.univ φ ∧
        ∃ t : Set ℝ, MeasurableSet t ∧ s = coeffPairing e e' φ ⁻¹' t})
    (fun a => a.subSkew g hg)
  apply measurable_generateFrom
  rintro s ⟨e, e', φ, hφ, t, ht, rfl⟩
  have hset : (fun a : CoeffSpace d => a.subSkew g hg) ⁻¹' (coeffPairing e e' φ ⁻¹' t) =
      coeffPairing e e' φ ⁻¹'
        ((fun y : ℝ => y - vecDot e' (matVecMul g e) * ∫ x, φ x ∂volume) ⁻¹' t) := by
    ext a
    change coeffPairing e e' φ (a.subSkew g hg) ∈ t ↔ _
    rw [coeffPairing_subSkew e e' hφ g hg a]
    rfl
  rw [hset]
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨e, e', φ, hφ, _, (measurable_sub_const _) ht, rfl⟩

/-! ## The adjoint sample is measurable -/

/-- A generating linear statistic of the adjoint sample is the statistic of the
sample with its two directions exchanged. -/
theorem coeffPairing_transpose (e e' : Vec d) (φ : Vec d → ℝ) (a : CoeffSpace d) :
    coeffPairing e e' φ a.transpose = coeffPairing e' e φ a := by
  have hcoe : ((a.transpose).1 : Vec d → Mat d) =ᵐ[volume]
      fun x => matTranspose (a.1 x) :=
    MeasureTheory.AEEqFun.coeFn_comp matTranspose continuous_id.matrix_transpose a.1
  have hswap : ∀ A : Mat d,
      vecDot e' (matVecMul (matTranspose A) e) = vecDot e (matVecMul A e') := by
    intro A
    simp only [vecDot, matVecMul, matTranspose, Matrix.transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine integral_congr_ae ?_
  filter_upwards [hcoe] with x hx
  rw [hx, hswap]

/-- **The adjoint sample is measurable** on the coefficient space: transposition
exchanges the two direction vectors of each generating linear statistic. -/
theorem measurable_transpose : Measurable (CoeffSpace.transpose (d := d)) := by
  change @Measurable (CoeffSpace d) (CoeffSpace d) (coeffSigma d Set.univ)
    (MeasurableSpace.generateFrom
      {s | ∃ (e e' : Vec d) (φ : Vec d → ℝ), IsLocalTest Set.univ φ ∧
        ∃ t : Set ℝ, MeasurableSet t ∧ s = coeffPairing e e' φ ⁻¹' t})
    CoeffSpace.transpose
  apply measurable_generateFrom
  rintro s ⟨e, e', φ, hφ, t, ht, rfl⟩
  have hset : CoeffSpace.transpose (d := d) ⁻¹' (coeffPairing e e' φ ⁻¹' t) =
      coeffPairing e' e φ ⁻¹' t := by
    ext a
    change coeffPairing e e' φ a.transpose ∈ t ↔ _
    rw [coeffPairing_transpose e e' φ a]
    rfl
  rw [hset]
  exact MeasurableSpace.measurableSet_generateFrom ⟨e', e, φ, hφ, t, ht, rfl⟩

/-! ## Square integrability of a bounded localized weight -/

/-- A bounded continuous weight, restricted to a measurable subset and extended
by zero, is square integrable on a cell of finite measure. -/
theorem memScalarL2_indicator_of_bounded {U V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hV : MeasurableSet V) {w : Vec d → ℝ}
    (hw : Continuous w) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |w x| ≤ C) :
    MemScalarL2 U (Set.indicator V w) := by
  refine MeasureTheory.MemLp.of_bound
    (hw.aestronglyMeasurable.indicator hV) C (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ V
  · simpa [Set.indicator, hx, Real.norm_eq_abs] using hbound x
  · simpa [Set.indicator, hx] using hC

/-- The localized oscillation of the pre-Young cutoff is square integrable on
the parent cell. -/
theorem memScalarL2_indicator_cutoffOscillation [NeZero d] {q : Mat d} (hq : q.PosDef)
    (t : ℤ) {U V : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hV : MeasurableSet V) :
    MemScalarL2 U (Set.indicator V fun x =>
      Response.adaptedPreYoungCutoff q hq t x -
        volumeAverage V (Response.adaptedPreYoungCutoff q hq t)) := by
  set m : ℝ := volumeAverage V (Response.adaptedPreYoungCutoff q hq t) with hm
  refine memScalarL2_indicator_of_bounded hV
    (((Response.adaptedPreYoungCutoff_smooth hq t).continuous).sub continuous_const)
    (C := 2 + |m|) (by positivity) fun x => ?_
  have h0 : 0 ≤ Response.adaptedPreYoungCutoff q hq t x := Response.adaptedPreYoungCutoff_nonneg hq t x
  have h2 : Response.adaptedPreYoungCutoff q hq t x ≤ 2 := Response.adaptedPreYoungCutoff_le_two hq t x
  have hmabs : -|m| ≤ m ∧ m ≤ |m| := ⟨neg_abs_le m, le_abs_self m⟩
  rw [abs_le]
  constructor
  · linarith only [h0, hmabs.2]
  · linarith only [h2, hmabs.1]

/-! ## Localized weighted averages of the optimizer state -/

/-- Restricting a weighted integral to a subset is testing against the extension
of the weight by zero. -/
theorem setIntegral_indicator_mul {V U : Set (Vec d)} (hV : MeasurableSet V)
    (hVU : V ⊆ U) (w F : Vec d → ℝ) :
    ∫ x in U, Set.indicator V w x * F x ∂volume = ∫ x in V, w x * F x ∂volume := by
  have hfun : (fun x => Set.indicator V w x * F x) = Set.indicator V fun x => w x * F x := by
    funext x
    by_cases hx : x ∈ V <;> simp [Set.indicator, hx]
  rw [hfun, MeasureTheory.setIntegral_indicator hV, Set.inter_eq_self_of_subset_right hVU]

/-- A localized weighted average of one doubled coordinate of the optimizer
state is a weighted coordinate readout on the whole cell. -/
theorem volumeAverage_weighted_optimizerBlockState {U : Book.Ch02.Domain d}
    (aU : Book.Ch02.CoeffOn U) (p q : Vec d) (alpha : BlockCoord d)
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ (U : Set (Vec d)))
    (w : Vec d → ℝ) :
    volumeAverage V
        (fun x => w x * toFullBlockVec (optimizerBlockState U aU p q x) alpha) =
      (volume V).toReal⁻¹ *
        optimizerStateReadout U aU p q alpha (Set.indicator V w) := by
  rw [volumeAverage, optimizerStateReadout, setIntegral_indicator_mul hV hVU]

/-- **A localized weighted average of one doubled coordinate of the optimizer
state is measurable on the coefficient space.** -/
theorem measurable_volumeAverage_weighted_optimizerBlockState_coeffSpace
    {U : Book.Ch02.Domain d} (hUopen : IsOpen (U : Set (Vec d)))
    (hUbdd : IsBoundedDomain (U : Set (Vec d)))
    (hvol : 0 < (volume (U : Set (Vec d))).toReal)
    (p q : Vec d) (alpha : BlockCoord d)
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ (U : Set (Vec d)))
    {w : Vec d → ℝ} (hw : MemScalarL2 (U : Set (Vec d)) (Set.indicator V w)) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage V (fun x =>
        w x * toFullBlockVec (optimizerBlockState U (a.coeffOn U) p q x) alpha) := by
  have hrw : (fun a : CoeffSpace d =>
      volumeAverage V (fun x =>
        w x * toFullBlockVec (optimizerBlockState U (a.coeffOn U) p q x) alpha)) =
      fun a : CoeffSpace d =>
        (volume V).toReal⁻¹ *
          optimizerStateReadout U (a.coeffOn U) p q alpha (Set.indicator V w) := by
    funext a
    exact volumeAverage_weighted_optimizerBlockState (a.coeffOn U) p q alpha hV hVU w
  rw [hrw]
  exact (measurable_optimizerStateReadout_coeffSpace hUopen hUbdd hvol p q alpha hw).const_mul _

/-! ## The observables of the diagonal weak estimate -/

/-- The doubled optimizer state of the diagonal weak estimate is the doubled
optimizer state of its adapted parent cell. -/
theorem diagonalWeakState_eq_optimizerBlockState {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (a : CoeffSpace d) (p r : Vec d) :
    Response.diagonalWeakState hq t a p r =
      optimizerBlockState (Response.adaptedDomain hq t)
        (a.coeffOn (Response.adaptedDomain hq t)) p r :=
  rfl

/-- One doubled coordinate of a block cell average is the localized average of
that coordinate. -/
theorem toFullBlockVec_blockCellAverage (V : Set (Vec d)) (F : Vec d → BlockVec d)
    (alpha : BlockCoord d) :
    toFullBlockVec (Response.blockCellAverage V F) alpha =
      volumeAverage V fun x => toFullBlockVec (F x) alpha := by
  cases alpha with
  | inl i => rfl
  | inr i => rfl

/-- **The localized oscillation readout of the terminal optimizer state on an
aligned child cell is measurable**, for the sample sigma-field of the
coefficient space. -/
theorem measurable_volumeAverage_weighted_diagonalWeakState_subSkew
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (alpha : BlockCoord d) {V : Set (Vec d)} (hV : MeasurableSet V)
    (hVU : V ⊆ adaptedCell q t) {w : Vec d → ℝ}
    (hw : MemScalarL2 (adaptedCell q t) (Set.indicator V w)) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage V (fun x =>
        w x * toFullBlockVec (Response.diagonalWeakState hq t (a.subSkew g hg) p r x) alpha) := by
  have hbase : Measurable fun b : CoeffSpace d =>
      volumeAverage V (fun x =>
        w x * toFullBlockVec (Response.diagonalWeakState hq t b p r x) alpha) := by
    simpa only [diagonalWeakState_eq_optimizerBlockState] using
      measurable_volumeAverage_weighted_optimizerBlockState_coeffSpace
        (U := Response.adaptedDomain hq t)
        (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isOpen
        (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isBoundedDomain
        (Recurrence.toReal_volume_adaptedCell_pos hq t) p r alpha hV hVU hw
  exact hbase.comp (measurable_subSkew g hg)

/-- **The block cell average of the terminal optimizer state on an aligned child
cell is measurable**, in every doubled coordinate. -/
theorem measurable_toFullBlockVec_blockCellAverage_diagonalWeakState_subSkew
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (alpha : BlockCoord d) {V : Set (Vec d)} (hV : MeasurableSet V)
    (hVU : V ⊆ adaptedCell q t) (hVfin : volume V ≠ ⊤) :
    Measurable fun a : CoeffSpace d =>
      toFullBlockVec
        (Response.blockCellAverage V (Response.diagonalWeakState hq t (a.subSkew g hg) p r)) alpha := by
  have hw : MemScalarL2 (adaptedCell q t)
      (Set.indicator V fun _ => (1 : ℝ)) := by
    refine MeasureTheory.memLp_indicator_const (p := (2 : ℝ≥0∞)) (μ := volumeMeasureOn
      (adaptedCell q t)) (s := V) hV (c := (1 : ℝ)) (Or.inr ?_)
    have hle : volumeMeasureOn (adaptedCell q t) V ≤ volume V :=
      MeasureTheory.Measure.restrict_le_self V
    exact ne_top_of_le_ne_top hVfin hle
  have hrw : (fun a : CoeffSpace d =>
      toFullBlockVec
        (Response.blockCellAverage V (Response.diagonalWeakState hq t (a.subSkew g hg) p r)) alpha) =
      fun a : CoeffSpace d =>
        volumeAverage V (fun x =>
          (1 : ℝ) *
            toFullBlockVec (Response.diagonalWeakState hq t (a.subSkew g hg) p r x) alpha) := by
    funext a
    rw [toFullBlockVec_blockCellAverage]
    simp
  rw [hrw]
  exact measurable_volumeAverage_weighted_diagonalWeakState_subSkew hq t g hg p r alpha
    hV hVU hw

/-! ## The observables on an aligned child cell -/

/-- **The measurability half of the per-child block-average observable of the
cutoff split.** -/
theorem aestronglyMeasurable_blockCellAverage_diagonalWeakState_subSkew_alignedIndex
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    (P : Measure (CoeffSpace d)) (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    {w : Fin d → ℤ} (hw : w ∈ Response.alignedIndex q s t) (alpha : BlockCoord d) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      toFullBlockVec (Response.blockCellAverage (adaptedCellAt q s w)
        (Response.diagonalWeakState hq t (a.subSkew g hg) p r)) alpha) P := by
  refine (measurable_toFullBlockVec_blockCellAverage_diagonalWeakState_subSkew hq t g hg p r
    alpha (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).isOpen.measurableSet
    (Response.adaptedCellAt_subset_of_mem_alignedIndex hq hst hw) ?_).aestronglyMeasurable
  exact ne_of_lt (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).volume_lt_top

/-- **The measurability half of the localized cutoff-oscillation observable of
the cutoff split.**  The weight is the oscillation of any fixed profile on the
child cell, extended by zero. -/
theorem aestronglyMeasurable_volumeAverage_weighted_diagonalWeakState_subSkew_alignedIndex
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    (P : Measure (CoeffSpace d)) (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    {w : Fin d → ℤ} (hw : w ∈ Response.alignedIndex q s t) (alpha : BlockCoord d)
    {eta : Vec d → ℝ}
    (heta : MemScalarL2 (adaptedCell q t) (Set.indicator (adaptedCellAt q s w) eta)) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      volumeAverage (adaptedCellAt q s w) (fun x =>
        eta x *
          toFullBlockVec (Response.diagonalWeakState hq t (a.subSkew g hg) p r x) alpha)) P :=
  (measurable_volumeAverage_weighted_diagonalWeakState_subSkew hq t g hg p r alpha
    (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).isOpen.measurableSet
    (Response.adaptedCellAt_subset_of_mem_alignedIndex hq hst hw) heta).aestronglyMeasurable

/-- **The adjoint block cell average of the terminal optimizer state on an
aligned child cell is measurable.** -/
theorem aestronglyMeasurable_blockCellAverage_diagonalWeakAdjointState_subSkew_alignedIndex
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    (P : Measure (CoeffSpace d)) (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    {w : Fin d → ℤ} (hw : w ∈ Response.alignedIndex q s t) (alpha : BlockCoord d) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      toFullBlockVec (Response.blockCellAverage (adaptedCellAt q s w)
        (Response.diagonalWeakAdjointState hq t (a.subSkew g hg) p r)) alpha) P := by
  have hbase : Measurable fun b : CoeffSpace d =>
      toFullBlockVec (Response.blockCellAverage (adaptedCellAt q s w)
        (Response.diagonalWeakState hq t b p r)) alpha := by
    have hw' : MemScalarL2 (adaptedCell q t)
        (Set.indicator (adaptedCellAt q s w) fun _ => (1 : ℝ)) := by
      refine MeasureTheory.memLp_indicator_const (p := (2 : ℝ≥0∞)) (μ := volumeMeasureOn
        (adaptedCell q t)) (s := adaptedCellAt q s w)
        (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).isOpen.measurableSet
        (c := (1 : ℝ)) (Or.inr ?_)
      have hle : volumeMeasureOn (adaptedCell q t) (adaptedCellAt q s w) ≤
          volume (adaptedCellAt q s w) :=
        MeasureTheory.Measure.restrict_le_self (adaptedCellAt q s w)
      exact ne_top_of_le_ne_top
        (ne_of_lt (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).volume_lt_top) hle
    have hrw : (fun b : CoeffSpace d =>
        toFullBlockVec (Response.blockCellAverage (adaptedCellAt q s w)
          (Response.diagonalWeakState hq t b p r)) alpha) =
        fun b : CoeffSpace d =>
          volumeAverage (adaptedCellAt q s w) (fun x =>
            (1 : ℝ) * toFullBlockVec
              (optimizerBlockState (Response.adaptedDomain hq t)
                (b.coeffOn (Response.adaptedDomain hq t)) p r x) alpha) := by
      funext b
      rw [toFullBlockVec_blockCellAverage]
      simp [diagonalWeakState_eq_optimizerBlockState]
    rw [hrw]
    exact measurable_volumeAverage_weighted_optimizerBlockState_coeffSpace
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isOpen
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isBoundedDomain
      (Recurrence.toReal_volume_adaptedCell_pos hq t) p r alpha
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).isOpen.measurableSet
      (Response.adaptedCellAt_subset_of_mem_alignedIndex hq hst hw) hw'
  exact ((hbase.comp measurable_transpose).comp
    (measurable_subSkew g hg)).aestronglyMeasurable

/-- **The adjoint localized oscillation readout of the terminal optimizer state
on an aligned child cell is measurable.** -/
theorem aestronglyMeasurable_volumeAverage_weighted_diagonalWeakAdjointState_subSkew_alignedIndex
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    (P : Measure (CoeffSpace d)) (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    {w : Fin d → ℤ} (hw : w ∈ Response.alignedIndex q s t) (alpha : BlockCoord d)
    {eta : Vec d → ℝ}
    (heta : MemScalarL2 (adaptedCell q t) (Set.indicator (adaptedCellAt q s w) eta)) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      volumeAverage (adaptedCellAt q s w) (fun x =>
        eta x *
          toFullBlockVec (Response.diagonalWeakAdjointState hq t (a.subSkew g hg) p r x)
            alpha)) P := by
  have hbase : Measurable fun b : CoeffSpace d =>
      volumeAverage (adaptedCellAt q s w) (fun x =>
        eta x * toFullBlockVec (Response.diagonalWeakState hq t b p r x) alpha) := by
    simpa only [diagonalWeakState_eq_optimizerBlockState] using
      measurable_volumeAverage_weighted_optimizerBlockState_coeffSpace
        (U := Response.adaptedDomain hq t)
        (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isOpen
        (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isBoundedDomain
        (Recurrence.toReal_volume_adaptedCell_pos hq t) p r alpha
        (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).isOpen.measurableSet
        (Response.adaptedCellAt_subset_of_mem_alignedIndex hq hst hw) heta
  exact ((hbase.comp measurable_transpose).comp
    (measurable_subSkew g hg)).aestronglyMeasurable

end

end Selection
end HighContrast
end HCPolySupport
