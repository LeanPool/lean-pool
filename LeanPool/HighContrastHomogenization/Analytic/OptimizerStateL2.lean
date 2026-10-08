/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.WeightedBlockCoordOperator
public import LeanPool.HighContrastHomogenization.Analytic.OptimizerGradientReadout
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.SolutionIntegrability

/-!
# High-contrast homogenization: Analytic.OptimizerStateL2

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The doubled optimizer state as an ambient `L²` field

The doubled state of the response optimizer is square integrable on its cell:
the gradient because the optimizer is a Sobolev function, the flux because the
coefficient object is essentially bounded.  This file realizes it as an element
of the ambient block `L²` space and shows that this element is a strongly
measurable function of the sample.

Measurability is obtained from the weighted coordinate readouts already
available: the ambient inner product against a fixed block test state is a
finite sum of such readouts, every ambient element is the image of a block
state, and a map into a separable Hilbert space is measurable once its inner
products against a dense family are.  Localized quadratic observables of the
optimizer state then become continuous functionals of a measurable field.
-/

namespace HCPolySupport
namespace HighContrast
namespace Selection

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Doubled pairing as a coordinate sum -/

theorem blockVecDot_eq_sum_toFullBlockVec (X Y : BlockVec d) :
    blockVecDot X Y = ∑ alpha : BlockCoord d, toFullBlockVec X alpha * toFullBlockVec Y alpha := by
  simp [blockVecDot, vecDot, toFullBlockVec, Fintype.sum_sum_type]

/-! ## Every ambient block field comes from a block state -/

/-- Every element of the ambient block `L²` space is the image of a block
state. -/
theorem exists_blockState_toHilbertBlockL2 {U : Set (Vec d)} (f : HilbertBlockL2 U) :
    ∃ (Y : BlockState d) (hY : MemBlockL2 U Y.eval),
      toHilbertBlockL2OfBlockField (U := U) hY = f := by
  classical
  set F : Vec d → BlockVec d :=
    fun x => ((f : Vec d → HilbertBlockVec d) x).toBlockVec with hF
  have hFmem : MemBlockL2 U F := by
    have hcomp :=
      ((HilbertBlockVec.continuousLinearEquivBlockVec
        d).toContinuousLinearMap.lipschitzWith).comp_memLp
        (by simp) (MeasureTheory.Lp.memLp f)
    simpa [hF, Function.comp_def] using hcomp
  refine ⟨⟨fun x => (F x).1, fun x => (F x).2⟩, ?_, ?_⟩
  · exact hFmem
  · refine MeasureTheory.Lp.ext ?_
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField (U := U) (F := F) hFmem] with x hx
    exact hx.trans (by simp [hilbertifyBlockField, hF])

/-! ## The optimizer state is square integrable -/

theorem memBlockL2_optimizerBlockState {U : Book.Ch02.Domain d}
    (aU : Book.Ch02.CoeffOn U) (p q : Vec d) :
    MemBlockL2 (U : Set (Vec d)) (optimizerBlockState U aU p q) :=
  MeasureTheory.MemLp.of_fst_snd
    ⟨(Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U aU) p
        q).toSolution.toH1.grad_memVectorL2,
      Book.Ch02.Solution.flux_memVectorL2
        (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U aU) p q).toSolution⟩

/-- The doubled optimizer state as an element of the ambient block `L²`
space. -/
@[expose]
def optimizerStateL2 (U : Book.Ch02.Domain d) (aU : Book.Ch02.CoeffOn U)
    (p q : Vec d) : HilbertBlockL2 (U : Set (Vec d)) :=
  toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
    (memBlockL2_optimizerBlockState aU p q)

theorem coeFn_optimizerStateL2 (U : Book.Ch02.Domain d) (aU : Book.Ch02.CoeffOn U)
    (p q : Vec d) :
    (optimizerStateL2 U aU p q : Vec d → HilbertBlockVec d)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => HilbertBlockVec.ofBlockVec (optimizerBlockState U aU p q x) :=
  coeFn_toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
    (memBlockL2_optimizerBlockState aU p q)

/-! ## The inner product against a fixed block state -/

theorem inner_optimizerStateL2 {U : Book.Ch02.Domain d}
    (aU : Book.Ch02.CoeffOn U) (p q : Vec d) {Y : BlockState d}
    (hY : MemBlockL2 (U : Set (Vec d)) Y.eval) :
    inner ℝ (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hY)
        (optimizerStateL2 U aU p q) =
      ∑ alpha : BlockCoord d, ∫ x in (U : Set (Vec d)),
        toFullBlockVec (Y.eval x) alpha *
          toFullBlockVec (optimizerBlockState U aU p q x) alpha ∂volume := by
  have hint : ∀ alpha : BlockCoord d,
      IntegrableOn (fun x => toFullBlockVec (Y.eval x) alpha *
        toFullBlockVec (optimizerBlockState U aU p q x) alpha) (U : Set (Vec d)) := by
    intro alpha
    exact MeasureTheory.MemLp.integrable_mul
      (memScalarL2_fullBlockCoord_of_memBlockL2 hY alpha)
      (memScalarL2_fullBlockCoord_of_memBlockL2
        (memBlockL2_optimizerBlockState aU p q) alpha)
  calc
    inner ℝ (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hY)
          (optimizerStateL2 U aU p q)
        = ∫ x in (U : Set (Vec d)),
            blockVecDot (Y.eval x) (optimizerBlockState U aU p q x) ∂volume :=
          inner_toHilbertBlockL2OfBlockField_eq_integral hY
            (memBlockL2_optimizerBlockState aU p q)
    _ = ∫ x in (U : Set (Vec d)), ∑ alpha : BlockCoord d,
          toFullBlockVec (Y.eval x) alpha *
            toFullBlockVec (optimizerBlockState U aU p q x) alpha ∂volume := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          exact blockVecDot_eq_sum_toFullBlockVec _ _
    _ = ∑ alpha : BlockCoord d, ∫ x in (U : Set (Vec d)),
          toFullBlockVec (Y.eval x) alpha *
            toFullBlockVec (optimizerBlockState U aU p q x) alpha ∂volume :=
          integral_finsetSum _ fun alpha _ => hint alpha

/-! ## Strong measurability of the ambient optimizer state -/

/-- **The ambient doubled optimizer state is a strongly measurable function of
the sample**, on one quantitative ellipticity slice of the cell. -/
theorem stronglyMeasurable_optimizerStateL2 {Om : Type*} [mOm : MeasurableSpace Om]
    {U : Book.Ch02.Domain d} [IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))]
    {k : ℕ} (hUopen : IsOpen (U : Set (Vec d))) (hUfin : volume (U : Set (Vec d)) ≠ ⊤)
    (hvol : 0 < (volume (U : Set (Vec d))).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice (U : Set (Vec d)) k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ (U : Set (Vec d)) →
      Measurable fun w => entryTestR i j φ (A w))
    (aU : Om → Book.Ch02.CoeffOn U)
    (haU : ∀ w : Om, (aU w).toCoeffField = (A w).toFun)
    (p q : Vec d) :
    StronglyMeasurable fun w : Om => optimizerStateL2 U (aU w) p q := by
  classical
  have : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  let : MeasurableSpace (HilbertBlockL2 (U : Set (Vec d))) := borel _
  have : BorelSpace (HilbertBlockL2 (U : Set (Vec d))) := ⟨rfl⟩
  obtain ⟨u, hu, hrep⟩ :
      ∃ u : ℕ → HilbertBlockL2 (U : Set (Vec d)), DenseRange u ∧
        ∀ n : ℕ, ∃ (Y : BlockState d) (hY : MemBlockL2 (U : Set (Vec d)) Y.eval),
          u n = toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hY := by
    refine ⟨TopologicalSpace.denseSeq _, TopologicalSpace.denseRange_denseSeq _, fun n => ?_⟩
    obtain ⟨Y, hY, hEq⟩ :=
      exists_blockState_toHilbertBlockL2 (TopologicalSpace.denseSeq
        (HilbertBlockL2 (U : Set (Vec d))) n)
    exact ⟨Y, hY, hEq.symm⟩
  have hmeas : Measurable fun w : Om => optimizerStateL2 U (aU w) p q := by
    refine measurable_of_measurable_inner_denseRange_polish u hu fun n => ?_
    obtain ⟨Y, hY, hEq⟩ := hrep n
    simp only [hEq]
    have hrw : (fun w : Om =>
        inner ℝ (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hY)
          (optimizerStateL2 U (aU w) p q)) =
        fun w : Om => ∑ alpha : BlockCoord d, ∫ x in (U : Set (Vec d)),
          toFullBlockVec (Y.eval x) alpha *
            toFullBlockVec (optimizerBlockState U (aU w) p q x) alpha ∂volume := by
      funext w
      exact inner_optimizerStateL2 (aU w) p q hY
    rw [hrw]
    refine Finset.measurable_sum _ fun alpha _ => ?_
    exact measurable_integral_weighted_optimizerBlockState hUopen hUfin hvol hSlice hEntry
      aU haU p q alpha (memScalarL2_fullBlockCoord_of_memBlockL2 hY alpha)
  exact hmeas.stronglyMeasurable

end

end Selection
end HighContrast
end HCPolySupport
