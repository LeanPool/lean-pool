/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.OptimizerEnergyMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Response.LocalizedOptimizerObservables
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormRecentState

/-!
# High-contrast homogenization: Provider.Response.RecentDifferenceEnergyMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Sample measurability of the per-cell recent difference energies

The recent difference energy of the weak-norm estimate for the optimizer state
is the doubled energy, on an aligned child cell, of the difference between the
child optimizer state and the terminal optimizer state of the parent cell.  Both
states are aligned pairs
of a gradient and its own flux, so their difference is aligned too and the
doubled operator sends it to its own swap; the energy is therefore the plain
coordinate pairing of the two halves of the difference, with no coefficient
field left in the weight.

That pairing is a continuous quadratic functional of the ambient difference
field, and the difference field is a strongly measurable function of the sample
because each of its inner products against a fixed block state splits into a
child readout and a parent readout localized to the child cell.
-/

namespace HCPolySupport
namespace HighContrast
namespace Selection

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Restriction to a subcell -/

theorem memScalarL2_indicator_subset {V W : Set (Vec d)} (hV : MeasurableSet V)
    (hVW : V ⊆ W) {f : Vec d → ℝ} (hf : MemScalarL2 V f) :
    MemScalarL2 W (Set.indicator V f) := by
  show MeasureTheory.MemLp (Set.indicator V f) 2 (volumeMeasureOn W)
  rw [MeasureTheory.memLp_indicator_iff_restrict hV]
  rwa [volumeMeasureOn, MeasureTheory.Measure.restrict_restrict hV,
    Set.inter_eq_self_of_subset_left hVW]

theorem memBlockL2_subset {V W : Set (Vec d)} (hV : MeasurableSet V) (hVW : V ⊆ W)
    {F : Vec d → BlockVec d} (hF : MemBlockL2 W F) : MemBlockL2 V F := by
  have h := hF.restrict V
  rwa [volumeMeasureOn, MeasureTheory.Measure.restrict_restrict hV,
    Set.inter_eq_self_of_subset_left hVW] at h

/-- A quantitative ellipticity slice of a cell is one of every measurable
subcell. -/
theorem aeeQuantitativeEllipticSlice_subset {V W : Set (Vec d)} (hV : MeasurableSet V)
    (hVW : V ⊆ W) {k : ℕ} {a : CoeffField d}
    (h : AEEQuantitativeEllipticSlice W k a) : AEEQuantitativeEllipticSlice V k a := by
  obtain ⟨-, hmeas, hell⟩ := h
  refine ⟨hV, ?_, ?_⟩
  · intro i j
    have hres := (hmeas i j).restrict (s := V)
    rw [volumeMeasureOn, MeasureTheory.Measure.restrict_restrict hV,
      Set.inter_eq_self_of_subset_left hVW] at hres
    refine hres.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hV] with x hx
    simp [restrictCoeffField, hx, hVW hx]
  · have hres := MeasureTheory.ae_restrict_of_ae (μ := volumeMeasureOn W) (s := V) hell
    rwa [volumeMeasureOn, MeasureTheory.Measure.restrict_restrict hV,
      Set.inter_eq_self_of_subset_left hVW] at hres

/-- A coefficient object restricts to every measurable subcell. -/
@[expose]
def restrictCoeffOn {V W : Book.Ch02.Domain d}
    (hV : MeasurableSet (V : Set (Vec d))) (hVW : (V : Set (Vec d)) ⊆ (W : Set (Vec d)))
    (aW : Book.Ch02.CoeffOn W) : Book.Ch02.CoeffOn V where
  toCoeffField := aW.toCoeffField
  lam := aW.lam
  Lam := aW.Lam
  lam_pos := aW.lam_pos
  lam_le_Lam := aW.lam_le_Lam
  aeStronglyMeasurable := by
    intro i j
    have hres := (aW.aeStronglyMeasurable i j).restrict (s := (V : Set (Vec d)))
    rw [volumeMeasureOn, MeasureTheory.Measure.restrict_restrict hV,
      Set.inter_eq_self_of_subset_left hVW] at hres
    refine hres.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hV] with x hx
    simp [restrictCoeffField, hx, hVW hx]
  aeElliptic := by
    have hres := MeasureTheory.ae_restrict_of_ae (μ := volumeMeasureOn (W : Set (Vec d)))
      (s := (V : Set (Vec d))) aW.aeElliptic
    rwa [volumeMeasureOn, MeasureTheory.Measure.restrict_restrict hV,
      Set.inter_eq_self_of_subset_left hVW] at hres

/-! ## The difference of two optimizer states on the subcell -/

/-- The difference between the optimizer state of a subcell and the optimizer
state of the ambient cell. -/
@[expose]
def optimizerDifferenceState (V W : Book.Ch02.Domain d) (aV : Book.Ch02.CoeffOn V)
    (aW : Book.Ch02.CoeffOn W) (p q : Vec d) : BlockState d where
  potential := fun x =>
    (optimizerBlockState V aV p q x).1 - (optimizerBlockState W aW p q x).1
  flux := fun x =>
    (optimizerBlockState V aV p q x).2 - (optimizerBlockState W aW p q x).2

theorem memBlockL2_optimizerDifferenceState {V W : Book.Ch02.Domain d}
    (hV : MeasurableSet (V : Set (Vec d))) (hVW : (V : Set (Vec d)) ⊆ (W : Set (Vec d)))
    (aV : Book.Ch02.CoeffOn V) (aW : Book.Ch02.CoeffOn W) (p q : Vec d) :
    MemBlockL2 (V : Set (Vec d)) (optimizerDifferenceState V W aV aW p q).eval := by
  have hVstate : MemBlockL2 (V : Set (Vec d)) (optimizerBlockState V aV p q) :=
    memBlockL2_optimizerBlockState aV p q
  have hWstate : MemBlockL2 (V : Set (Vec d)) (optimizerBlockState W aW p q) :=
    memBlockL2_subset hV hVW (memBlockL2_optimizerBlockState aW p q)
  exact MeasureTheory.MemLp.of_fst_snd
    ⟨(MeasureTheory.MemLp.fst hVstate).sub (MeasureTheory.MemLp.fst hWstate),
      (MeasureTheory.MemLp.snd hVstate).sub (MeasureTheory.MemLp.snd hWstate)⟩

/-- The ambient realization of the optimizer difference state. -/
@[expose]
def optimizerDifferenceL2 {V W : Book.Ch02.Domain d}
    (hV : MeasurableSet (V : Set (Vec d))) (hVW : (V : Set (Vec d)) ⊆ (W : Set (Vec d)))
    (aV : Book.Ch02.CoeffOn V) (aW : Book.Ch02.CoeffOn W) (p q : Vec d) :
    HilbertBlockL2 (V : Set (Vec d)) :=
  toHilbertBlockL2OfBlockField (U := (V : Set (Vec d)))
    (memBlockL2_optimizerDifferenceState hV hVW aV aW p q)

theorem coeFn_optimizerDifferenceL2 {V W : Book.Ch02.Domain d}
    (hV : MeasurableSet (V : Set (Vec d))) (hVW : (V : Set (Vec d)) ⊆ (W : Set (Vec d)))
    (aV : Book.Ch02.CoeffOn V) (aW : Book.Ch02.CoeffOn W) (p q : Vec d) :
    (optimizerDifferenceL2 hV hVW aV aW p q : Vec d → HilbertBlockVec d)
      =ᵐ[volumeMeasureOn (V : Set (Vec d))]
      fun x => HilbertBlockVec.ofBlockVec
        ((optimizerDifferenceState V W aV aW p q).eval x) :=
  coeFn_toHilbertBlockL2OfBlockField (U := (V : Set (Vec d)))
    (memBlockL2_optimizerDifferenceState hV hVW aV aW p q)

/-! ## Inner products of the difference against fixed block states -/

theorem inner_optimizerDifferenceL2 {V W : Book.Ch02.Domain d}
    [IsFiniteMeasure (volumeMeasureOn (V : Set (Vec d)))]
    (hV : MeasurableSet (V : Set (Vec d))) (hVW : (V : Set (Vec d)) ⊆ (W : Set (Vec d)))
    (aV : Book.Ch02.CoeffOn V) (aW : Book.Ch02.CoeffOn W) (p q : Vec d)
    {Y : BlockState d} (hY : MemBlockL2 (V : Set (Vec d)) Y.eval) :
    inner ℝ (toHilbertBlockL2OfBlockField (U := (V : Set (Vec d))) hY)
        (optimizerDifferenceL2 hV hVW aV aW p q) =
      ∑ alpha : BlockCoord d,
        ((∫ x in (V : Set (Vec d)), toFullBlockVec (Y.eval x) alpha *
            toFullBlockVec (optimizerBlockState V aV p q x) alpha ∂volume) -
          ∫ x in (W : Set (Vec d)),
            Set.indicator (V : Set (Vec d))
              (fun y => toFullBlockVec (Y.eval y) alpha) x *
              toFullBlockVec (optimizerBlockState W aW p q x) alpha ∂volume) := by
  have hVstate : MemBlockL2 (V : Set (Vec d)) (optimizerBlockState V aV p q) :=
    memBlockL2_optimizerBlockState aV p q
  have hWstate : MemBlockL2 (V : Set (Vec d)) (optimizerBlockState W aW p q) :=
    memBlockL2_subset hV hVW (memBlockL2_optimizerBlockState aW p q)
  have hintV : ∀ alpha : BlockCoord d,
      IntegrableOn (fun x => toFullBlockVec (Y.eval x) alpha *
        toFullBlockVec (optimizerBlockState V aV p q x) alpha) (V : Set (Vec d)) :=
    fun alpha => MeasureTheory.MemLp.integrable_mul
      (memScalarL2_fullBlockCoord_of_memBlockL2 hY alpha)
      (memScalarL2_fullBlockCoord_of_memBlockL2 hVstate alpha)
  have hintW : ∀ alpha : BlockCoord d,
      IntegrableOn (fun x => toFullBlockVec (Y.eval x) alpha *
        toFullBlockVec (optimizerBlockState W aW p q x) alpha) (V : Set (Vec d)) :=
    fun alpha => MeasureTheory.MemLp.integrable_mul
      (memScalarL2_fullBlockCoord_of_memBlockL2 hY alpha)
      (memScalarL2_fullBlockCoord_of_memBlockL2 hWstate alpha)
  calc
    inner ℝ (toHilbertBlockL2OfBlockField (U := (V : Set (Vec d))) hY)
          (optimizerDifferenceL2 hV hVW aV aW p q)
        = ∫ x in (V : Set (Vec d)),
            blockVecDot (Y.eval x) ((optimizerDifferenceState V W aV aW p q).eval x)
              ∂volume :=
          inner_toHilbertBlockL2OfBlockField_eq_integral hY
            (memBlockL2_optimizerDifferenceState hV hVW aV aW p q)
    _ = ∫ x in (V : Set (Vec d)), ∑ alpha : BlockCoord d,
          (toFullBlockVec (Y.eval x) alpha *
              toFullBlockVec (optimizerBlockState V aV p q x) alpha -
            toFullBlockVec (Y.eval x) alpha *
              toFullBlockVec (optimizerBlockState W aW p q x) alpha) ∂volume := by
          refine integral_congr_ae (_root_.Filter.Eventually.of_forall fun x => ?_)
          simp only [blockVecDot_eq_sum_toFullBlockVec]
          refine Finset.sum_congr rfl fun alpha _ => ?_
          cases alpha with
          | inl i => simp [optimizerDifferenceState, toFullBlockVec, BlockState.eval, mul_sub]
          | inr i => simp [optimizerDifferenceState, toFullBlockVec, BlockState.eval, mul_sub]
    _ = ∑ alpha : BlockCoord d, ∫ x in (V : Set (Vec d)),
          (toFullBlockVec (Y.eval x) alpha *
              toFullBlockVec (optimizerBlockState V aV p q x) alpha -
            toFullBlockVec (Y.eval x) alpha *
              toFullBlockVec (optimizerBlockState W aW p q x) alpha) ∂volume :=
          integral_finsetSum _ fun alpha _ => (hintV alpha).sub (hintW alpha)
    _ = ∑ alpha : BlockCoord d,
          ((∫ x in (V : Set (Vec d)), toFullBlockVec (Y.eval x) alpha *
              toFullBlockVec (optimizerBlockState V aV p q x) alpha ∂volume) -
            ∫ x in (W : Set (Vec d)),
              Set.indicator (V : Set (Vec d))
                (fun y => toFullBlockVec (Y.eval y) alpha) x *
                toFullBlockVec (optimizerBlockState W aW p q x) alpha ∂volume) := by
          refine Finset.sum_congr rfl fun alpha _ => ?_
          rw [integral_sub (hintV alpha) (hintW alpha),
            setIntegral_indicator_mul hV hVW]

/-! ## Strong measurability of the ambient difference field -/

/-- **The ambient optimizer difference field is a strongly measurable function
of the sample**, on one quantitative ellipticity slice of the ambient cell. -/
theorem stronglyMeasurable_optimizerDifferenceL2 {Om : Type*} [mOm : MeasurableSpace Om]
    {V W : Book.Ch02.Domain d}
    [IsFiniteMeasure (volumeMeasureOn (V : Set (Vec d)))]
    [IsFiniteMeasure (volumeMeasureOn (W : Set (Vec d)))] {k : ℕ}
    (hVopen : IsOpen (V : Set (Vec d))) (hVfin : volume (V : Set (Vec d)) ≠ ⊤)
    (hVvol : 0 < (volume (V : Set (Vec d))).toReal)
    (hWopen : IsOpen (W : Set (Vec d))) (hWfin : volume (W : Set (Vec d)) ≠ ⊤)
    (hWvol : 0 < (volume (W : Set (Vec d))).toReal)
    (hV : MeasurableSet (V : Set (Vec d))) (hVW : (V : Set (Vec d)) ⊆ (W : Set (Vec d)))
    {A : Om → RegCoeffField d}
    (hSliceW : ∀ w : Om, AEEQuantitativeEllipticSlice (W : Set (Vec d)) k (A w).toFun)
    (hEntryW : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ (W : Set (Vec d)) →
      Measurable fun w => entryTestR i j φ (A w))
    (aV : Om → Book.Ch02.CoeffOn V) (aW : Om → Book.Ch02.CoeffOn W)
    (haV : ∀ w : Om, (aV w).toCoeffField = (A w).toFun)
    (haW : ∀ w : Om, (aW w).toCoeffField = (A w).toFun)
    (p q : Vec d) :
    StronglyMeasurable fun w : Om => optimizerDifferenceL2 hV hVW (aV w) (aW w) p q := by
  classical
  have : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  let : MeasurableSpace (HilbertBlockL2 (V : Set (Vec d))) := borel _
  have : BorelSpace (HilbertBlockL2 (V : Set (Vec d))) := ⟨rfl⟩
  have hSliceV : ∀ w : Om,
      AEEQuantitativeEllipticSlice (V : Set (Vec d)) k (A w).toFun := fun w =>
    aeeQuantitativeEllipticSlice_subset hV hVW (hSliceW w)
  have hEntryV : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ (V : Set (Vec d)) →
      Measurable fun w => entryTestR i j φ (A w) := by
    intro i j φ hcont hcpt hsupp
    exact hEntryW i j hcont hcpt (hsupp.trans hVW)
  obtain ⟨u, hu, hrep⟩ :
      ∃ u : ℕ → HilbertBlockL2 (V : Set (Vec d)), DenseRange u ∧
        ∀ n : ℕ, ∃ (Y : BlockState d) (hY : MemBlockL2 (V : Set (Vec d)) Y.eval),
          u n = toHilbertBlockL2OfBlockField (U := (V : Set (Vec d))) hY := by
    refine ⟨TopologicalSpace.denseSeq _, TopologicalSpace.denseRange_denseSeq _, fun n => ?_⟩
    obtain ⟨Y, hY, hEq⟩ :=
      exists_blockState_toHilbertBlockL2 (TopologicalSpace.denseSeq
        (HilbertBlockL2 (V : Set (Vec d))) n)
    exact ⟨Y, hY, hEq.symm⟩
  have hmeas : Measurable fun w : Om => optimizerDifferenceL2 hV hVW (aV w) (aW w) p q := by
    refine measurable_of_measurable_inner_denseRange_polish u hu fun n => ?_
    obtain ⟨Y, hY, hEq⟩ := hrep n
    simp only [hEq]
    have hrw : (fun w : Om =>
        inner ℝ (toHilbertBlockL2OfBlockField (U := (V : Set (Vec d))) hY)
          (optimizerDifferenceL2 hV hVW (aV w) (aW w) p q)) =
        fun w : Om => ∑ alpha : BlockCoord d,
          ((∫ x in (V : Set (Vec d)), toFullBlockVec (Y.eval x) alpha *
              toFullBlockVec (optimizerBlockState V (aV w) p q x) alpha ∂volume) -
            ∫ x in (W : Set (Vec d)),
              Set.indicator (V : Set (Vec d))
                (fun y => toFullBlockVec (Y.eval y) alpha) x *
                toFullBlockVec (optimizerBlockState W (aW w) p q x) alpha ∂volume) := by
      funext w
      exact inner_optimizerDifferenceL2 hV hVW (aV w) (aW w) p q hY
    rw [hrw]
    refine Finset.measurable_sum _ fun alpha _ => Measurable.sub ?_ ?_
    · exact measurable_integral_weighted_optimizerBlockState hVopen hVfin hVvol hSliceV
        hEntryV aV haV p q alpha (memScalarL2_fullBlockCoord_of_memBlockL2 hY alpha)
    · exact measurable_integral_weighted_optimizerBlockState hWopen hWfin hWvol hSliceW
        hEntryW aW haW p q alpha
        (memScalarL2_indicator_subset hV hVW
          (memScalarL2_fullBlockCoord_of_memBlockL2 hY alpha))
  exact hmeas.stronglyMeasurable

/-! ## The difference energy is a coordinate pairing -/

/-- The recent difference energy of the two optimizer states. -/
@[expose]
def recentDifferenceEnergy (V W : Book.Ch02.Domain d) (aV : Book.Ch02.CoeffOn V)
    (aW : Book.Ch02.CoeffOn W) (p q : Vec d) : ℝ :=
  (1 / 2 : ℝ) * Book.Ch02.average V fun x =>
    blockVecDot ((optimizerDifferenceState V W aV aW p q).eval x)
      (blockMatVecMul (blockMatrixOfCoeff (aV.toCoeffField x))
        ((optimizerDifferenceState V W aV aW p q).eval x))

/-- **The recent difference energy is the plain coordinate pairing of the two
halves of the difference field.**  The difference of two aligned states is
aligned, so the doubled operator returns its own swap. -/
theorem recentDifferenceEnergy_eq {V W : Book.Ch02.Domain d}
    [IsFiniteMeasure (volumeMeasureOn (V : Set (Vec d)))]
    (hV : MeasurableSet (V : Set (Vec d))) (hVW : (V : Set (Vec d)) ⊆ (W : Set (Vec d)))
    (aV : Book.Ch02.CoeffOn V) (aW : Book.Ch02.CoeffOn W)
    (hfield : aV.toCoeffField = aW.toCoeffField) (p q : Vec d) :
    recentDifferenceEnergy V W aV aW p q =
      (volume (V : Set (Vec d))).toReal⁻¹ *
        ∑ i : Fin d, inner ℝ
          (weightedCoordOperator (U := (V : Set (Vec d))) (measurable_const (a := (1 : ℝ)))
            zero_le_one (fun _ => by norm_num) (Sum.inl i) (Sum.inr i)
            (optimizerDifferenceL2 hV hVW aV aW p q))
          (optimizerDifferenceL2 hV hVW aV aW p q) := by
  have hDmem : MemBlockL2 (V : Set (Vec d))
      (optimizerDifferenceState V W aV aW p q).eval :=
    memBlockL2_optimizerDifferenceState hV hVW aV aW p q
  have haligned : ∀ x : Vec d,
      (optimizerDifferenceState V W aV aW p q).eval x =
        ((optimizerDifferenceState V W aV aW p q).potential x,
          matVecMul (aV.toCoeffField x)
            ((optimizerDifferenceState V W aV aW p q).potential x)) := by
    intro x
    have hsnd : (optimizerDifferenceState V W aV aW p q).flux x =
        matVecMul (aV.toCoeffField x)
          ((optimizerDifferenceState V W aV aW p q).potential x) := by
      show (optimizerBlockState V aV p q x).2 - (optimizerBlockState W aW p q x).2 = _
      rw [optimizerBlockState_snd, optimizerBlockState_snd, ← hfield]
      show matVecMul (aV.toCoeffField x) _ - matVecMul (aV.toCoeffField x) _ =
        matVecMul (aV.toCoeffField x) _
      funext i
      simp [matVecMul, optimizerDifferenceState, mul_sub, Finset.sum_sub_distrib]
    show ((optimizerDifferenceState V W aV aW p q).potential x,
      (optimizerDifferenceState V W aV aW p q).flux x) = _
    rw [hsnd]
  have hpt : ∀ᵐ x ∂volumeMeasureOn (V : Set (Vec d)),
      blockVecDot ((optimizerDifferenceState V W aV aW p q).eval x)
          (blockMatVecMul (blockMatrixOfCoeff (aV.toCoeffField x))
            ((optimizerDifferenceState V W aV aW p q).eval x)) =
        2 * ∑ i : Fin d,
          toFullBlockVec ((optimizerDifferenceState V W aV aW p q).eval x) (Sum.inl i) *
            toFullBlockVec ((optimizerDifferenceState V W aV aW p q).eval x)
              (Sum.inr i) := by
    filter_upwards [aV.aeElliptic] with x hx
    rw [haligned x, blockMatVecMul_blockMatrixOfCoeff_primal_of_isEllipticMatrix hx]
    simp only [blockVecDot, toFullBlockVec, Finset.mul_sum]
    rw [vecDot_comm (matVecMul (aV.toCoeffField x)
      ((optimizerDifferenceState V W aV aW p q).potential x))]
    simp only [vecDot]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcoord : ∀ i : Fin d,
      inner ℝ (weightedCoordOperator (U := (V : Set (Vec d))) (measurable_const (a := (1 : ℝ)))
          zero_le_one (fun _ => by norm_num) (Sum.inl i) (Sum.inr i)
          (optimizerDifferenceL2 hV hVW aV aW p q))
        (optimizerDifferenceL2 hV hVW aV aW p q) =
        ∫ x in (V : Set (Vec d)),
          toFullBlockVec ((optimizerDifferenceState V W aV aW p q).eval x) (Sum.inl i) *
            toFullBlockVec ((optimizerDifferenceState V W aV aW p q).eval x)
              (Sum.inr i) ∂volume := by
    intro i
    rw [inner_weightedCoordOperator]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_optimizerDifferenceL2 hV hVW aV aW p q] with x hx
    rw [hx]
    simp
  have hint : ∀ i : Fin d,
      IntegrableOn (fun x =>
        toFullBlockVec ((optimizerDifferenceState V W aV aW p q).eval x) (Sum.inl i) *
          toFullBlockVec ((optimizerDifferenceState V W aV aW p q).eval x) (Sum.inr i))
        (V : Set (Vec d)) := fun i =>
    MeasureTheory.MemLp.integrable_mul
      (memScalarL2_fullBlockCoord_of_memBlockL2 hDmem (Sum.inl i))
      (memScalarL2_fullBlockCoord_of_memBlockL2 hDmem (Sum.inr i))
  rw [recentDifferenceEnergy, Book.Ch02.average]
  have hsum : (∑ i : Fin d, inner ℝ
      (weightedCoordOperator (U := (V : Set (Vec d))) (measurable_const (a := (1 : ℝ)))
        zero_le_one (fun _ => by norm_num) (Sum.inl i) (Sum.inr i)
        (optimizerDifferenceL2 hV hVW aV aW p q))
      (optimizerDifferenceL2 hV hVW aV aW p q)) =
      ∫ x in (V : Set (Vec d)), ∑ i : Fin d,
        toFullBlockVec ((optimizerDifferenceState V W aV aW p q).eval x) (Sum.inl i) *
          toFullBlockVec ((optimizerDifferenceState V W aV aW p q).eval x)
            (Sum.inr i) ∂volume := by
    rw [integral_finsetSum _ fun i _ => hint i]
    exact Finset.sum_congr rfl fun i _ => hcoord i
  have hI : (∫ x in (V : Set (Vec d)),
      blockVecDot ((optimizerDifferenceState V W aV aW p q).eval x)
        (blockMatVecMul (blockMatrixOfCoeff (aV.toCoeffField x))
          ((optimizerDifferenceState V W aV aW p q).eval x)) ∂volume) =
      2 * ∫ x in (V : Set (Vec d)), ∑ i : Fin d,
        toFullBlockVec ((optimizerDifferenceState V W aV aW p q).eval x) (Sum.inl i) *
          toFullBlockVec ((optimizerDifferenceState V W aV aW p q).eval x)
            (Sum.inr i) ∂volume := by
    rw [← integral_const_mul]
    exact integral_congr_ae hpt
  rw [hsum, hI]
  ring

/-! ## The difference energy on the coefficient space -/

theorem ae_of_subset {V W : Set (Vec d)} (hV : MeasurableSet V) (hVW : V ⊆ W)
    {Pr : Vec d → Prop} (h : ∀ᵐ x ∂volumeMeasureOn W, Pr x) :
    ∀ᵐ x ∂volumeMeasureOn V, Pr x := by
  have hres := MeasureTheory.ae_restrict_of_ae (μ := volumeMeasureOn W) (s := V) h
  rwa [volumeMeasureOn, MeasureTheory.Measure.restrict_restrict hV,
    Set.inter_eq_self_of_subset_left hVW] at hres

theorem optimizerBlockState_ae_congr {U : Book.Ch02.Domain d}
    {aU bU : Book.Ch02.CoeffOn U} (h : Book.Ch02.CoeffOn.AEEq aU bU) (p q : Vec d) :
    (fun x => optimizerBlockState U aU p q x) =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => optimizerBlockState U bU p q x := by
  have hgrad := Book.Ch02.canonicalMaximizer_sameGradientAE_ofAEEq h p q
  filter_upwards [hgrad, h] with x hx hax
  have hx' :
      (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U aU) p
        q).toSolution.toH1.grad x =
      (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U bU) p
        q).toSolution.toH1.grad x := hx
  simp only [optimizerBlockState, hx', hax]

theorem recentDifferenceEnergy_congr {V W : Book.Ch02.Domain d}
    (hV : MeasurableSet (V : Set (Vec d))) (hVW : (V : Set (Vec d)) ⊆ (W : Set (Vec d)))
    {aV bV : Book.Ch02.CoeffOn V} {aW bW : Book.Ch02.CoeffOn W}
    (hVeq : Book.Ch02.CoeffOn.AEEq aV bV) (hWeq : Book.Ch02.CoeffOn.AEEq aW bW)
    (p q : Vec d) :
    recentDifferenceEnergy V W aV aW p q = recentDifferenceEnergy V W bV bW p q := by
  rw [recentDifferenceEnergy, recentDifferenceEnergy, Book.Ch02.average, Book.Ch02.average]
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [optimizerBlockState_ae_congr hVeq p q,
    ae_of_subset hV hVW (optimizerBlockState_ae_congr hWeq p q), hVeq] with x h1 h2 h3
  simp only [optimizerDifferenceState, BlockState.eval, h1, h2, h3]

/-- The coordinate pairing functional is continuous. -/
theorem continuous_coordPairingFunctional {V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn V)] {eta : Vec d → ℝ} (hmeas : Measurable eta)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |eta x| ≤ C) :
    Continuous fun z : HilbertBlockL2 V =>
      (volume V).toReal⁻¹ * ∑ i : Fin d,
        inner ℝ (weightedCoordOperator (U := V) hmeas hC hbound (Sum.inl i) (Sum.inr i) z)
          z := by
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
  exact continuous_inner.comp
    (((weightedCoordOperator (U := V) hmeas hC hbound (Sum.inl i)
      (Sum.inr i)).continuous).prodMk continuous_id)

/-- **The recent difference energy is measurable on one ellipticity slice.** -/
theorem measurable_recentDifferenceEnergy_slice {Om : Type*} [mOm : MeasurableSpace Om]
    {V W : Book.Ch02.Domain d}
    [IsFiniteMeasure (volumeMeasureOn (V : Set (Vec d)))]
    [IsFiniteMeasure (volumeMeasureOn (W : Set (Vec d)))] {k : ℕ}
    (hVopen : IsOpen (V : Set (Vec d))) (hVfin : volume (V : Set (Vec d)) ≠ ⊤)
    (hVvol : 0 < (volume (V : Set (Vec d))).toReal)
    (hWopen : IsOpen (W : Set (Vec d))) (hWfin : volume (W : Set (Vec d)) ≠ ⊤)
    (hWvol : 0 < (volume (W : Set (Vec d))).toReal)
    (hV : MeasurableSet (V : Set (Vec d))) (hVW : (V : Set (Vec d)) ⊆ (W : Set (Vec d)))
    {A : Om → RegCoeffField d}
    (hSliceW : ∀ w : Om, AEEQuantitativeEllipticSlice (W : Set (Vec d)) k (A w).toFun)
    (hEntryW : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ (W : Set (Vec d)) →
      Measurable fun w => entryTestR i j φ (A w))
    (aW : Om → Book.Ch02.CoeffOn W)
    (haW : ∀ w : Om, (aW w).toCoeffField = (A w).toFun)
    (p q : Vec d) :
    Measurable fun w : Om =>
      recentDifferenceEnergy V W (restrictCoeffOn hV hVW (aW w)) (aW w) p q := by
  have hdiff := stronglyMeasurable_optimizerDifferenceL2 hVopen hVfin hVvol hWopen hWfin
    hWvol hV hVW hSliceW hEntryW (fun w => restrictCoeffOn hV hVW (aW w)) aW
    (fun w => haW w) haW p q
  have hrw : (fun w : Om =>
      recentDifferenceEnergy V W (restrictCoeffOn hV hVW (aW w)) (aW w) p q) =
      fun w : Om =>
        (volume (V : Set (Vec d))).toReal⁻¹ * ∑ i : Fin d,
          inner ℝ
            (weightedCoordOperator (U := (V : Set (Vec d)))
              (measurable_const (a := (1 : ℝ))) zero_le_one (fun _ => by norm_num)
              (Sum.inl i) (Sum.inr i)
              (optimizerDifferenceL2 hV hVW (restrictCoeffOn hV hVW (aW w)) (aW w) p q))
            (optimizerDifferenceL2 hV hVW (restrictCoeffOn hV hVW (aW w)) (aW w) p q) := by
    funext w
    exact recentDifferenceEnergy_eq hV hVW (restrictCoeffOn hV hVW (aW w)) (aW w) rfl p q
  rw [hrw]
  exact ((continuous_coordPairingFunctional (V := (V : Set (Vec d)))
    (measurable_const (a := (1 : ℝ))) zero_le_one
    (fun _ => by norm_num)).comp_stronglyMeasurable hdiff).measurable

/-- **The recent difference energy is measurable on the coefficient space.** -/
theorem measurable_recentDifferenceEnergy_coeffSpace {V W : Book.Ch02.Domain d}
    (hVopen : IsOpen (V : Set (Vec d))) (hVbdd : IsBoundedDomain (V : Set (Vec d)))
    (hVvol : 0 < (volume (V : Set (Vec d))).toReal)
    (hWopen : IsOpen (W : Set (Vec d))) (hWbdd : IsBoundedDomain (W : Set (Vec d)))
    (hWvol : 0 < (volume (W : Set (Vec d))).toReal)
    (hVW : (V : Set (Vec d)) ⊆ (W : Set (Vec d))) (p q : Vec d) :
    Measurable fun a : CoeffSpace d =>
      recentDifferenceEnergy V W (a.coeffOn V) (a.coeffOn W) p q := by
  have : IsFiniteMeasure (volumeMeasureOn (V : Set (Vec d))) :=
    hVbdd.isFiniteMeasure_restrict_volume
  have : IsFiniteMeasure (volumeMeasureOn (W : Set (Vec d))) :=
    hWbdd.isFiniteMeasure_restrict_volume
  have hV : MeasurableSet (V : Set (Vec d)) := hVopen.measurableSet
  have hbase : Measurable fun a : CoeffSpace d =>
      recentDifferenceEnergy V W (restrictCoeffOn hV hVW (a.coeffOn W)) (a.coeffOn W) p q := by
    refine measurable_coeffSpace_of_slicewise hWopen hWbdd
      (fun aW => recentDifferenceEnergy V W (restrictCoeffOn hV hVW aW) aW p q) ?_ ?_
    · intro aW bW h
      exact recentDifferenceEnergy_congr (aV := restrictCoeffOn hV hVW aW)
        (bV := restrictCoeffOn hV hVW bW) hV hVW
        (ae_of_subset (Pr := fun x => aW.toCoeffField x = bW.toCoeffField x) hV hVW h) h p q
    · intro k Om mOm A hSliceW hEntryW aW haW
      exact measurable_recentDifferenceEnergy_slice hVopen
        (ne_of_lt hVbdd.volume_lt_top) hVvol hWopen (ne_of_lt hWbdd.volume_lt_top) hWvol
        hV hVW hSliceW hEntryW aW haW p q
  have hrw : (fun a : CoeffSpace d =>
      recentDifferenceEnergy V W (a.coeffOn V) (a.coeffOn W) p q) =
      fun a : CoeffSpace d =>
        recentDifferenceEnergy V W (restrictCoeffOn hV hVW (a.coeffOn W)) (a.coeffOn W) p q := by
    funext a
    exact recentDifferenceEnergy_congr hV hVW _root_.Filter.EventuallyEq.rfl
      _root_.Filter.EventuallyEq.rfl p q
  rw [hrw]
  exact hbase

/-! ## The recent difference energy of an aligned child cell -/

/-- **The measurability half of the per-cell recent difference energy binder**,
in the shape the profile estimate consumes. -/
theorem aestronglyMeasurable_recentDifferenceEnergy_alignedIndex [NeZero d] {q : Mat d}
    (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t) (P : Measure (CoeffSpace d)) (g : Mat d)
    (hg : IsSkewMat g) (p r : Vec d) {w : Fin d → ℤ}
    (hw : w ∈ Response.alignedIndex q s t) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      (1 / 2 : ℝ) * Book.Ch02.average (Response.adaptedDomainAt hq s w) (fun x =>
        blockVecDot
          (Response.diagonalWeakChildState hq s w (a.subSkew g hg) p r x -
            Response.diagonalWeakState hq t (a.subSkew g hg) p r x)
          (blockMatVecMul (blockMatrixOfCoeff ((⇑(a.subSkew g hg).1 : CoeffField d) x))
            (Response.diagonalWeakChildState hq s w (a.subSkew g hg) p r x -
              Response.diagonalWeakState hq t (a.subSkew g hg) p r x)))) P := by
  have hVvol : 0 < (volume (adaptedCellAt q s w)).toReal :=
    ENNReal.toReal_pos (Recurrence.volume_adaptedCellAt_pos hq s w).ne'
      (ne_of_lt (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).volume_lt_top)
  have hbase : Measurable fun b : CoeffSpace d =>
      recentDifferenceEnergy (Response.adaptedDomainAt hq s w) (Response.adaptedDomain hq t)
        (b.coeffOn (Response.adaptedDomainAt hq s w)) (b.coeffOn (Response.adaptedDomain hq t)) p r :=
    measurable_recentDifferenceEnergy_coeffSpace
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).isOpen
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).isBoundedDomain hVvol
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isOpen
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isBoundedDomain
      (Recurrence.toReal_volume_adaptedCell_pos hq t)
      (Response.adaptedCellAt_subset_of_mem_alignedIndex hq hst hw) p r
  exact (hbase.comp (measurable_subSkew g hg)).aestronglyMeasurable

/-- **The measurability half of the adjoint per-cell recent difference energy
binder**, in the shape the transposed profile estimate consumes. -/
theorem aestronglyMeasurable_adjointRecentDifferenceEnergy_alignedIndex [NeZero d]
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t) (P : Measure (CoeffSpace d))
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) {w : Fin d → ℤ}
    (hw : w ∈ Response.alignedIndex q s t) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      (1 / 2 : ℝ) * Book.Ch02.average (Response.adaptedDomainAt hq s w) (fun x =>
        blockVecDot
          (Response.diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r x -
            Response.diagonalWeakState hq t (a.subSkew g hg).transpose p r x)
          (blockMatVecMul (blockMatrixOfCoeff
              ((⇑(a.subSkew g hg).transpose.1 : CoeffField d) x))
            (Response.diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r x -
              Response.diagonalWeakState hq t (a.subSkew g hg).transpose p r x)))) P := by
  have hVvol : 0 < (volume (adaptedCellAt q s w)).toReal :=
    ENNReal.toReal_pos (Recurrence.volume_adaptedCellAt_pos hq s w).ne'
      (ne_of_lt (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).volume_lt_top)
  have hbase : Measurable fun b : CoeffSpace d =>
      recentDifferenceEnergy (Response.adaptedDomainAt hq s w) (Response.adaptedDomain hq t)
        (b.coeffOn (Response.adaptedDomainAt hq s w)) (b.coeffOn (Response.adaptedDomain hq t)) p r :=
    measurable_recentDifferenceEnergy_coeffSpace
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).isOpen
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s w).isBoundedDomain hVvol
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isOpen
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t).isBoundedDomain
      (Recurrence.toReal_volume_adaptedCell_pos hq t)
      (Response.adaptedCellAt_subset_of_mem_alignedIndex hq hst hw) p r
  exact (((hbase.comp measurable_transpose).comp
    (measurable_subSkew g hg))).aestronglyMeasurable

end

end Selection
end HighContrast
end HCPolySupport
