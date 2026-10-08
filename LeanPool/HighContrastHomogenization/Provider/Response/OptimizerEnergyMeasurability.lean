/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.OptimizerStateL2
public import LeanPool.HighContrastHomogenization.Provider.Response.OptimizerReadoutMeasurability

/-!
# High-contrast homogenization: Provider.Response.OptimizerEnergyMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Sample measurability of localized optimizer energies

A localized energy of the response optimizer is the average of a bounded weight
against the quadratic form of the coefficient field on the optimizer gradient.
It is a continuous quadratic functional of the ambient doubled optimizer state,
hence a measurable function of the sample.

The passage from one quantitative ellipticity slice of the cell to the whole
coefficient space is isolated here as a reusable rule: a real observable of the
coefficient object that sees only its almost everywhere class and is measurable
on each slice is measurable on the coefficient space.
-/

namespace HCPolySupport
namespace HighContrast
namespace Selection

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## From the ellipticity slices to the coefficient space -/

/-- **The slice-gluing rule.**  An observable of the coefficient object that
depends only on its almost everywhere class and is measurable over every
parameter family lying in a single quantitative ellipticity slice is measurable
on the coefficient space. -/
theorem measurable_coeffSpace_of_slicewise {U : Book.Ch02.Domain d}
    (hUopen : IsOpen (U : Set (Vec d))) (hUbdd : IsBoundedDomain (U : Set (Vec d)))
    (R : Book.Ch02.CoeffOn U → ℝ)
    (hcongr : ∀ aU bU : Book.Ch02.CoeffOn U, Book.Ch02.CoeffOn.AEEq aU bU → R aU = R bU)
    (hslice : ∀ (k : ℕ) (Om : Type) (mOm : MeasurableSpace Om) (A : Om → RegCoeffField d),
      (∀ w : Om, AEEQuantitativeEllipticSlice (U : Set (Vec d)) k (A w).toFun) →
      (∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ (U : Set (Vec d)) → Measurable fun w => entryTestR i j φ (A w)) →
      ∀ aU : Om → Book.Ch02.CoeffOn U, (∀ w : Om, (aU w).toCoeffField = (A w).toFun) →
        @Measurable Om ℝ mOm _ fun w => R (aU w)) :
    Measurable fun a : CoeffSpace d => R (a.coeffOn U) := by
  classical
  have hlocal : @Measurable (Source.Coarse.Carrier d) ℝ
      (Source.Coarse.localSigma (U : Set (Vec d)) hUopen.measurableSet) _
      (fun b => R (sourceCoeffOn U hUbdd b)) := by
    let : MeasurableSpace (Source.Coarse.Carrier d) :=
      Source.Coarse.localSigma (U : Set (Vec d)) hUopen.measurableSet
    set slice : ℕ → Set (Source.Coarse.Carrier d) :=
      fun k => {b | AEEQuantitativeEllipticSlice (U : Set (Vec d)) k b.1} with hslicedef
    set covered : Set (Source.Coarse.Carrier d) := ⋃ k : ℕ, slice k with hcovered
    set cover : Option ℕ → Set (Source.Coarse.Carrier d) := fun n =>
      match n with
      | none => coveredᶜ
      | some k => slice k with hcoverdef
    set f : (n : Option ℕ) → cover n → ℝ := fun _ b =>
      R (sourceCoeffOn U hUbdd b.1) with hf
    have hagree : ∀ (m n : Option ℕ) (b : Source.Coarse.Carrier d)
        (hbm : b ∈ cover m) (hbn : b ∈ cover n), f m ⟨b, hbm⟩ = f n ⟨b, hbn⟩ := by
      intro _ _ _ _ _
      rfl
    have hcover : ⋃ n : Option ℕ, cover n = Set.univ := by
      ext b
      refine ⟨fun _ => Set.mem_univ b, fun _ => ?_⟩
      by_cases hb : b ∈ covered
      · rcases Set.mem_iUnion.mp hb with ⟨k, hk⟩
        exact Set.mem_iUnion.mpr ⟨some k, by simpa [hcoverdef] using hk⟩
      · exact Set.mem_iUnion.mpr ⟨none, by simpa [hcoverdef] using hb⟩
    have hcover_meas : ∀ n : Option ℕ, MeasurableSet (cover n) := by
      intro n
      have hk : ∀ k : ℕ, MeasurableSet (slice k) := fun k =>
        Recurrence.measurableSet_sourceLocal_aeeSlice hUopen k
      cases n with
      | none => exact (MeasurableSet.iUnion hk).compl
      | some k => exact hk k
    have hfm : ∀ n : Option ℕ, Measurable (f n) := by
      intro n
      cases n with
      | none =>
          have hzero : f none = fun _ : cover none => (0 : ℝ) := by
            funext b
            exact absurd (Set.mem_iUnion.mpr
              (Recurrence.exists_source_aeeQuantitativeEllipticSlice hUopen.measurableSet hUbdd
                (b : Source.Coarse.Carrier d))) b.2
          rw [hzero]
          exact measurable_const
      | some k =>
          have hEntry : ∀ (i' j' : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
              HasCompactSupport φ → tsupport φ ⊆ (U : Set (Vec d)) →
              Measurable fun x : cover (some k) =>
                entryTestR i' j' φ
                  (Source.Coarse.coarseToRegular (x : Source.Coarse.Carrier d)) := by
            intro i' j' φ hcont hcpt hsupp
            have hentry : @Measurable (RegCoeffField d) ℝ
                (SmoothLocalSigmaR (U : Set (Vec d))) _ (entryTestR i' j' φ) := by
              intro tt htt
              exact MeasurableSpace.measurableSet_generateFrom
                ⟨i', j', φ, hcont, hcpt, hsupp, tt, htt, rfl⟩
            exact hentry.comp
              ((Source.Coarse.measurable_coarseToRegular_smoothLocal (U : Set (Vec d))
                hUopen.measurableSet).comp measurable_subtype_coe)
          exact hslice k (cover (some k)) inferInstance
            (fun x => Source.Coarse.coarseToRegular (x : Source.Coarse.Carrier d))
            (fun x => x.2) hEntry
            (fun x => sourceCoeffOn U hUbdd (x : Source.Coarse.Carrier d)) (fun _ => rfl)
    have hEq : (fun b : Source.Coarse.Carrier d => R (sourceCoeffOn U hUbdd b)) =
        Set.liftCover cover f hagree hcover := by
      funext b
      obtain ⟨k, hbk⟩ :=
        Recurrence.exists_source_aeeQuantitativeEllipticSlice hUopen.measurableSet hUbdd b
      have hmem : b ∈ cover (some k) := hbk
      rw [Set.liftCover_of_mem (S := cover) (f := f) (hf := hagree) (hS := hcover)
        (i := some k) hmem]
    rw [hEq]
    exact measurable_liftCover cover hcover_meas f hfm hagree hcover
  have hglobal : Measurable fun b : Source.Coarse.Carrier d => R (sourceCoeffOn U hUbdd b) :=
    Measurable.mono hlocal
      (Source.Coarse.localSigma_mono hUopen.measurableSet MeasurableSet.univ
        (Set.subset_univ _)) le_rfl
  have hEq : (fun a : CoeffSpace d => R (a.coeffOn U)) =
      (fun b : Source.Coarse.Carrier d => R (sourceCoeffOn U hUbdd b)) ∘ sourceRepresentative := by
    funext a
    exact hcongr _ _ (ae_restrict_of_ae (sourceRepresentative_ae_eq a))
  rw [hEq]
  exact hglobal.comp measurable_sourceRepresentative

/-! ## Bounded weights against square integrable functions -/

theorem memScalarL2_bounded_mul {U : Set (Vec d)} {eta w : Vec d → ℝ}
    (hmeas : Measurable eta) {C : ℝ} (hbound : ∀ x, |eta x| ≤ C)
    (hw : MemScalarL2 U w) : MemScalarL2 U (fun x => eta x * w x) := by
  refine MeasureTheory.MemLp.mono' (MeasureTheory.MemLp.const_mul hw.norm C)
    (hmeas.aestronglyMeasurable.mul hw.aestronglyMeasurable)
    (_root_.Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hbound x) (abs_nonneg _)

/-! ## The localized optimizer energy -/

theorem optimizerBlockState_fst (U : Book.Ch02.Domain d)
    (aU : Book.Ch02.CoeffOn U) (p q : Vec d) (x : Vec d) :
    (optimizerBlockState U aU p q x).1 =
      (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U aU) p
        q).toSolution.toH1.grad x :=
  rfl

theorem optimizerBlockState_snd (U : Book.Ch02.Domain d)
    (aU : Book.Ch02.CoeffOn U) (p q : Vec d) (x : Vec d) :
    (optimizerBlockState U aU p q x).2 =
      matVecMul (aU.toCoeffField x) (optimizerBlockState U aU p q x).1 :=
  rfl

/-- The localized weighted energy of the response optimizer on its cell. -/
@[expose]
def weightedOptimizerEnergy (U : Book.Ch02.Domain d) (aU : Book.Ch02.CoeffOn U)
    (p q : Vec d) (eta : Vec d → ℝ) : ℝ :=
  Book.Ch02.average U fun x => eta x * ((1 / 2 : ℝ) *
    vecDot (optimizerBlockState U aU p q x).1
      (matVecMul (aU.toCoeffField x) (optimizerBlockState U aU p q x).1))

/-- **The localized optimizer energy is a continuous quadratic functional of the
ambient optimizer state.** -/
theorem weightedOptimizerEnergy_eq {U : Book.Ch02.Domain d}
    (aU : Book.Ch02.CoeffOn U) (p q : Vec d) {eta : Vec d → ℝ}
    (hmeas : Measurable eta) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |eta x| ≤ C) :
    weightedOptimizerEnergy U aU p q eta =
      (volume (U : Set (Vec d))).toReal⁻¹ * ((1 / 2 : ℝ) *
        ∑ i : Fin d, inner ℝ
          (weightedCoordOperator (U := (U : Set (Vec d))) hmeas hC hbound
            (Sum.inl i) (Sum.inr i) (optimizerStateL2 U aU p q))
          (optimizerStateL2 U aU p q)) := by
  have hgrad : MemVectorL2 (U : Set (Vec d)) fun x => (optimizerBlockState U aU p q x).1 :=
    MeasureTheory.MemLp.fst (memBlockL2_optimizerBlockState aU p q)
  have hflux : MemVectorL2 (U : Set (Vec d)) fun x => (optimizerBlockState U aU p q x).2 :=
    MeasureTheory.MemLp.snd (memBlockL2_optimizerBlockState aU p q)
  have hterm : ∀ i : Fin d, IntegrableOn (fun x => eta x *
      (optimizerBlockState U aU p q x).1 i * (optimizerBlockState U aU p q x).2 i)
      (U : Set (Vec d)) := by
    intro i
    have h1 : MemScalarL2 (U : Set (Vec d))
        (fun x => eta x * (optimizerBlockState U aU p q x).1 i) :=
      memScalarL2_bounded_mul hmeas hbound (MeasureTheory.MemLp.eval hgrad i)
    have h2 : MemScalarL2 (U : Set (Vec d))
        (fun x => (optimizerBlockState U aU p q x).2 i) :=
      MeasureTheory.MemLp.eval hflux i
    have hmul := MeasureTheory.MemLp.integrable_mul h1 h2
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn, Pi.mul_apply] using! hmul
  have hcoord : ∀ i : Fin d,
      inner ℝ (weightedCoordOperator (U := (U : Set (Vec d))) hmeas hC hbound
          (Sum.inl i) (Sum.inr i) (optimizerStateL2 U aU p q))
        (optimizerStateL2 U aU p q) =
        ∫ x in (U : Set (Vec d)), eta x * (optimizerBlockState U aU p q x).1 i *
          (optimizerBlockState U aU p q x).2 i ∂volume := by
    intro i
    rw [inner_weightedCoordOperator]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_optimizerStateL2 U aU p q] with x hx
    rw [hx]
    simp [toFullBlockVec]
  rw [weightedOptimizerEnergy, Book.Ch02.average]
  have hsum : (∑ i : Fin d, inner ℝ
      (weightedCoordOperator (U := (U : Set (Vec d))) hmeas hC hbound
        (Sum.inl i) (Sum.inr i) (optimizerStateL2 U aU p q))
      (optimizerStateL2 U aU p q)) =
      ∫ x in (U : Set (Vec d)), eta x *
        vecDot (optimizerBlockState U aU p q x).1
          (matVecMul (aU.toCoeffField x) (optimizerBlockState U aU p q x).1) ∂volume := by
    calc
      (∑ i : Fin d, inner ℝ
          (weightedCoordOperator (U := (U : Set (Vec d))) hmeas hC hbound
            (Sum.inl i) (Sum.inr i) (optimizerStateL2 U aU p q))
          (optimizerStateL2 U aU p q))
          = ∑ i : Fin d, ∫ x in (U : Set (Vec d)),
              eta x * (optimizerBlockState U aU p q x).1 i *
                (optimizerBlockState U aU p q x).2 i ∂volume :=
            Finset.sum_congr rfl fun i _ => hcoord i
      _ = ∫ x in (U : Set (Vec d)), ∑ i : Fin d,
            eta x * (optimizerBlockState U aU p q x).1 i *
              (optimizerBlockState U aU p q x).2 i ∂volume :=
            (integral_finsetSum _ fun i _ => hterm i).symm
      _ = ∫ x in (U : Set (Vec d)), eta x *
            vecDot (optimizerBlockState U aU p q x).1
              (matVecMul (aU.toCoeffField x) (optimizerBlockState U aU p q x).1) ∂volume := by
            refine integral_congr_ae (_root_.Filter.Eventually.of_forall fun x => ?_)
            simp only [vecDot, Finset.mul_sum, optimizerBlockState_snd]
            exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  congr 1
  rw [← integral_const_mul]
  exact integral_congr_ae (_root_.Filter.Eventually.of_forall fun x => by ring)

/-! ## Measurability of the localized optimizer energy -/

/-- The weighted quadratic functional of the ambient state is continuous. -/
theorem continuous_weightedEnergyFunctional {U : Set (Vec d)}
    {eta : Vec d → ℝ} (hmeas : Measurable eta)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |eta x| ≤ C) :
    Continuous fun z : HilbertBlockL2 U =>
      (volume U).toReal⁻¹ * ((1 / 2 : ℝ) *
        ∑ i : Fin d, inner ℝ
          (weightedCoordOperator (U := U) hmeas hC hbound (Sum.inl i) (Sum.inr i) z) z) := by
  refine continuous_const.mul (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_))
  exact continuous_inner.comp
    (((weightedCoordOperator (U := U) hmeas hC hbound (Sum.inl i)
      (Sum.inr i)).continuous).prodMk continuous_id)

/-- **The localized optimizer energy is measurable on one ellipticity slice.** -/
theorem measurable_weightedOptimizerEnergy_slice {Om : Type*} [mOm : MeasurableSpace Om]
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
    (p q : Vec d) {eta : Vec d → ℝ} (hmeas : Measurable eta) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, |eta x| ≤ C) :
    Measurable fun w : Om => weightedOptimizerEnergy U (aU w) p q eta := by
  have hstate := stronglyMeasurable_optimizerStateL2 hUopen hUfin hvol hSlice hEntry aU haU p q
  have hrw : (fun w : Om => weightedOptimizerEnergy U (aU w) p q eta) =
      fun w : Om =>
        (volume (U : Set (Vec d))).toReal⁻¹ * ((1 / 2 : ℝ) *
          ∑ i : Fin d, inner ℝ
            (weightedCoordOperator (U := (U : Set (Vec d))) hmeas hC hbound
              (Sum.inl i) (Sum.inr i) (optimizerStateL2 U (aU w) p q))
            (optimizerStateL2 U (aU w) p q)) := by
    funext w
    exact weightedOptimizerEnergy_eq (aU w) p q hmeas hC hbound
  rw [hrw]
  exact ((continuous_weightedEnergyFunctional (U := (U : Set (Vec d))) hmeas hC
    hbound).comp_stronglyMeasurable hstate).measurable

/-- The localized optimizer energy sees only the almost everywhere class of the
coefficient field. -/
theorem weightedOptimizerEnergy_congr {U : Book.Ch02.Domain d}
    {aU bU : Book.Ch02.CoeffOn U} (h : Book.Ch02.CoeffOn.AEEq aU bU) (p q : Vec d)
    (eta : Vec d → ℝ) :
    weightedOptimizerEnergy U aU p q eta = weightedOptimizerEnergy U bU p q eta := by
  have hgrad := Book.Ch02.canonicalMaximizer_sameGradientAE_ofAEEq h p q
  rw [weightedOptimizerEnergy, weightedOptimizerEnergy, Book.Ch02.average, Book.Ch02.average]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hgrad, h] with x hx hax
  have hx' :
      (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U aU) p
        q).toSolution.toH1.grad x =
      (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U bU) p
        q).toSolution.toH1.grad x := hx
  simp only [optimizerBlockState, hx', hax]

/-- **The localized optimizer energy is measurable on the coefficient space.** -/
theorem measurable_weightedOptimizerEnergy_coeffSpace {U : Book.Ch02.Domain d}
    (hUopen : IsOpen (U : Set (Vec d))) (hUbdd : IsBoundedDomain (U : Set (Vec d)))
    (hvol : 0 < (volume (U : Set (Vec d))).toReal) (p q : Vec d)
    {eta : Vec d → ℝ} (hmeas : Measurable eta) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, |eta x| ≤ C) :
    Measurable fun a : CoeffSpace d =>
      weightedOptimizerEnergy U (a.coeffOn U) p q eta := by
  have : IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d))) :=
    hUbdd.isFiniteMeasure_restrict_volume
  refine measurable_coeffSpace_of_slicewise hUopen hUbdd _
    (fun aU bU h => weightedOptimizerEnergy_congr h p q eta) ?_
  intro k Om mOm A hSlice hEntry aU haU
  exact measurable_weightedOptimizerEnergy_slice hUopen (ne_of_lt hUbdd.volume_lt_top) hvol
    hSlice hEntry aU haU p q hmeas hC hbound

/-! ## The response functional is a localized optimizer energy -/

/-- **The response functional is the optimizer energy at unit weight.** -/
theorem responseJ_eq_weightedOptimizerEnergy (U : Book.Ch02.Domain d)
    (aU : Book.Ch02.CoeffOn U) (p q : Vec d) :
    Book.Ch02.responseJ U aU p q = weightedOptimizerEnergy U aU p q (fun _ => 1) := by
  have hv := Book.Ch02.canonicalMaximizer_isMaximizer
    (Book.Ch02.responseExistenceTheory U aU) p q
  rw [(Book.Ch02.responseBasicVariationalIdentitiesTheory U aU).responseJ_eq_energy hv,
    Book.Ch02.variationEnergyValue, weightedOptimizerEnergy, Book.Ch02.average,
    Book.Ch02.average, ← mul_assoc, mul_comm (1 / 2 : ℝ), mul_assoc]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (_root_.Filter.Eventually.of_forall fun x => ?_)
  simp only [Book.Ch02.variationEnergyIntegrand, vecDot_matVecMul_symmPart,
    optimizerBlockState_fst]
  ring

/-- **The response functional is measurable on the coefficient space.** -/
theorem measurable_responseJ_coeffSpace {U : Book.Ch02.Domain d}
    (hUopen : IsOpen (U : Set (Vec d))) (hUbdd : IsBoundedDomain (U : Set (Vec d)))
    (hvol : 0 < (volume (U : Set (Vec d))).toReal) (p q : Vec d) :
    Measurable fun a : CoeffSpace d => Book.Ch02.responseJ U (a.coeffOn U) p q := by
  have hrw : (fun a : CoeffSpace d => Book.Ch02.responseJ U (a.coeffOn U) p q) =
      fun a : CoeffSpace d => weightedOptimizerEnergy U (a.coeffOn U) p q (fun _ => 1) := by
    funext a
    exact responseJ_eq_weightedOptimizerEnergy U (a.coeffOn U) p q
  rw [hrw]
  exact measurable_weightedOptimizerEnergy_coeffSpace hUopen hUbdd hvol p q
    measurable_const (C := 1) zero_le_one (fun _ => by norm_num)

end

end Selection
end HighContrast
end HCPolySupport
