/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.CellMuMeasurability
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Internal.AEESliceAssembly.CarrierMinimizerFamily

/-!
# High-contrast homogenization: Analytic.DoubledMinimizerSelection

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Measurable selection of the doubled variational minimizer on a general cell

The doubled variational problem defining the coarse block of `s.introduction`
minimizes the doubled energy over the affine space `P + \Lpoto(U) × \Lsolo(U)`,
whose correction space does not depend on the coefficient field.  The minimizer is
therefore a genuine function of the field, and this file proves that it is a
measurable one, on an arbitrary bounded open cell of positive volume.

The argument is a Galerkin selection.  The correction space is the closure of a
separable submodule of pointwise potential/solenoidal corrections, so along a
fixed dense sequence of generators the variational quantity is the infimum of
countably many competitor energies, each a measurable function of the field.
Choosing, for each tolerance, the first generator whose energy is within that
tolerance of the infimum gives a measurable countably valued approximation, and
the energy gap controls the Hilbert distance to the minimizer, so the
approximations converge to it pointwise.  A pointwise limit of strongly
measurable maps into the ambient `L²` space is strongly measurable, and so is
every fixed continuous readout of it.

Everything here is stated on one quantitative ellipticity slice of the cell and
for an arbitrary measurable parameter space whose localized smooth entry tests
are measurable; the passage to the coefficient space is a separate step.
-/

namespace HCPolySupport
namespace HighContrast
namespace Selection

open MeasureTheory
open scoped Topology
open _root_.Filter

noncomputable section

variable {d : ℕ}

/-! ## The doubled problem of a general cell on one ellipticity slice -/

section Realization

variable {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}

/-- The doubled operator system of a cell of positive volume, on one
quantitative ellipticity slice, with the canonical potential/solenoidal
correction space. -/
@[expose]
def cellMuSystem (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    AEEMuOperatorSystemData U a.1 :=
  (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toAEEMuOperatorSystemData
    (AEEMuCoeffOperatorData.ofIsAEEllipticFieldOn a.2 hvol)

/-- The doubled variational problem of a cell of positive volume, realized in
the ambient `L²` space on one quantitative ellipticity slice. -/
@[expose]
def cellMuHilbert (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    MuHilbertRealization U a.1 :=
  (cellMuSystem hvol a).toMuHilbertRealization

theorem constantField_cellMuHilbert (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    (cellMuHilbert hvol a).constantField = blockVecToHilbertBlockL2Const (U := U) :=
  rfl

theorem correctionSpace_cellMuHilbert (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    (cellMuHilbert hvol a).correctionSpace = MuCorrectionSpaceData.ofSubmoduleClosures U :=
  rfl

theorem energyBilin_cellMuHilbert (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    (cellMuHilbert hvol a).energyBilin =
      energyBilinOfOperator (cellMuSystem hvol a).toMuOperatorRealization.operator :=
  rfl

/-- The minimizer of the cell's doubled problem is the affine Hilbert minimizer
of its energy over the canonical correction space. -/
theorem minimizerMap_cellMuHilbert (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d) :
    (cellMuHilbert hvol a).minimizerMap P0 =
      affineMinimizerMap (cellMuHilbert hvol a).correctionSpace.correctionSpace
        (cellMuHilbert hvol a).energyBilin (cellMuHilbert hvol a).energyCoercive
        ((cellMuHilbert hvol a).constantField P0) :=
  rfl

/-- The affine competitor attached to a correction generator. -/
@[expose]
def cellMuCandidate (P0 : BlockVec d)
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) : HilbertBlockL2 U :=
  blockVecToHilbertBlockL2Const (U := U) P0 +
    (canonicalMuCorrectionGeneratorEmbedding U Y : HilbertBlockL2 U)

/-- The competitor attached to a generator is the ambient image of its affine
block state. -/
theorem toHilbertBlockL2_generatorAffineField (P0 : BlockVec d)
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    toHilbertBlockL2OfBlockField (U := U)
        (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Y) =
      cellMuCandidate (U := U) P0 Y :=
  canonicalMuGeneratorAffineField_hilbert_eq_const_add (U := U) P0 Y

/-- The competitor attached to a generator is admissible for the cell's doubled
problem. -/
theorem cellMuCandidate_sub_constantField_mem (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d)
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    cellMuCandidate (U := U) P0 Y - (cellMuHilbert hvol a).constantField P0 ∈
      (cellMuHilbert hvol a).correctionSpace.correctionSpace := by
  rw [correctionSpace_cellMuHilbert, constantField_cellMuHilbert, cellMuCandidate,
    add_sub_cancel_left]
  exact (canonicalMuCorrectionGeneratorEmbedding U Y).2

/-- The quadratic energy of a generator competitor is the block energy average
of its pointwise representative. -/
theorem quadraticEnergy_cellMuCandidate (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d)
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    quadraticEnergy (cellMuHilbert hvol a).energyBilin (cellMuCandidate (U := U) P0 Y) =
      blockEnergyAverage U a.1 (canonicalMuGeneratorAffineField (U := U) P0 Y) := by
  rw [← toHilbertBlockL2_generatorAffineField (U := U) P0 Y, energyBilin_cellMuHilbert]
  exact (cellMuSystem hvol
    a).toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
    (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Y)

/-- The variational quantity of the cell is the minimized quadratic energy of
its doubled problem. -/
theorem mu_eq_muCandidate_cellMuHilbert (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d) :
    Mu U P0 a.1 = (cellMuHilbert hvol a).muCandidate P0 :=
  Recurrence.mu_eq_aeeMuCandidate a.2 hvol P0

/-- The variational quantity of the cell is the quadratic energy of the
minimizer of its doubled problem. -/
theorem mu_eq_quadraticEnergy_minimizerMap (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d) :
    Mu U P0 a.1 =
      quadraticEnergy (cellMuHilbert hvol a).energyBilin
        ((cellMuHilbert hvol a).minimizerMap P0) :=
  mu_eq_muCandidate_cellMuHilbert hvol a P0

end Realization

/-! ## The Galerkin selection over a measurable parameter space -/

section Engine

variable {Om : Type*} [mOm : MeasurableSpace Om] {U : Set (Vec d)} {k : ℕ}
  [IsFiniteMeasure (volumeMeasureOn U)]

/-- The slice datum attached to a parameter. -/
@[expose]
def sliceOf {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun) (w : Om) :
    {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} :=
  ⟨(A w).toFun, hSlice w⟩

/-- The `L²` realization of the block coefficient field is measurable in the
parameter whenever the localized smooth entry tests are. -/
theorem measurable_toHilbertMatrixL2_of_measurable_entryTest
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U → Measurable fun w => entryTestR i j φ (A w)) :
    @Measurable Om (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)) mOm (borel _)
      (fun w => AEEQuantitativeEllipticSlice.toHilbertMatrixL2 (sliceOf hSlice w)) := by
  classical
  have : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  let : MeasurableSpace (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)) := borel _
  have : BorelSpace (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)) := ⟨rfl⟩
  obtain ⟨u, hu, hSmooth⟩ := exists_dense_smoothProbeSequence_of_dense_smoothProbeSet (U := U)
    (dense_smoothCompactSupportHilbertMatrixL2_tsupport_subset hUopen hUfin)
  refine measurable_of_measurable_inner_denseRange_polish u hu fun n => ?_
  rcases hSmooth n with ⟨g, hgL2, hEqn, hg_cont, hg_compact, hg_support⟩
  rw [hEqn]
  exact measurable_inner_hilbertMatrixSmoothProbe_toHilbertMatrixL2_carrier
    (mΩ := mOm) (A := A) (hSlice := hSlice) hUopen.measurableSet hEntry hgL2 hg_cont
    hg_compact hg_support

/-- The competitor energies along a fixed generator sequence are measurable in
the parameter. -/
theorem measurable_blockEnergyAverage_generator
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U → Measurable fun w => entryTestR i j φ (A w))
    (P0 : BlockVec d) (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    Measurable fun w : Om =>
      blockEnergyAverage U (A w).toFun (canonicalMuGeneratorAffineField (U := U) P0 Y) := by
  refine measurable_blockEnergyAverage_carrier (hSlice := hSlice) ?_ _
    (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Y)
  exact measurable_toHilbertMatrixL2_of_measurable_entryTest hUopen hUfin hSlice hEntry

omit mOm in
/-- For each tolerance and each parameter some competitor along a dense
generator sequence is within that tolerance of the variational quantity. -/
theorem exists_blockEnergyAverage_le (hvol : 0 < (volume U).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (P0 : BlockVec d) (xi : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U)
    (hxi : DenseRange xi) (m : ℕ) (w : Om) :
    ∃ n : ℕ,
      blockEnergyAverage U (A w).toFun
          (canonicalMuGeneratorAffineField (U := U) P0 (xi n)) ≤
        Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1) := by
  have hmu : Mu U P0 (A w).toFun =
      ⨅ n : ℕ, blockEnergyAverage U (A w).toFun
        (canonicalMuGeneratorAffineField (U := U) P0 (xi n)) :=
    Recurrence.mu_eq_iInf_blockEnergyAverage (hSlice w) hvol P0 xi hxi
  have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  have hlt :
      (⨅ n : ℕ, blockEnergyAverage U (A w).toFun
          (canonicalMuGeneratorAffineField (U := U) P0 (xi n))) <
        (⨅ n : ℕ, blockEnergyAverage U (A w).toFun
          (canonicalMuGeneratorAffineField (U := U) P0 (xi n))) + 1 / ((m : ℝ) + 1) :=
    lt_add_of_le_of_pos le_rfl hpos
  rcases exists_lt_of_ciInf_lt hlt with ⟨n, hn⟩
  exact ⟨n, le_of_lt (by simpa [hmu] using hn)⟩

omit mOm in
/-- The selected competitors converge, at every parameter, to the minimizer of
the cell's doubled problem. -/
theorem tendsto_cellMuCandidate_selected (hvol : 0 < (volume U).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (P0 : BlockVec d) (xi : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U)
    (idx : ℕ → Om → ℕ)
    (hidx : ∀ (m : ℕ) (w : Om),
      blockEnergyAverage U (A w).toFun
          (canonicalMuGeneratorAffineField (U := U) P0 (xi (idx m w))) ≤
        Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1))
    (w : Om) :
    Tendsto (fun m : ℕ => cellMuCandidate (U := U) P0 (xi (idx m w))) atTop
      (𝓝 ((cellMuHilbert hvol (sliceOf hSlice w)).minimizerMap P0)) := by
  have heps : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmem : ∀ m : ℕ,
      cellMuCandidate (U := U) P0 (xi (idx m w)) -
          (cellMuHilbert hvol (sliceOf hSlice w)).constantField P0 ∈
        (cellMuHilbert hvol (sliceOf hSlice w)).correctionSpace.correctionSpace := fun m =>
    cellMuCandidate_sub_constantField_mem hvol (sliceOf hSlice w) P0 (xi (idx m w))
  have hnear : ∀ m : ℕ,
      quadraticEnergy (cellMuHilbert hvol (sliceOf hSlice w)).energyBilin
          (cellMuCandidate (U := U) P0 (xi (idx m w))) ≤
        quadraticEnergy (cellMuHilbert hvol (sliceOf hSlice w)).energyBilin
          (affineMinimizerMap
            (cellMuHilbert hvol (sliceOf hSlice w)).correctionSpace.correctionSpace
            (cellMuHilbert hvol (sliceOf hSlice w)).energyBilin
            (cellMuHilbert hvol (sliceOf hSlice w)).energyCoercive
            ((cellMuHilbert hvol (sliceOf hSlice w)).constantField P0)) +
          1 / ((m : ℝ) + 1) := by
    intro m
    have hmin :
        Mu U P0 (A w).toFun =
          quadraticEnergy (cellMuHilbert hvol (sliceOf hSlice w)).energyBilin
            (affineMinimizerMap
              (cellMuHilbert hvol (sliceOf hSlice w)).correctionSpace.correctionSpace
              (cellMuHilbert hvol (sliceOf hSlice w)).energyBilin
              (cellMuHilbert hvol (sliceOf hSlice w)).energyCoercive
              ((cellMuHilbert hvol (sliceOf hSlice w)).constantField P0)) := by
      rw [← minimizerMap_cellMuHilbert hvol (sliceOf hSlice w) P0]
      exact mu_eq_quadraticEnergy_minimizerMap hvol (sliceOf hSlice w) P0
    calc
      quadraticEnergy (cellMuHilbert hvol (sliceOf hSlice w)).energyBilin
            (cellMuCandidate (U := U) P0 (xi (idx m w)))
          = blockEnergyAverage U (A w).toFun
              (canonicalMuGeneratorAffineField (U := U) P0 (xi (idx m w))) :=
            quadraticEnergy_cellMuCandidate hvol (sliceOf hSlice w) P0 (xi (idx m w))
      _ ≤ Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1) := hidx m w
      _ = quadraticEnergy (cellMuHilbert hvol (sliceOf hSlice w)).energyBilin
            (affineMinimizerMap
              (cellMuHilbert hvol (sliceOf hSlice w)).correctionSpace.correctionSpace
              (cellMuHilbert hvol (sliceOf hSlice w)).energyBilin
              (cellMuHilbert hvol (sliceOf hSlice w)).energyCoercive
              ((cellMuHilbert hvol (sliceOf hSlice w)).constantField P0)) +
              1 / ((m : ℝ) + 1) := by rw [hmin]
  rw [minimizerMap_cellMuHilbert hvol (sliceOf hSlice w) P0]
  exact tendsto_of_quadraticEnergy_le_min_add_eps
    (cellMuHilbert hvol (sliceOf hSlice w)).correctionSpace.correctionSpace
    (cellMuHilbert hvol (sliceOf hSlice w)).energyCoercive
    (cellMuHilbert hvol (sliceOf hSlice w)).energySymm
    ((cellMuHilbert hvol (sliceOf hSlice w)).constantField P0) hmem heps hnear

/-- **The minimizer of the cell's doubled variational problem is a strongly
measurable function of the parameter.**  The Galerkin selection along a fixed
dense generator sequence produces countably valued measurable approximations,
and the energy gap forces them to converge to the minimizer. -/
theorem stronglyMeasurable_cellMuMinimizer
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤) (hvol : 0 < (volume U).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U → Measurable fun w => entryTestR i j φ (A w))
    (P0 : BlockVec d) :
    StronglyMeasurable fun w : Om =>
      (cellMuHilbert hvol (sliceOf hSlice w)).minimizerMap P0 := by
  classical
  have : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  obtain ⟨xi, hxi⟩ :
      ∃ xi : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U, DenseRange xi :=
    ⟨TopologicalSpace.denseSeq _, TopologicalSpace.denseRange_denseSeq _⟩
  have hex := exists_blockEnergyAverage_le hvol hSlice P0 xi hxi
  have hidx : ∀ (m : ℕ) (w : Om),
      blockEnergyAverage U (A w).toFun
          (canonicalMuGeneratorAffineField (U := U) P0 (xi (Nat.find (hex m w)))) ≤
        Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1) := fun m w => Nat.find_spec (hex m w)
  have hgood : ∀ m n : ℕ,
      MeasurableSet {w : Om |
        blockEnergyAverage U (A w).toFun
            (canonicalMuGeneratorAffineField (U := U) P0 (xi n)) ≤
          Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1)} := by
    intro m n
    exact measurableSet_le
      (measurable_blockEnergyAverage_generator hUopen hUfin hSlice hEntry P0 (xi n))
      ((Recurrence.measurable_Mu_of_measurable_entryTest hUopen hUfin hvol hSlice hEntry P0).add
        measurable_const)
  have hidx_meas : ∀ m : ℕ, Measurable fun w : Om => Nat.find (hex m w) := fun m =>
    measurable_find (hex m) (hgood m)
  have happrox : ∀ m : ℕ,
      StronglyMeasurable fun w : Om =>
        cellMuCandidate (U := U) P0 (xi (Nat.find (hex m w))) := by
    intro m
    have hdisc : StronglyMeasurable fun n : ℕ => cellMuCandidate (U := U) P0 (xi n) :=
      StronglyMeasurable.of_discrete
    simpa [Function.comp_def] using hdisc.comp_measurable (hidx_meas m)
  refine stronglyMeasurable_of_tendsto atTop happrox ?_
  rw [tendsto_pi_nhds]
  exact fun w =>
    tendsto_cellMuCandidate_selected hvol hSlice P0 xi (fun m w => Nat.find (hex m w)) hidx w

end Engine

end

end Selection
end HighContrast
end HCPolySupport
