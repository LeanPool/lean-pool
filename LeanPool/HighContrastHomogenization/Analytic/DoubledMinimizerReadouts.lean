/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.DoubledMinimizerSelection

/-!
# High-contrast homogenization: Analytic.DoubledMinimizerReadouts

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Readouts of the doubled variational minimizer

A readout of the doubled minimizer of a cell is a real-valued functional of the
minimizing field which may itself depend on the coefficient field, the leading
example being the energy pairing against a fixed test state.  This file records
the general transfer principle: a readout that is continuous in the field for
every sample and measurable in the sample on every fixed generator competitor is
measurable in the sample when evaluated at the minimizer.

The proof is the Galerkin selection again.  The selected competitors are
countably valued measurable functions of the sample converging to the minimizer,
so continuity of the readout in its field argument turns them into a sequence of
measurable real functions converging pointwise to the readout of the minimizer.

Two consequences are recorded: the pairing of the minimizer with a fixed `L²`
test field, and the doubled energy pairing of the minimizer with a fixed test
state — that is, the localized average of the coefficient-operator image of the
minimizer.
-/

namespace HCPolySupport
namespace HighContrast
namespace Selection

open MeasureTheory
open scoped Topology
open _root_.Filter

noncomputable section

variable {d : ℕ}

section Engine

variable {Om : Type*} [mOm : MeasurableSpace Om] {U : Set (Vec d)} {k : ℕ}
  [IsFiniteMeasure (volumeMeasureOn U)]

/-- **Transfer principle for readouts of the doubled minimizer.**  A readout
continuous in the field argument and measurable in the sample on every fixed
generator competitor is measurable in the sample at the minimizer. -/
theorem measurable_readout_cellMuMinimizer
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤) (hvol : 0 < (volume U).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U → Measurable fun w => entryTestR i j φ (A w))
    (P0 : BlockVec d) {F : Om → HilbertBlockL2 U → ℝ}
    (hFcont : ∀ w : Om, Continuous (F w))
    (hFmeas : ∀ Y : canonicalMuBlockCorrectionGeneratorSubmodule U,
      Measurable fun w : Om => F w (cellMuCandidate (U := U) P0 Y)) :
    Measurable fun w : Om =>
      F w ((cellMuHilbert hvol (sliceOf hSlice w)).minimizerMap P0) := by
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
  have hsel : ∀ m : ℕ,
      Measurable fun w : Om =>
        F w (cellMuCandidate (U := U) P0 (xi (Nat.find (hex m w)))) := by
    intro m
    exact Measurable.find (f := fun n w => F w (cellMuCandidate (U := U) P0 (xi n)))
      (fun n => hFmeas (xi n)) (hgood m) (hex m)
  refine measurable_of_tendsto_metrizable hsel ?_
  rw [tendsto_pi_nhds]
  intro w
  exact ((hFcont w).tendsto _).comp
    (tendsto_cellMuCandidate_selected hvol hSlice P0 xi
      (fun m w => Nat.find (hex m w)) hidx w)

/-- **The pairing of the doubled minimizer with a fixed `L²` test field is a
measurable function of the sample.** -/
theorem measurable_inner_cellMuMinimizer
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤) (hvol : 0 < (volume U).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U → Measurable fun w => entryTestR i j φ (A w))
    (P0 : BlockVec d) (y : HilbertBlockL2 U) :
    Measurable fun w : Om =>
      inner ℝ y ((cellMuHilbert hvol (sliceOf hSlice w)).minimizerMap P0) := by
  have hstrong :
      StronglyMeasurable fun w : Om =>
        (cellMuHilbert hvol (sliceOf hSlice w)).minimizerMap P0 :=
    stronglyMeasurable_cellMuMinimizer hUopen hUfin hvol hSlice hEntry P0
  have hcomp :
      StronglyMeasurable fun w : Om =>
        inner ℝ y ((cellMuHilbert hvol (sliceOf hSlice w)).minimizerMap P0) := by
    simpa [Function.comp_def, innerSL_apply_apply] using
      (innerSL ℝ y).continuous.comp_stronglyMeasurable hstrong
  exact hcomp.measurable

/-! ## The doubled energy pairing against a fixed test state -/

/-- The doubled block pairing average against a fixed pair of `L²` block states
is measurable in the sample. -/
theorem measurable_blockPairingAverage_of_measurable_entryTest
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U → Measurable fun w => entryTestR i j φ (A w))
    (X Y : BlockState d) (hX : MemBlockL2 U X.eval) (hY : MemBlockL2 U Y.eval) :
    Measurable fun w : Om => blockPairingAverage U (A w).toFun X Y := by
  refine measurable_blockPairingAverage_comp_of_measurable_weightedFullBlockCoeffEntryIntegrals
    (A := fun w => (A w).toFun) (X := X) (Y := Y)
    (fun w α β =>
      (hSlice w).integrableOn_pairingWeightedFullBlockCoeffEntry_of_memBlockL2 hX hY α β)
    (fun α β => ?_)
  exact measurable_integrableWeightedFullBlockCoeffEntry_carrier (hSlice := hSlice)
    (measurable_toHilbertMatrixL2_of_measurable_entryTest hUopen hUfin hSlice hEntry)
    (integrable_blockPairingEntryWeight_of_memBlockL2 hX hY α β) α β

/-- The doubled energy pairing of a fixed test state against a generator
competitor is a block pairing average. -/
theorem energyBilin_cellMuCandidate_eq_blockPairingAverage
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d)
    {Y : BlockState d} (hY : MemBlockL2 U Y.eval)
    (Z : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    (cellMuHilbert hvol a).energyBilin (toHilbertBlockL2OfBlockField (U := U) hY)
        (cellMuCandidate (U := U) P0 Z) =
      blockPairingAverage U a.1 (canonicalMuGeneratorAffineField (U := U) P0 Z) Y := by
  rw [energyBilin_cellMuHilbert, ← toHilbertBlockL2_generatorAffineField (U := U) P0 Z]
  exact (cellMuSystem hvol a).toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
    (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Z) hY

/-- **The doubled energy pairing of a fixed test state against the minimizer is
a measurable function of the sample.**  This is the localized average of the
coefficient-operator image of the minimizer. -/
theorem measurable_energyBilin_cellMuMinimizer
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤) (hvol : 0 < (volume U).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U → Measurable fun w => entryTestR i j φ (A w))
    (P0 : BlockVec d) {Y : BlockState d} (hY : MemBlockL2 U Y.eval) :
    Measurable fun w : Om =>
      (cellMuHilbert hvol (sliceOf hSlice w)).energyBilin
        (toHilbertBlockL2OfBlockField (U := U) hY)
        ((cellMuHilbert hvol (sliceOf hSlice w)).minimizerMap P0) := by
  refine measurable_readout_cellMuMinimizer hUopen hUfin hvol hSlice hEntry P0
    (F := fun w z => (cellMuHilbert hvol (sliceOf hSlice w)).energyBilin
      (toHilbertBlockL2OfBlockField (U := U) hY) z)
    (fun w => ((cellMuHilbert hvol (sliceOf hSlice w)).energyBilin
      (toHilbertBlockL2OfBlockField (U := U) hY)).continuous) (fun Z => ?_)
  have hrw : (fun w : Om =>
      (cellMuHilbert hvol (sliceOf hSlice w)).energyBilin
        (toHilbertBlockL2OfBlockField (U := U) hY) (cellMuCandidate (U := U) P0 Z)) =
      fun w : Om =>
        blockPairingAverage U (A w).toFun
          (canonicalMuGeneratorAffineField (U := U) P0 Z) Y := by
    funext w
    exact energyBilin_cellMuCandidate_eq_blockPairingAverage hvol (sliceOf hSlice w) P0 hY Z
  rw [hrw]
  exact measurable_blockPairingAverage_of_measurable_entryTest hUopen hUfin hSlice hEntry _ Y
    (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Z) hY

end Engine

end

end Selection
end HighContrast
end HCPolySupport
