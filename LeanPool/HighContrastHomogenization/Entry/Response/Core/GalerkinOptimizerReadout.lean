/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.DoubledMinimizerReadouts
public import LeanPool.HighContrastHomogenization.Analytic.DoubledMinimizerSelection
public import LeanPool.HighContrastHomogenization.Analytic.OptimizerGradientReadout
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ResponseFieldSize
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DoubledMu
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Internal.AEESliceAssembly.CarrierMinimizerFamily

/-!
# High-contrast homogenization: Entry.Response.Core.GalerkinOptimizerReadout

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Galerkin realization and readout of the response optimizer

On a general open response cell, this file re-derives the measurable canonical response optimizer
from the library's countable-energy Hilbert-space presentation and the Chapter-4 realization,
constructing the correction space, the quadratic energy functional and its minimizer, and proving
the measurability of the resulting bilinear form, inner product and readout. It then recovers the
canonical optimizer's block state and its coefficient-on-a-slice presentation from the doubled
minimizer, showing the readout is almost everywhere the full block vector, that it agrees under
congruence, and that a potential built from it has zero trace on the book's boundary presentation.
This furnishes the measurable response-optimizer readout that the response-transfer estimate
`p.response.transfer` consumes.
-/

section
/-!
## Galerkin selection on a response cell

This is the general-open-cell part of the measurable response-maximizer chain.  It is re-derived
on the current `RegCoeffField` carrier from CG's Chapter-4 Hilbert realization and this
library's public countable-energy presentation.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {d : ℕ}

/-- The doubled operator system on a general positive-volume response cell. -/
@[expose]
def responseCellMuSystem {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    AEEMuOperatorSystemData U a.1 :=
  (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toAEEMuOperatorSystemData
    (AEEMuCoeffOperatorData.ofIsAEEllipticFieldOn a.2 hvol)

/-- The Hilbert realization of `responseCellMuSystem`. -/
@[expose]
def responseCellMuHilbert {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    MuHilbertRealization U a.1 :=
  (responseCellMuSystem hvol a).toMuHilbertRealization

/-- The carrier slice datum at a parameter. -/
@[expose]
def responseSliceOf {Om : Type*} [MeasurableSpace Om] {U : Set (Vec d)} {k : ℕ}
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun) (w : Om) :
    {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} :=
  ⟨(A w).toFun, hSlice w⟩

theorem constantField_responseCellMuHilbert
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    (responseCellMuHilbert hvol a).constantField = blockVecToHilbertBlockL2Const (U := U) :=
  rfl

theorem correctionSpace_responseCellMuHilbert
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    (responseCellMuHilbert hvol a).correctionSpace =
      MuCorrectionSpaceData.ofSubmoduleClosures U :=
  rfl

theorem responseCellMuCandidate_sub_constant_mem
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d)
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    Selection.cellMuCandidate P0 Y - (responseCellMuHilbert hvol a).constantField P0 ∈
      (responseCellMuHilbert hvol a).correctionSpace.correctionSpace := by
  rw [correctionSpace_responseCellMuHilbert, constantField_responseCellMuHilbert,
    Selection.cellMuCandidate, add_sub_cancel_left]
  exact (canonicalMuCorrectionGeneratorEmbedding U Y).2

theorem quadraticEnergy_responseCellMuCandidate
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d)
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    quadraticEnergy (responseCellMuHilbert hvol a).energyBilin
        (Selection.cellMuCandidate P0 Y) =
      blockEnergyAverage U a.1 (canonicalMuGeneratorAffineField (U := U) P0 Y) := by
  have hsplit := canonicalMuGeneratorAffineField_hilbert_eq_const_add (U := U) P0 Y
  rw [Selection.cellMuCandidate, ← hsplit]
  simpa [responseCellMuHilbert, responseCellMuSystem,
    AEEMuOperatorSystemData.toMuHilbertRealization,
    MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
    (responseCellMuSystem hvol a).toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
      (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Y)

/-- On a general response cell, `Mu` is the energy of the Hilbert minimizer. -/
theorem responseMu_eq_quadraticEnergy_minimizer
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d) :
    Mu U P0 a.1 = quadraticEnergy (responseCellMuHilbert hvol a).energyBilin
      ((responseCellMuHilbert hvol a).minimizerMap P0) := by
  let ξ : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U :=
    TopologicalSpace.denseSeq _
  let H := responseCellMuHilbert hvol a
  let gen : ℕ → H.correctionSpace.correctionSpace.toSubmodule := fun n =>
    canonicalMuCorrectionGeneratorEmbedding U (ξ n)
  have hgen : DenseRange gen := by
    have hc := DenseRange.comp
      (denseRange_canonicalMuCorrectionGeneratorEmbedding U)
      (TopologicalSpace.denseRange_denseSeq
        (canonicalMuBlockCorrectionGeneratorSubmodule U))
      (continuous_canonicalMuCorrectionGeneratorEmbedding U)
    simpa [gen, ξ, H, responseCellMuHilbert, responseCellMuSystem,
      PotentialSolenoidalL2Data.toAEEMuOperatorSystemData,
      MuCorrectionSpaceData.ofSubmoduleClosures,
      AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
      Function.comp_def] using! hc
  have hcandidate : H.muCandidate P0 = ⨅ n : ℕ,
      quadraticEnergy H.energyBilin (Selection.cellMuCandidate P0 (ξ n)) := by
    rw [H.muCandidate_eq_sInf_quadraticEnergy_denseRange P0 gen hgen, sInf_range]
    apply iInf_congr
    intro n
    simp [H, gen, Selection.cellMuCandidate, responseCellMuHilbert, responseCellMuSystem,
      PotentialSolenoidalL2Data.toAEEMuOperatorSystemData,
      AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator]
  have hmu := Annealed.mu_eq_iInf_energy_for_responseSelection hvol k a P0
  have henergy : ∀ n : ℕ,
      quadraticEnergy H.energyBilin (Selection.cellMuCandidate P0 (ξ n)) =
        blockEnergyAverage U a.1
          (canonicalMuGeneratorAffineField (U := U) P0 (ξ n)) := by
    intro n
    exact quadraticEnergy_responseCellMuCandidate hvol a P0 (ξ n)
  have hMuCandidate : Mu U P0 a.1 = H.muCandidate P0 := by
    calc
      Mu U P0 a.1 = ⨅ n : ℕ, blockEnergyAverage U a.1
          (canonicalMuGeneratorAffineField (U := U) P0 (ξ n)) := by simpa [ξ] using hmu
      _ = ⨅ n : ℕ, quadraticEnergy H.energyBilin
          (Selection.cellMuCandidate P0 (ξ n)) := (iInf_congr henergy).symm
      _ = H.muCandidate P0 := hcandidate.symm
  simpa [H, MuHilbertRealization.muCandidate, MuHilbertProblem.muCandidate,
    MuHilbertRealization.minimizerMap, MuHilbertProblem.minimizerMap,
    parameterAffineMinimizerMap] using! hMuCandidate

/-- Near-minimal fixed Galerkin competitors converge pointwise to the response-cell minimizer. -/
theorem tendsto_responseCellMuCandidate_selected
    {Om : Type*} [MeasurableSpace Om] {U : Set (Vec d)} {k : ℕ}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hvol : 0 < (volume U).toReal) {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (P0 : BlockVec d) (ξ : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U)
    (index : ℕ → Om → ℕ)
    (hindex : ∀ (m : ℕ) (w : Om),
      blockEnergyAverage U (A w).toFun
          (canonicalMuGeneratorAffineField (U := U) P0 (ξ (index m w))) ≤
        Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1))
    (w : Om) :
    Tendsto (fun m : ℕ ↦ Selection.cellMuCandidate P0 (ξ (index m w))) atTop
      (𝓝 ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0)) := by
  let a := responseSliceOf hSlice w
  let H := responseCellMuHilbert hvol a
  have hmem : ∀ m : ℕ,
      Selection.cellMuCandidate P0 (ξ (index m w)) - H.constantField P0 ∈
        H.correctionSpace.correctionSpace := fun m ↦
    responseCellMuCandidate_sub_constant_mem hvol a P0 (ξ (index m w))
  have heps : Tendsto (fun m : ℕ ↦ 1 / ((m : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hnear : ∀ m : ℕ,
      quadraticEnergy H.energyBilin (Selection.cellMuCandidate P0 (ξ (index m w))) ≤
        quadraticEnergy H.energyBilin (affineMinimizerMap H.correctionSpace.correctionSpace
          H.energyBilin H.energyCoercive (H.constantField P0)) + 1 / ((m : ℝ) + 1) := by
    intro m
    have hmin := responseMu_eq_quadraticEnergy_minimizer hvol a P0
    calc
      quadraticEnergy H.energyBilin (Selection.cellMuCandidate P0 (ξ (index m w))) =
          blockEnergyAverage U (A w).toFun
            (canonicalMuGeneratorAffineField (U := U) P0 (ξ (index m w))) := by
        simpa [H, a, responseSliceOf] using
          quadraticEnergy_responseCellMuCandidate hvol a P0 (ξ (index m w))
      _ ≤ Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1) := hindex m w
      _ = quadraticEnergy H.energyBilin
          (affineMinimizerMap H.correctionSpace.correctionSpace H.energyBilin
            H.energyCoercive (H.constantField P0)) + 1 / ((m : ℝ) + 1) := by
        simpa [H, a, responseSliceOf, MuHilbertRealization.minimizerMap,
          MuHilbertProblem.minimizerMap, parameterAffineMinimizerMap] using!
          congrArg (fun r : ℝ ↦ r + 1 / ((m : ℝ) + 1)) hmin
  change Tendsto (fun m : ℕ ↦ Selection.cellMuCandidate P0 (ξ (index m w))) atTop
    (𝓝 (H.minimizerMap P0))
  rw [show H.minimizerMap P0 = affineMinimizerMap H.correctionSpace.correctionSpace
      H.energyBilin H.energyCoercive (H.constantField P0) by rfl]
  exact tendsto_of_quadraticEnergy_le_min_add_eps H.correctionSpace.correctionSpace
    H.energyCoercive H.energySymm (H.constantField P0) hmem heps hnear

/-- The doubled `Mu` minimizer on a general positive-volume open cell is strongly measurable in
any regular-field parameter whose supported smooth entry tests are measurable on one quantitative
ellipticity slice. -/
theorem stronglyMeasurable_responseCellMuMinimizer
    {Om : Type*} [mOm : MeasurableSpace Om] {U : Set (Vec d)} {k : ℕ}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤) (hvol : 0 < (volume U).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
        Measurable fun w ↦ entryTestR i j φ (A w))
    (P0 : BlockVec d) :
    StronglyMeasurable fun w : Om ↦
      (responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0 := by
  classical
  have hF := measurable_toHilbertMatrixL2_carrier (A := A) (hSlice := hSlice)
    hUopen.measurableSet hEntry hUopen hUfin
  let ξ : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U :=
    TopologicalSpace.denseSeq _
  let energy : Om → ℕ → ℝ := fun w n ↦
    blockEnergyAverage U (A w).toFun
      (canonicalMuGeneratorAffineField (U := U) P0 (ξ n))
  have henergyMeas : ∀ n : ℕ, Measurable fun w ↦ energy w n := by
    intro n
    exact measurable_blockEnergyAverage_carrier hF
      (canonicalMuGeneratorAffineField (U := U) P0 (ξ n))
      (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 (ξ n))
  have hMuEq : (fun w ↦ Mu U P0 (A w).toFun) = fun w ↦ ⨅ n : ℕ, energy w n := by
    funext w
    simpa [energy, ξ] using!
      Annealed.mu_eq_iInf_energy_for_responseSelection hvol k
        (responseSliceOf hSlice w) P0
  have hMuMeas : Measurable fun w ↦ Mu U P0 (A w).toFun := by
    rw [hMuEq]
    exact Measurable.iInf henergyMeas
  have hexists : ∀ m : ℕ, ∀ w : Om,
      ∃ n : ℕ, energy w n ≤ Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1) := by
    intro m w
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hlt : (⨅ n : ℕ, energy w n) <
        (⨅ n : ℕ, energy w n) + 1 / ((m : ℝ) + 1) :=
      lt_add_of_le_of_pos le_rfl hpos
    rcases exists_lt_of_ciInf_lt hlt with ⟨n, hn⟩
    refine ⟨n, le_of_lt ?_⟩
    rw [congrFun hMuEq w]
    exact hn
  let index : ℕ → Om → ℕ := fun m w ↦ Nat.find (hexists m w)
  have hgood : ∀ m n : ℕ,
      MeasurableSet {w : Om | energy w n ≤ Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1)} := by
    intro m n
    exact measurableSet_le (henergyMeas n) (hMuMeas.add measurable_const)
  have hindex : ∀ m : ℕ, Measurable (index m) := fun m ↦ by
    simpa [index] using measurable_find (hexists m) (hgood m)
  have happrox : ∀ m : ℕ, StronglyMeasurable fun w : Om ↦
      Selection.cellMuCandidate P0 (ξ (index m w)) := by
    intro m
    have hdisc : StronglyMeasurable fun n : ℕ ↦ Selection.cellMuCandidate P0 (ξ n) :=
      StronglyMeasurable.of_discrete
    simpa [Function.comp_def] using hdisc.comp_measurable (hindex m)
  refine stronglyMeasurable_of_tendsto atTop happrox ?_
  rw [tendsto_pi_nhds]
  intro w
  let a := responseSliceOf hSlice w
  let H := responseCellMuHilbert hvol a
  have hmem : ∀ m : ℕ,
      Selection.cellMuCandidate P0 (ξ (index m w)) - H.constantField P0 ∈
        H.correctionSpace.correctionSpace := fun m ↦
    responseCellMuCandidate_sub_constant_mem hvol a P0 (ξ (index m w))
  have heps : Tendsto (fun m : ℕ ↦ 1 / ((m : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hnear : ∀ m : ℕ,
      quadraticEnergy H.energyBilin (Selection.cellMuCandidate P0 (ξ (index m w))) ≤
        quadraticEnergy H.energyBilin (affineMinimizerMap H.correctionSpace.correctionSpace
          H.energyBilin H.energyCoercive (H.constantField P0)) + 1 / ((m : ℝ) + 1) := by
    intro m
    have hg := Nat.find_spec (hexists m w)
    have hqe := quadraticEnergy_responseCellMuCandidate hvol a P0 (ξ (index m w))
    have hmin := responseMu_eq_quadraticEnergy_minimizer hvol a P0
    calc
      quadraticEnergy H.energyBilin (Selection.cellMuCandidate P0 (ξ (index m w))) =
          energy w (index m w) := by simpa [H, a, energy]
      _ ≤ Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1) := hg
      _ = quadraticEnergy H.energyBilin
          (affineMinimizerMap H.correctionSpace.correctionSpace H.energyBilin
            H.energyCoercive (H.constantField P0)) + 1 / ((m : ℝ) + 1) := by
        simpa [H, a, responseSliceOf, MuHilbertRealization.minimizerMap,
          MuHilbertProblem.minimizerMap, parameterAffineMinimizerMap] using!
          congrArg (fun r : ℝ ↦ r + 1 / ((m : ℝ) + 1)) hmin
  change Tendsto (fun m : ℕ ↦ Selection.cellMuCandidate P0 (ξ (index m w))) atTop
    (𝓝 (H.minimizerMap P0))
  rw [show H.minimizerMap P0 = affineMinimizerMap H.correctionSpace.correctionSpace
      H.energyBilin H.energyCoercive (H.constantField P0) by rfl]
  exact tendsto_of_quadraticEnergy_le_min_add_eps H.correctionSpace.correctionSpace
    H.energyCoercive H.energySymm (H.constantField P0) hmem heps hnear

/-- Every fixed Hilbert-space coordinate of the general-cell minimizer is measurable. -/
theorem measurable_inner_responseCellMuMinimizer
    {Om : Type*} [mOm : MeasurableSpace Om] {U : Set (Vec d)} {k : ℕ}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤) (hvol : 0 < (volume U).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
        Measurable fun w ↦ entryTestR i j φ (A w))
    (P0 : BlockVec d) (y : HilbertBlockL2 U) :
    Measurable fun w : Om ↦ inner ℝ y
      ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0) := by
  have hstrong := stronglyMeasurable_responseCellMuMinimizer
    hUopen hUfin hvol hSlice hEntry P0
  have hcomp : StronglyMeasurable fun w : Om ↦ inner ℝ y
      ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0) := by
    simpa [Function.comp_def, innerSL_apply_apply] using
      (innerSL ℝ y).continuous.comp_stronglyMeasurable hstrong
  exact hcomp.measurable

/-- Continuous sample-dependent readouts transfer from fixed Galerkin competitors to the
response-cell minimizer. -/
theorem measurable_readout_responseCellMuMinimizer
    {Om : Type*} [mOm : MeasurableSpace Om] {U : Set (Vec d)} {k : ℕ}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤) (hvol : 0 < (volume U).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
        Measurable fun w ↦ entryTestR i j φ (A w))
    (P0 : BlockVec d) {R : Om → HilbertBlockL2 U → ℝ}
    (hRcont : ∀ w : Om, Continuous (R w))
    (hRmeas : ∀ Y : canonicalMuBlockCorrectionGeneratorSubmodule U,
      Measurable fun w : Om ↦ R w (Selection.cellMuCandidate P0 Y)) :
    Measurable fun w : Om ↦
      R w ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0) := by
  classical
  have hF := measurable_toHilbertMatrixL2_carrier (A := A) (hSlice := hSlice)
    hUopen.measurableSet hEntry hUopen hUfin
  let ξ : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U :=
    TopologicalSpace.denseSeq _
  let energy : Om → ℕ → ℝ := fun w n ↦ blockEnergyAverage U (A w).toFun
    (canonicalMuGeneratorAffineField (U := U) P0 (ξ n))
  have henergyMeas : ∀ n : ℕ, Measurable fun w ↦ energy w n := by
    intro n
    exact measurable_blockEnergyAverage_carrier hF
      (canonicalMuGeneratorAffineField (U := U) P0 (ξ n))
      (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 (ξ n))
  have hMuEq : (fun w ↦ Mu U P0 (A w).toFun) = fun w ↦ ⨅ n : ℕ, energy w n := by
    funext w
    simpa [energy, ξ] using!
      Annealed.mu_eq_iInf_energy_for_responseSelection hvol k
        (responseSliceOf hSlice w) P0
  have hMuMeas : Measurable fun w ↦ Mu U P0 (A w).toFun := by
    rw [hMuEq]
    exact Measurable.iInf henergyMeas
  have hexists : ∀ m : ℕ, ∀ w : Om,
      ∃ n : ℕ, energy w n ≤ Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1) := by
    intro m w
    have hlt : (⨅ n : ℕ, energy w n) <
        (⨅ n : ℕ, energy w n) + 1 / ((m : ℝ) + 1) := by
      exact lt_add_of_le_of_pos le_rfl (by positivity)
    rcases exists_lt_of_ciInf_lt hlt with ⟨n, hn⟩
    refine ⟨n, le_of_lt ?_⟩
    rw [congrFun hMuEq w]
    exact hn
  have hgood : ∀ m n : ℕ,
      MeasurableSet {w : Om | energy w n ≤ Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1)} := by
    intro m n
    exact measurableSet_le (henergyMeas n) (hMuMeas.add measurable_const)
  let index : ℕ → Om → ℕ := fun m w ↦ Nat.find (hexists m w)
  have hselected : ∀ m : ℕ, Measurable fun w : Om ↦
      R w (Selection.cellMuCandidate P0 (ξ (index m w))) := by
    intro m
    exact Measurable.find
      (f := fun n w ↦ R w (Selection.cellMuCandidate P0 (ξ n)))
      (fun n ↦ hRmeas (ξ n)) (hgood m) (hexists m)
  refine measurable_of_tendsto_metrizable hselected ?_
  rw [tendsto_pi_nhds]
  intro w
  exact (hRcont w).tendsto _ |>.comp
    (tendsto_responseCellMuCandidate_selected hvol hSlice P0 ξ index
      (fun m w ↦ Nat.find_spec (hexists m w)) w)

/-- The energy pairing against a fixed state, evaluated at a Galerkin competitor, is the
corresponding block pairing average. -/
theorem energyBilin_responseCellMuCandidate_eq_blockPairingAverage
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d)
    {Y : BlockState d} (hY : MemBlockL2 U Y.eval)
    (Z : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    (responseCellMuHilbert hvol a).energyBilin
        (toHilbertBlockL2OfBlockField (U := U) hY) (Selection.cellMuCandidate P0 Z) =
      blockPairingAverage U a.1 (canonicalMuGeneratorAffineField (U := U) P0 Z) Y := by
  rw [Selection.cellMuCandidate,
    ← canonicalMuGeneratorAffineField_hilbert_eq_const_add (U := U) P0 Z]
  simpa [responseCellMuHilbert, responseCellMuSystem,
    AEEMuOperatorSystemData.toMuHilbertRealization,
    MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
    (responseCellMuSystem hvol a).toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
      (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Z) hY

/-- The coefficient-dependent doubled energy pairing of the minimizer against a fixed block state
is measurable. -/
theorem measurable_energyBilin_responseCellMuMinimizer
    {Om : Type*} [mOm : MeasurableSpace Om] {U : Set (Vec d)} {k : ℕ}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤) (hvol : 0 < (volume U).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
        Measurable fun w ↦ entryTestR i j φ (A w))
    (P0 : BlockVec d) {Y : BlockState d} (hY : MemBlockL2 U Y.eval) :
    Measurable fun w : Om ↦
      (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
        (toHilbertBlockL2OfBlockField (U := U) hY)
        ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0) := by
  refine measurable_readout_responseCellMuMinimizer hUopen hUfin hvol hSlice hEntry P0
    (R := fun w z ↦ (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
      (toHilbertBlockL2OfBlockField (U := U) hY) z)
    (fun w ↦ ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
      (toHilbertBlockL2OfBlockField (U := U) hY)).continuous) ?_
  intro Z
  have heq : (fun w : Om ↦
      (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
        (toHilbertBlockL2OfBlockField (U := U) hY) (Selection.cellMuCandidate P0 Z)) =
      fun w ↦ blockPairingAverage U (A w).toFun
        (canonicalMuGeneratorAffineField (U := U) P0 Z) Y := by
    funext w
    exact energyBilin_responseCellMuCandidate_eq_blockPairingAverage
      hvol (responseSliceOf hSlice w) P0 hY Z
  rw [heq]
  exact Selection.measurable_blockPairingAverage_of_measurable_entryTest hUopen hUfin hSlice hEntry _ Y
    (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Z) hY

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Recovery of the canonical response optimizer from the doubled minimizer
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The complete doubled state of the Chapter-2 canonical response maximizer. -/
@[expose]
def canonicalOptimizerBlockState (U : Book.Ch02.Domain d) (aU : Book.Ch02.CoeffOn U)
    (p q : Vec d) : Vec d → BlockVec d := fun x ↦
  let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U aU) p q).toSolution
  (v.toH1.grad x, matVecMul (aU.toCoeffField x) (v.toH1.grad x))

/-- A weighted coordinate readout of the canonical optimizer state. -/
@[expose]
def canonicalOptimizerStateReadout (U : Book.Ch02.Domain d) (aU : Book.Ch02.CoeffOn U)
    (p q : Vec d) (α : BlockCoord d) (η : Vec d → ℝ) : ℝ :=
  ∫ x in (U : Set (Vec d)), η x *
    toFullBlockVec (canonicalOptimizerBlockState U aU p q x) α ∂volume

theorem canonicalOptimizerStateReadout_congr {U : Book.Ch02.Domain d}
    {aU bU : Book.Ch02.CoeffOn U} (h : Book.Ch02.CoeffOn.AEEq aU bU)
    (p q : Vec d) (α : BlockCoord d) (η : Vec d → ℝ) :
    canonicalOptimizerStateReadout U aU p q α η =
      canonicalOptimizerStateReadout U bU p q α η := by
  have hgrad := Book.Ch02.canonicalMaximizer_sameGradientAE_ofAEEq h p q
  refine integral_congr_ae ?_
  filter_upwards [hgrad, h] with x hx hax
  have hx' :
      (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U aU) p
        q).toSolution.toH1.grad x =
      (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U bU) p
        q).toSolution.toH1.grad x := hx
  have hstate : canonicalOptimizerBlockState U aU p q x =
      canonicalOptimizerBlockState U bU p q x := by
    simp only [canonicalOptimizerBlockState, hx', hax]
  rw [hstate]

/-- A regular field on a quantitative slice, packaged as a Chapter-2 coefficient object. -/
@[expose]
def responseCoeffOnOfSlice (U : Book.Ch02.Domain d) {k : ℕ} (A : RegCoeffField d)
    (hk : AEEQuantitativeEllipticSlice (U : Set (Vec d)) k A.toFun) : Book.Ch02.CoeffOn U where
  toCoeffField := A.toFun
  lam := ((k + 1 : ℝ)⁻¹)
  Lam := k + 1
  lam_pos := inv_pos.mpr (by positivity)
  lam_le_Lam := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith only [hk0]
    exact le_trans ((inv_le_one₀ (by positivity)).2 h) h
  aeStronglyMeasurable := hk.2.1
  aeElliptic := hk.2.2

private theorem isPotentialZeroTraceOn_of_book
    {U : Set (Vec d)} {f : Vec d → Vec d} (hf : Book.Ch01.PotentialZeroTraceFieldOn U f) :
    IsPotentialZeroTraceOn U f := by
  rcases hf with ⟨_, φ, hφ⟩
  exact IsPotentialZeroTraceOn.congr_ae hφ.symm φ.isPotentialZeroTraceOn

/-- A pointwise Chapter-2 doubled minimizer represents the same Hilbert minimizer selected by the
general-cell Galerkin construction. -/
theorem toHilbertBlockL2_eq_responseMinimizer_of_isDoubledMuMinimizer
    {U : Book.Ch02.Domain d} [IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))]
    {k : ℕ} (hvol : 0 < (volume (U : Set (Vec d))).toReal) {aU : Book.Ch02.CoeffOn U}
    (hk : AEEQuantitativeEllipticSlice (U : Set (Vec d)) k aU.toCoeffField)
    (P0 : BlockVec d) {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuMinimizer U aU P0 X)
    (hAdm : IsBlockMuAdmissible (U : Set (Vec d)) P0
      ({ potential := X.potential, flux := X.flux } : BlockState d)) :
    toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hAdm.memBlockL2_eval =
      (responseCellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).minimizerMap P0 := by
  let a : {b : CoeffField d // AEEQuantitativeEllipticSlice (U : Set (Vec d)) k b} :=
    ⟨aU.toCoeffField, hk⟩
  let H := responseCellMuHilbert hvol a
  have hEnergy : blockEnergyAverage (U : Set (Vec d)) aU.toCoeffField
      ({ potential := X.potential, flux := X.flux } : BlockState d) =
        Mu (U : Set (Vec d)) P0 aU.toCoeffField := by
    calc
      blockEnergyAverage (U : Set (Vec d)) aU.toCoeffField
          ({ potential := X.potential, flux := X.flux } : BlockState d) =
          Book.Ch02.doubledMuValue U aU X := rfl
      _ = Book.Ch02.doubledMu U aU P0 := hX.doubledMuValue_eq_doubledMu
      _ = Mu (U : Set (Vec d)) P0 aU.toCoeffField := Book.Ch02.doubledMu_eq_Mu U aU P0
  have hcorr : toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
        hAdm.memBlockL2_eval - H.constantField P0 ∈ H.correctionSpace.correctionSpace := by
    rw [show H.correctionSpace = MuCorrectionSpaceData.ofSubmoduleClosures (U : Set (Vec d)) by
        exact correctionSpace_responseCellMuHilbert hvol a,
      show H.constantField = blockVecToHilbertBlockL2Const (U := (U : Set (Vec d))) by
        exact constantField_responseCellMuHilbert hvol a,
      hAdm.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add,
      add_sub_cancel_left]
    exact hAdm.toCorrectionFieldData_mem_correctionSpace
  have hQuad : quadraticEnergy H.energyBilin
      (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hAdm.memBlockL2_eval) =
        Mu (U : Set (Vec d)) P0 aU.toCoeffField := by
    rw [← hEnergy]
    simpa [H, a, responseCellMuHilbert, responseCellMuSystem,
      AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
      (responseCellMuSystem hvol a).toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
        hAdm.memBlockL2_eval
  refine H.eq_minimizerMap_of_quadraticEnergy_le_muCandidate P0 _ hcorr (le_of_eq ?_)
  rw [hQuad]
  simpa [H, MuHilbertRealization.muCandidate, MuHilbertProblem.muCandidate,
    MuHilbertRealization.minimizerMap, MuHilbertProblem.minimizerMap,
    parameterAffineMinimizerMap] using! responseMu_eq_quadraticEnergy_minimizer hvol a P0

/-- Coordinatewise a.e. recovery of the canonical optimizer's complete doubled state. -/
theorem ae_toFullBlockVec_canonicalOptimizerBlockState
    {U : Book.Ch02.Domain d} {aU : Book.Ch02.CoeffOn U} (p q : Vec d)
    (α : BlockCoord d) {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuMinimizer U aU (-p, q) X) :
    (fun x ↦ toFullBlockVec (canonicalOptimizerBlockState U aU p q x) α)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    fun x ↦ toFullBlockVec (X.eval x) α +
      toFullBlockVec (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x))
        α.swap := by
  cases α with
  | inl i =>
      filter_upwards
        [Book.Ch02.doubledMuMinimizer_neg_left_extracts_canonicalMaximizerGradient U aU p q hX]
        with x hx
      show (canonicalOptimizerBlockState U aU p q x).1 i = _
      rw [canonicalOptimizerBlockState, ← hx]
      rfl
  | inr i =>
      filter_upwards
        [Book.Ch02.doubledMuMinimizer_neg_left_extracts_canonicalMaximizerFlux U aU p q hX]
        with x hx
      show (canonicalOptimizerBlockState U aU p q x).2 i = _
      rw [canonicalOptimizerBlockState, ← hx]
      rfl

/-- Weighted coordinates of the canonical optimizer are the sum of an inner-product readout and
an energy-bilinear readout of the doubled minimizer. -/
theorem integral_weighted_canonicalOptimizerBlockState
    {U : Book.Ch02.Domain d} [IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))]
    {k : ℕ} (hvol : 0 < (volume (U : Set (Vec d))).toReal) {aU : Book.Ch02.CoeffOn U}
    (hk : AEEQuantitativeEllipticSlice (U : Set (Vec d)) k aU.toCoeffField)
    (p q : Vec d) (α : BlockCoord d) {η : Vec d → ℝ}
    (hη : MemScalarL2 (U : Set (Vec d)) η) :
    ∫ x in (U : Set (Vec d)), η x *
        toFullBlockVec (canonicalOptimizerBlockState U aU p q x) α ∂volume =
      inner ℝ
          (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
            (Selection.blockTestState_memBlockL2 hη α))
          ((responseCellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).minimizerMap (-p, q)) +
        (volume (U : Set (Vec d))).toReal *
          (responseCellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).energyBilin
            (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
              (Selection.blockTestState_memBlockL2 hη α.swap))
            ((responseCellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).minimizerMap (-p, q)) := by
  classical
  obtain ⟨X, hX⟩ := (Book.Ch02.doubledMuTheory U aU).minimizer_exists (-p, q)
  have hAdm : IsBlockMuAdmissible (U : Set (Vec d)) (-p, q)
      ({ potential := X.potential, flux := X.flux } : BlockState d) :=
    Selection.isBlockMuAdmissible_of_isDoubledMuAdmissible hX.1
  have hXmem := hAdm.memBlockL2_eval
  have hMin := toHilbertBlockL2_eq_responseMinimizer_of_isDoubledMuMinimizer
    hvol hk (-p, q) hX hAdm
  have hstate := ae_toFullBlockVec_canonicalOptimizerBlockState (aU := aU) p q α hX
  have hcoord : MemScalarL2 (U : Set (Vec d)) (fun x ↦ toFullBlockVec
      (({ potential := X.potential, flux := X.flux } : BlockState d).eval x) α) :=
    memScalarL2_fullBlockCoord_of_memBlockL2 hXmem α
  have hint1 : IntegrableOn (fun x ↦ η x * toFullBlockVec (X.eval x) α)
      (U : Set (Vec d)) := MeasureTheory.MemLp.integrable_mul hη hcoord
  have hpairing := Selection.integrableOn_blockPairingIntegrand_of_slice hk
    (Selection.blockTestState_memBlockL2 hη α.swap) hXmem
  have hpairEq : blockPairingIntegrand aU.toCoeffField (Selection.blockTestState η α.swap)
      ({ potential := X.potential, flux := X.flux } : BlockState d) = fun x ↦
        η x * toFullBlockVec
          (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)) α.swap := by
    funext x
    exact Selection.blockVecDot_blockTestState η α.swap _ x
  have hint2 : IntegrableOn (fun x ↦ η x * toFullBlockVec
      (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)) α.swap)
      (U : Set (Vec d)) := by simpa [hpairEq] using hpairing
  have hsplit : ∫ x in (U : Set (Vec d)), η x *
        toFullBlockVec (canonicalOptimizerBlockState U aU p q x) α ∂volume =
      (∫ x in (U : Set (Vec d)), η x * toFullBlockVec (X.eval x) α ∂volume) +
      ∫ x in (U : Set (Vec d)), η x * toFullBlockVec
        (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)) α.swap ∂volume := by
    rw [← integral_add hint1 hint2]
    refine integral_congr_ae ?_
    filter_upwards [hstate] with x hx
    rw [hx, mul_add]
  rw [hsplit]
  congr 1
  · rw [← hMin, Selection.inner_toHilbertBlockL2OfBlockField_eq_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    exact (Selection.blockVecDot_blockTestState η α
      (({ potential := X.potential, flux := X.flux } : BlockState d).eval x) x).symm
  · have hbil :
        (responseCellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).energyBilin
            (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
              (Selection.blockTestState_memBlockL2 hη α.swap))
            ((responseCellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).minimizerMap (-p, q)) =
          blockPairingAverage (U : Set (Vec d)) aU.toCoeffField
            (Selection.blockTestState η α.swap)
            ({ potential := X.potential, flux := X.flux } : BlockState d) := by
      rw [← hMin, (responseCellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).energySymm]
      simpa [responseCellMuHilbert, responseCellMuSystem,
        AEEMuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
        (responseCellMuSystem hvol ⟨aU.toCoeffField, hk⟩).toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
          (Selection.blockTestState_memBlockL2 hη α.swap) hXmem
    rw [hbil, blockPairingAverage, volumeAverage, hpairEq, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hvol), one_mul]

/-- Weighted coordinate readouts of the canonical optimizer are measurable on one quantitative
ellipticity slice of a general response cell. -/
theorem measurable_integral_weighted_canonicalOptimizerBlockState
    {Om : Type*} [mOm : MeasurableSpace Om] {U : Book.Ch02.Domain d}
    [IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))] {k : ℕ}
    (hUopen : IsOpen (U : Set (Vec d))) (hUfin : volume (U : Set (Vec d)) ≠ ⊤)
    (hvol : 0 < (volume (U : Set (Vec d))).toReal) {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice (U : Set (Vec d)) k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ (U : Set (Vec d)) →
        Measurable fun w ↦ entryTestR i j φ (A w))
    (aU : Om → Book.Ch02.CoeffOn U) (haU : ∀ w : Om, (aU w).toCoeffField = (A w).toFun)
    (p q : Vec d) (α : BlockCoord d) {η : Vec d → ℝ}
    (hη : MemScalarL2 (U : Set (Vec d)) η) :
    Measurable fun w : Om ↦ ∫ x in (U : Set (Vec d)), η x *
      toFullBlockVec (canonicalOptimizerBlockState U (aU w) p q x) α ∂volume := by
  have hk : ∀ w : Om,
      AEEQuantitativeEllipticSlice (U : Set (Vec d)) k (aU w).toCoeffField := by
    intro w
    rw [haU w]
    exact hSlice w
  have hEqSlice : ∀ w : Om,
      (⟨(aU w).toCoeffField, hk w⟩ :
        {b : CoeffField d // AEEQuantitativeEllipticSlice (U : Set (Vec d)) k b}) =
      responseSliceOf hSlice w := fun w ↦ Subtype.ext (haU w)
  have heq : (fun w : Om ↦ ∫ x in (U : Set (Vec d)), η x *
      toFullBlockVec (canonicalOptimizerBlockState U (aU w) p q x) α ∂volume) =
      fun w ↦
        inner ℝ
            (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
              (Selection.blockTestState_memBlockL2 hη α))
            ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap (-p, q)) +
          (volume (U : Set (Vec d))).toReal *
            (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
              (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
                (Selection.blockTestState_memBlockL2 hη α.swap))
              ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap (-p, q)) := by
    funext w
    rw [integral_weighted_canonicalOptimizerBlockState hvol (hk w) p q α hη,
      hEqSlice w]
  rw [heq]
  exact (measurable_inner_responseCellMuMinimizer hUopen hUfin hvol hSlice hEntry (-p, q) _).add
    ((measurable_energyBilin_responseCellMuMinimizer hUopen hUfin hvol hSlice hEntry
      (-p, q) (Selection.blockTestState_memBlockL2 hη α.swap)).const_mul _)
end

end HCPolySupport.HighContrast.Multiscale
end
