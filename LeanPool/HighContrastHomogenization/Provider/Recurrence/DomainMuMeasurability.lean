/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Annealed.Measurability
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.MuOperator.AEEOperator.CanonicalCubeSet
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.MuRecovery.CorrectionSpaceEnergy
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Internal.AEESliceAssembly.CarrierMuFamily

/-!
# High-contrast homogenization: Provider.Recurrence.DomainMuMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coarse-grained energy of a general cell, as a countable infimum

The measurability among the coarse-block properties taken from HC is asked of
the coarse response on a Lipschitz cell.  CoarseGraining proves the variational quantity
`μ(U, P; ·)` measurable only when `U` is a triadic cube; the obstruction is not
mathematical but bookkeeping — the two facts its cube proof rests on are stated
at `cubeSet Q` although their proofs never use anything but finiteness and
positivity of the volume of `U`.  This file transports those two facts to an
arbitrary cell, so that the measurability clause becomes available on
every bounded open cell of positive volume, the adapted cells among them.

The first is the identification of the variational quantity with the value of
the Hilbert minimization problem attached to the canonical potential/solenoidal
correction space: both are the infimum of the same block energies, one over the
admissible block states and one over the dense generator submodule.

The second is the resulting countable presentation
`μ(U, P; a) = inf_n E(U, a; X_n)` along a dense sequence of *fixed* smooth
generators — fixed meaning independent of the coefficient field.  Measurability
of `μ` is then measurability of each fixed-competitor energy, which is
CoarseGraining's carrier machinery and is already stated on an arbitrary cell.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The variational quantity is the Hilbert candidate -/

/-- **The variational quantity of an arbitrary cell of positive finite volume is
the canonical Hilbert candidate.**  The candidate is at most every admissible
block energy, so it is at most `μ`; and the generator submodule is dense in the
correction space and its affine fields are admissible, so `μ` is at most the
candidate.  This is CoarseGraining's cube statement with the cube removed. -/
theorem mu_eq_aeeMuCandidate {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ} {a : CoeffField d} (hAEE : IsAEEllipticFieldOn lam Lam U a)
    (hvol : 0 < (volume U).toReal) (P0 : BlockVec d) :
    Mu U P0 a =
      (((PotentialSolenoidalL2Data.ofSubmoduleClosures U).toAEEMuOperatorSystemData
          (AEEMuCoeffOperatorData.ofIsAEEllipticFieldOn hAEE
            hvol)).toMuHilbertRealization).muCandidate
        P0 := by
  let system : AEEMuOperatorSystemData U a :=
    (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toAEEMuOperatorSystemData
      (AEEMuCoeffOperatorData.ofIsAEEllipticFieldOn hAEE hvol)
  let H : MuHilbertRealization U a := system.toMuHilbertRealization
  let gen : canonicalMuBlockCorrectionGeneratorSubmodule U →
      H.correctionSpace.correctionSpace.toSubmodule :=
    canonicalMuCorrectionGeneratorEmbedding U
  let s : Set ℝ := Set.range fun Y : canonicalMuBlockCorrectionGeneratorSubmodule U =>
    quadraticEnergy H.energyBilin (H.constantField P0 + (gen Y : HilbertBlockL2 U))
  have hgen_dense : DenseRange gen := by
    dsimp [gen, H, system]
    exact denseRange_canonicalMuCorrectionGeneratorEmbedding U
  have hCandidate_sInf : H.muCandidate P0 = sInf s := by
    simpa [s] using H.muCandidate_eq_sInf_quadraticEnergy_denseRange P0 gen hgen_dense
  have hCandidateLe :
      ∀ X : BlockState d, IsBlockMuAdmissible U P0 X →
        H.muCandidate P0 ≤ blockEnergyAverage U a X := by
    intro X hX
    have hXmem : MemBlockL2 U X.eval := hX.memBlockL2_eval
    have hcorr_mem :
        toHilbertBlockL2OfBlockField (U := U) hXmem - H.constantField P0 ∈
          H.correctionSpace.correctionSpace := by
      have hsplit := hX.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
      rw [hsplit]
      have hcorr := hX.toCorrectionFieldData_mem_correctionSpace
      simpa [H, system, PotentialSolenoidalL2Data.toAEEMuOperatorSystemData,
        MuCorrectionSpaceData.ofSubmoduleClosures,
        AEEMuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
        sub_eq_add_neg, add_assoc, add_comm] using hcorr
    have hmin :
        H.muCandidate P0 ≤
          quadraticEnergy H.energyBilin (toHilbertBlockL2OfBlockField (U := U) hXmem) :=
      H.muCandidate_le_quadraticEnergy P0
        (toHilbertBlockL2OfBlockField (U := U) hXmem) hcorr_mem
    calc
      H.muCandidate P0 ≤
          quadraticEnergy H.energyBilin (toHilbertBlockL2OfBlockField (U := U) hXmem) := hmin
      _ = blockEnergyAverage U a X := by
        simpa [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
          MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
          system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
            (X := X) hXmem
  have hBddBelow : BddBelow (muValueSet U P0 a) := by
    refine ⟨H.muCandidate P0, ?_⟩
    intro m hm
    rcases hm with ⟨X, hX, rfl⟩
    simpa [blockEnergyAverage] using hCandidateLe X hX
  have hCandidate_le_Mu : H.muCandidate P0 ≤ Mu U P0 a := by
    apply le_Mu_of_forall_isBlockMuAdmissible
    intro X hX
    simpa [blockEnergyAverage] using hCandidateLe X hX
  have hEnergyGen : ∀ Y : canonicalMuBlockCorrectionGeneratorSubmodule U,
      quadraticEnergy H.energyBilin (H.constantField P0 + (gen Y : HilbertBlockL2 U)) =
        blockEnergyAverage U a (canonicalMuGeneratorAffineField (U := U) P0 Y) := by
    intro Y
    have hsplit :
        toHilbertBlockL2OfBlockField (U := U)
            (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Y) =
          H.constantField P0 + (gen Y : HilbertBlockL2 U) := by
      simpa [gen, H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
        canonicalMuGeneratorAffineField_hilbert_eq_const_add (U := U) P0 Y
    rw [← hsplit]
    simpa [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
      system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
        (X := canonicalMuGeneratorAffineField (U := U) P0 Y)
        (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Y)
  have hs_subset_mu : s ⊆ muValueSet U P0 a := by
    rintro m ⟨Y, rfl⟩
    change quadraticEnergy H.energyBilin (H.constantField P0 + (gen Y : HilbertBlockL2 U))
      ∈ muValueSet U P0 a
    rw [hEnergyGen Y]
    simpa [blockEnergyAverage] using
      muValueSet_mem (a := a) (canonicalMuGeneratorAffineField_admissible (U := U) P0 Y)
  have hs_nonempty : s.Nonempty :=
    ⟨quadraticEnergy H.energyBilin (H.constantField P0 + (gen 0 : HilbertBlockL2 U)), ⟨0, rfl⟩⟩
  have hMu_le_sInf : Mu U P0 a ≤ sInf s :=
    le_csInf hs_nonempty fun m hm => csInf_le hBddBelow (hs_subset_mu hm)
  have hMu_le_candidate : Mu U P0 a ≤ H.muCandidate P0 := by
    rw [hCandidate_sInf]
    exact hMu_le_sInf
  exact le_antisymm hMu_le_candidate hCandidate_le_Mu

/-! ## The countable presentation along a dense generator sequence -/

/-- **The variational quantity of an arbitrary cell is the infimum of the block
energies of a fixed dense sequence of smooth generators.**  The sequence does
not depend on the coefficient field, which is what makes the presentation a
measurability tool. -/
theorem mu_eq_iInf_blockEnergyAverage {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] {lam Lam : ℝ} {a : CoeffField d}
    (hAEE : IsAEEllipticFieldOn lam Lam U a) (hvol : 0 < (volume U).toReal)
    (P0 : BlockVec d) (xi : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U)
    (hxi : DenseRange xi) :
    Mu U P0 a =
      ⨅ n : ℕ, blockEnergyAverage U a (canonicalMuGeneratorAffineField (U := U) P0 (xi n)) := by
  let system : AEEMuOperatorSystemData U a :=
    (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toAEEMuOperatorSystemData
      (AEEMuCoeffOperatorData.ofIsAEEllipticFieldOn hAEE hvol)
  let H : MuHilbertRealization U a := system.toMuHilbertRealization
  let gen : ℕ → H.correctionSpace.correctionSpace.toSubmodule := fun n =>
    canonicalMuCorrectionGeneratorEmbedding U (xi n)
  have hgen_dense : DenseRange gen := by
    have hcomp : DenseRange (canonicalMuCorrectionGeneratorEmbedding U ∘ xi) :=
      DenseRange.comp (g := canonicalMuCorrectionGeneratorEmbedding U) (f := xi)
        (denseRange_canonicalMuCorrectionGeneratorEmbedding U) hxi
        (continuous_canonicalMuCorrectionGeneratorEmbedding U)
    dsimp [gen, H, system]
    exact hcomp
  have hCandidate : H.muCandidate P0 =
      sInf (Set.range fun n : ℕ =>
        quadraticEnergy H.energyBilin (H.constantField P0 + (gen n : HilbertBlockL2 U))) := by
    simpa using H.muCandidate_eq_sInf_quadraticEnergy_denseRange P0 gen hgen_dense
  have hEnergy : ∀ n : ℕ,
      quadraticEnergy H.energyBilin (H.constantField P0 + (gen n : HilbertBlockL2 U)) =
        blockEnergyAverage U a (canonicalMuGeneratorAffineField (U := U) P0 (xi n)) := by
    intro n
    have hsplit :
        toHilbertBlockL2OfBlockField (U := U)
            (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 (xi n)) =
          H.constantField P0 + (gen n : HilbertBlockL2 U) := by
      simpa [gen, H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
        canonicalMuGeneratorAffineField_hilbert_eq_const_add (U := U) P0 (xi n)
    rw [← hsplit]
    simpa [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
      system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
        (X := canonicalMuGeneratorAffineField (U := U) P0 (xi n))
        (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 (xi n))
  calc Mu U P0 a = H.muCandidate P0 := mu_eq_aeeMuCandidate hAEE hvol P0
    _ = ⨅ n : ℕ,
          quadraticEnergy H.energyBilin (H.constantField P0 + (gen n : HilbertBlockL2 U)) := by
        rw [hCandidate, sInf_range]
    _ = ⨅ n : ℕ,
          blockEnergyAverage U a (canonicalMuGeneratorAffineField (U := U) P0 (xi n)) :=
        iInf_congr hEnergy

/-! ## The measurability engine on a general cell -/

/-- **The coarse-grained energy of a general bounded open cell is measurable in
the coefficient field**, for any parameter space whose localized smooth entry
tests are measurable and whose fields all lie in one quantitative ellipticity
slice of the cell.  This is CoarseGraining's carrier `Mu` engine with the cube
removed: the countable presentation replaces `μ` by an infimum of fixed
competitor energies, and each of those is measurable by the carrier's `L²`
realization. -/
theorem measurable_Mu_of_measurable_entryTest {Om : Type*} [mOm : MeasurableSpace Om]
    {U : Set (Vec d)} {k : ℕ} [IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤) (hvol : 0 < (volume U).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U → Measurable fun w => entryTestR i j φ (A w))
    (P0 : BlockVec d) :
    Measurable fun w => Mu U P0 (A w).toFun := by
  classical
  have : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  have hRewrite : (fun w => Mu U P0 (A w).toFun)
      = fun w => ⨅ n : ℕ, blockEnergyAverage U (A w).toFun
          (canonicalMuGeneratorAffineField (U := U) P0
            (TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule U) n)) := by
    funext w
    exact mu_eq_iInf_blockEnergyAverage (hSlice w) hvol P0 _
      (TopologicalSpace.denseRange_denseSeq _)
  rw [hRewrite]
  refine Measurable.iInf fun n => ?_
  refine measurable_blockEnergyAverage_carrier (hSlice := hSlice) ?_ _
    (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 _)
  let : MeasurableSpace (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)) := borel _
  have : BorelSpace (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)) := ⟨rfl⟩
  obtain ⟨u, hu, hSmooth⟩ := exists_dense_smoothProbeSequence_of_dense_smoothProbeSet (U := U)
    (dense_smoothCompactSupportHilbertMatrixL2_tsupport_subset hUopen hUfin)
  refine measurable_of_measurable_inner_denseRange_polish u hu fun n' => ?_
  rcases hSmooth n' with ⟨g, hgL2, hEqn, hg_cont, hg_compact, hg_support⟩
  rw [hEqn]
  exact measurable_inner_hilbertMatrixSmoothProbe_toHilbertMatrixL2_carrier
    (mΩ := mOm) hUopen.measurableSet hEntry hgL2 hg_cont hg_compact hg_support

/-! ## From the variational quantity to the coarse response -/

/-- Every entry of the coarse block response is measurable once the variational
quantity is: the entries are the polarizations of `μ(U, ·; a)` at the doubled
vectors built from a pair of basis directions.  The sigma-field is arbitrary, so
the reduction serves both the global sigma-field of the coefficient space and
the local one of the cell. -/
theorem measurable_blockMatEntry_coarseBlock_of_measurable_Mu
    {m : MeasurableSpace (CoeffSpace d)} {U : Set (Vec d)}
    (hMu : ∀ Q : BlockVec d,
      @Measurable (CoeffSpace d) ℝ m _ fun a => Mu U Q (⇑a.1 : CoeffField d))
    (α β : BlockCoord d) :
    @Measurable (CoeffSpace d) ℝ m _ fun a => blockMatEntry (coarseBlock U a) α β := by
  let : MeasurableSpace (CoeffSpace d) := m
  simp only [coarseBlock, blockMatEntry_coarseBlockMatrix]
  by_cases h : α = β
  · simp only [ite_eq_left h]
    exact (hMu (blockBasis α)).const_mul 2
  · simp only [ite_eq_right h]
    exact ((hMu (blockBasis α + blockBasis β)).sub (hMu (blockBasis α))).sub
      (hMu (blockBasis β))

/-- **The measurability of the variational coarse block**, on an arbitrary
cell and for every law at once, reduced to the measurability of the variational
quantity. -/
theorem hasMeasurableCoarseBlock_of_measurable_Mu (P : Measure (CoeffSpace d))
    {U : Set (Vec d)}
    (hMu : ∀ Q : BlockVec d,
      Measurable fun a : CoeffSpace d => Mu U Q (⇑a.1 : CoeffField d)) :
    HasMeasurableCoarseBlock P U :=
  fun α β =>
    (measurable_blockMatEntry_coarseBlock_of_measurable_Mu hMu α β).aestronglyMeasurable

end

end Recurrence
end HighContrast
end HCPolySupport
