/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedDomainLocality
public import LeanPool.HighContrastHomogenization.Entry.Geometry.AdaptedCell
public import LeanPool.HighContrastHomogenization.Entry.Geometry.StandardCell
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Setup.LocalSigmaFields
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockMatrixProperties
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.CoarseBounds
public import LeanPool.HighContrastHomogenization.Setup.Response
public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.Translation
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Internal.AEESliceAssembly.CarrierMuFamily
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyLayer

/-!
# High-contrast homogenization: Entry.Annealed.AdaptedLocality

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local measurability and covariance of adapted coarse blocks

The coarse block is recovered by polarization of CG's `Mu`. We adapt
CG's Chapter 4 smooth-test route: approximate compact ball indicators by smooth
cutoffs, prove measurable ellipticity slices, and realize the coefficient field
in `L²` from the supported generating statistics. On each slice, `Mu` is the
infimum of energies along a countable dense family of admissible corrections.
The slice cover includes every coefficient field, giving strict local
measurability without a law premise or a uniform ellipticity bound.

The helpers below extend the open-set part of CG's
`Probability/RegCoeffField/SmoothSliceMeasurability.lean` and the countable
variational argument of `CoarseGraining/MuOperator/AEEOperator/CanonicalCubeSet.lean`.
The regular-carrier map and its sigma-algebra comparison are proved below.
No adapted-domain recovery or identification with an AKL fixed-Θ law is used.

Source: near `e.coarse.ellipticity`, `e.rounded.grid.bounds`, `e.fixed.geometry.parent.child`;
qualitative local
ellipticity is assumed.
-/

open HCPolySupport.HighContrast (CoeffSpace IsLocalTest
  ae_abs_entry_le_of_aeUniformlyEllipticField blockMatEntry_coarseBlockMatrix coarseBlock
  coarseBlock_eq_of_ae_eq coeffPairing coeffSigma translateCoeff)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory Metric Filter Topology
open scoped Manifold
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

private theorem adaptedCellTranslate_translateSet {d : ℕ} (q : Mat d) (j : ℤ)
    (y z : Vec d) :
    HighContrast.adaptedCellTranslate q j (y + z) =
      translateSet z (HighContrast.adaptedCellTranslate q j y) := by
  ext x
  constructor
  · rw [Geometry.mem_adaptedCellTranslate_iff]
    rintro ⟨v, hv, rfl⟩
    rw [mem_translateSet_iff_sub_mem, Geometry.mem_adaptedCellTranslate_iff]
    refine ⟨v, hv, ?_⟩
    abel
  · rw [mem_translateSet_iff_sub_mem, Geometry.mem_adaptedCellTranslate_iff]
    rintro ⟨v, hv, hvx⟩
    rw [Geometry.mem_adaptedCellTranslate_iff]
    refine ⟨v, hv, ?_⟩
    ext i
    have hi := congrFun hvx i
    simp only [Pi.add_apply, Pi.sub_apply] at hi ⊢
    linarith only [hi]

private theorem coarseBlock_translateCoeff_eq_translateSet {d : ℕ}
    (U : Set (Vec d)) (z : Fin d → ℤ) (a : CoeffSpace d) :
    coarseBlock U (translateCoeff z a) =
      coarseBlock (translateSet (Source.AKL.intTranslation z) U) a := by
  calc
    coarseBlock U (translateCoeff z a)
        = coarseBlockMatrix U
            (translateCoeffField (Source.AKL.intTranslation z) (⇑a.1)) := by
          simpa [translateCoeffField] using!
            (coarseBlock_eq_of_ae_eq (U := U) (translateCoeff z a)
              (Source.AKL.translateField_ae z a.1))
    _ = coarseBlockMatrix (translateSet (Source.AKL.intTranslation z) U) (⇑a.1) := by
          exact (coarseBlockMatrix_translateSet_eq_translateCoeffField
            (Source.AKL.intTranslation z) U (⇑a.1)).symm
    _ = coarseBlock (translateSet (Source.AKL.intTranslation z) U) a := rfl

theorem coarseBlock_adapted_translateCoeff
    {d : ℕ} (q : Mat d) (j : ℤ) (y : Vec d) (z : Fin d → ℤ) (a : CoeffSpace d) :
    coarseBlock (HighContrast.adaptedCellTranslate q j y) (translateCoeff z a) =
    coarseBlock (HighContrast.adaptedCellTranslate q j (y + Source.AKL.intTranslation z)) a := by
  calc
    coarseBlock (HighContrast.adaptedCellTranslate q j y) (translateCoeff z a)
        = coarseBlock (translateSet (Source.AKL.intTranslation z)
            (HighContrast.adaptedCellTranslate q j y)) a :=
          coarseBlock_translateCoeff_eq_translateSet
            (HighContrast.adaptedCellTranslate q j y) z a
    _ = coarseBlock (HighContrast.adaptedCellTranslate q j
            (y + Source.AKL.intTranslation z)) a := by
          rw [adaptedCellTranslate_translateSet]

variable {d : ℕ}

private theorem exists_smooth_cutoff_seq {U B : Set (Vec d)}
    (hUopen : IsOpen U) (hBcpt : IsCompact B) (hBU : B ⊆ U) :
    ∃ K : Set (Vec d), ∃ ψ : ℕ → Vec d → ℝ,
      IsCompact K ∧ K ⊆ U ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) ∧ HasCompactSupport (ψ n) ∧
        tsupport (ψ n) ⊆ U ∧ Function.support (ψ n) ⊆ K ∧
          ∀ x, ψ n x ∈ Set.Icc 0 1) ∧
      ∀ x, Tendsto (fun n => ψ n x) atTop
        (𝓝 (Set.indicator B (fun _ => (1 : ℝ)) x)) := by
  classical
  obtain ⟨ε, hεpos, hεU⟩ := hBcpt.exists_cthickening_subset_open hUopen hBU
  let δ : ℕ → ℝ := fun n => ε / (n + 1)
  have hδpos : ∀ n, 0 < δ n := fun n => by
    dsimp [δ]
    positivity
  have hδle : ∀ n, δ n ≤ ε := fun n => by
    dsimp [δ]
    have hn : 1 ≤ (n : ℝ) + 1 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith only [hn0]
    calc
      ε / ((n : ℝ) + 1) ≤ ε / 1 := by
        exact div_le_div_of_nonneg_left hεpos.le (by positivity) hn
      _ = ε := by rw [div_one]
  have hBint : ∀ n, B ⊆ interior (cthickening (δ n) B) := fun n =>
    (self_subset_thickening (hδpos n) B).trans
      (thickening_subset_interior_cthickening (δ n) B)
  choose ψ hψone hψzero hψrange using fun n =>
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, Vec d)) (n := (⊤ : ℕ∞))
      hBcpt.isClosed (hBint n)
  let ψ' : ℕ → Vec d → ℝ := fun n => ψ n
  let K : Set (Vec d) := cthickening ε B
  refine ⟨K, ψ', hBcpt.cthickening, hεU, ?_, ?_⟩
  · intro n
    have hTsub : cthickening (δ n) B ⊆ K :=
      cthickening_mono (hδle n) B
    have hsupp : Function.support (ψ' n) ⊆ cthickening (δ n) B := by
      intro x hx
      by_contra hxT
      exact hx (hψzero n x hxT)
    have hcompact : HasCompactSupport (ψ' n) :=
      HasCompactSupport.of_support_subset_isCompact (hBcpt.cthickening) hsupp
    have htsupp : tsupport (ψ' n) ⊆ U := by
      have htsuppT : tsupport (ψ' n) ⊆ cthickening (δ n) B := by
        simpa [tsupport] using closure_minimal hsupp isClosed_cthickening
      exact htsuppT.trans (hTsub.trans hεU)
    exact ⟨(ψ n).contMDiff.contDiff, hcompact, htsupp, hsupp.trans hTsub, hψrange n⟩
  · intro x
    by_cases hx : x ∈ B
    · have hone : ∀ n, ψ' n x = 1 := fun n =>
        hψone n |>.self_of_nhdsSet x hx
      rw [show Set.indicator B (fun _ => (1 : ℝ)) x = 1 by simp [hx]]
      simp_rw [hone]
      exact tendsto_const_nhds
    · have hxcl : x ∉ closure B := by simpa [hBcpt.isClosed.closure_eq] using hx
      obtain ⟨ρ, ⟨hρpos, hρlt⟩⟩ :=
        Metric.exists_real_pos_lt_infEDist_of_notMem_closure hxcl
      have hδtend : Tendsto δ atTop (𝓝 0) := by
        simpa only [δ, div_eq_mul_inv, one_mul, mul_zero] using
          (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat :
            Tendsto (fun n : ℕ => ε * (1 / ((n : ℝ) + 1))) atTop (𝓝 (ε * 0)))
      have hsmall : ∀ᶠ n in atTop, δ n < ρ := by
        rw [Metric.tendsto_nhds] at hδtend
        specialize hδtend ρ hρpos
        filter_upwards [hδtend] with n hn
        simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (hδpos n).le] using hn
      rw [show Set.indicator B (fun _ => (1 : ℝ)) x = 0 by simp [hx]]
      rcases (eventually_atTop.1 hsmall) with ⟨N, hN⟩
      apply tendsto_atTop_of_eventually_const (i₀ := N)
      intro n hn
      apply hψzero n x
      intro hxt
      rw [mem_cthickening_iff] at hxt
      have hδρ : ENNReal.ofReal (δ n) < ENNReal.ofReal ρ :=
        ENNReal.ofReal_lt_ofReal_iff hρpos |>.mpr (hN n hn)
      exact (not_le_of_gt (hδρ.trans hρlt)) hxt

private theorem exists_smooth_entryTestR_approximation {U B : Set (Vec d)}
    (hUopen : IsOpen U) (hBcpt : IsCompact B) (hBU : B ⊆ U) :
    ∃ ψ : ℕ → Vec d → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) ∧ HasCompactSupport (ψ n) ∧
        tsupport (ψ n) ⊆ U) ∧
      ∀ (i j : Fin d) (a : RegCoeffField d),
        Tendsto (fun n => entryTestR i j (ψ n) a) atTop
          (𝓝 (entryTestR i j (Set.indicator B (fun _ => (1 : ℝ))) a)) := by
  obtain ⟨K, ψ, hKcpt, hKU, hψ, hlim⟩ :=
    exists_smooth_cutoff_seq hUopen hBcpt hBU
  refine ⟨ψ, fun n => ⟨(hψ n).1, (hψ n).2.1, (hψ n).2.2.1⟩, ?_⟩
  intro i j a
  have hbound_integrable : Integrable (K.indicator fun x => |a x i j|) volume := by
    rw [integrable_indicator_iff hKcpt.measurableSet]
    simpa only [Real.norm_eq_abs] using!
      ((a.entry_locInt i j).integrableOn_isCompact hKcpt).norm
  have hF_measurable : ∀ n, AEStronglyMeasurable (fun x => a x i j * ψ n x) volume := by
    intro n
    exact ((a.entry_measurable i j).mul (hψ n).1.continuous.measurable).aestronglyMeasurable
  have hF_bound : ∀ n, ∀ᵐ x ∂volume,
      ‖a x i j * ψ n x‖ ≤ K.indicator (fun x => |a x i j|) x := by
    intro n
    filter_upwards with x
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK, norm_mul, Real.norm_eq_abs]
      have hψ01 := (hψ n).2.2.2.2 x
      rw [Real.norm_eq_abs, abs_of_nonneg hψ01.1]
      exact mul_le_of_le_one_right (abs_nonneg _) hψ01.2
    · rw [Set.indicator_of_notMem hxK]
      have hxSupp : x ∉ Function.support (ψ n) := fun hx => hxK ((hψ n).2.2.2.1 hx)
      have hzero : ψ n x = 0 := by
        simpa only [Function.mem_support, not_not] using hxSupp
      simp [hzero]
  have hF_lim : ∀ᵐ x ∂volume,
      Tendsto (fun n => a x i j * ψ n x) atTop
        (𝓝 (a x i j * Set.indicator B (fun _ => (1 : ℝ)) x)) :=
    Filter.Eventually.of_forall fun x => tendsto_const_nhds.mul (hlim x)
  simpa only [entryTestR] using
    tendsto_integral_of_dominated_convergence (K.indicator fun x => |a x i j|)
      hF_measurable hbound_integrable hF_bound hF_lim

/-- Supported smooth entry tests suffice to measure compact-set averages. -/
private theorem measurable_avgMat_of_entryTest
    {Ω : Type*} [MeasurableSpace Ω] {U B : Set (Vec d)}
    (A : Ω → RegCoeffField d) (hUopen : IsOpen U) (hBcpt : IsCompact B) (hBU : B ⊆ U)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, IsLocalTest U φ →
      Measurable (fun ω => entryTestR i j φ (A ω))) :
    Measurable (fun ω => avgMat B (A ω)) := by
  obtain ⟨ψ, hψ, hlim⟩ := exists_smooth_entryTestR_approximation hUopen hBcpt hBU
  refine measurable_matrix_of_entries ?_
  intro i j
  have hmeas : ∀ n, Measurable (fun ω => entryTestR i j (ψ n) (A ω)) := fun n =>
    hEntry i j ⟨(hψ n).1, (hψ n).2.1, (hψ n).2.2⟩
  have htend : Tendsto (fun n ω => entryTestR i j (ψ n) (A ω)) atTop
      (𝓝 (fun ω => entryTestR i j (Set.indicator B (fun _ => (1 : ℝ))) (A ω))) := by
    rw [tendsto_pi_nhds]
    intro ω
    exact hlim i j (A ω)
  have hindicator := measurable_of_tendsto_metrizable hmeas htend
  have heq : (fun ω => avgMat B (A ω) i j) = fun ω =>
      (volume B).toReal⁻¹ • entryTestR i j (Set.indicator B (fun _ => (1 : ℝ))) (A ω) := by
    funext ω
    exact avgMat_entry_eq_smul_entryTestR i j B hBcpt.measurableSet (A ω)
  rw [heq]
  exact hindicator.const_smul ((volume B).toReal⁻¹)

/-- The open-domain slice event follows from a countable family of averages
on compact rational balls, each recovered from the supported smooth tests. -/
private theorem measurableSet_aeeSlice_of_entryTest
    {Ω : Type*} [MeasurableSpace Ω] {U : Set (Vec d)}
    (A : Ω → RegCoeffField d) (hU : IsOpen U)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, IsLocalTest U φ →
      Measurable (fun ω => entryTestR i j φ (A ω))) (k : ℕ) :
    MeasurableSet {ω | AEEQuantitativeEllipticSlice U k (A ω).toFun} := by
  have heq : {ω | AEEQuantitativeEllipticSlice U k (A ω).toFun} =
      A ⁻¹' slicePart U ((k + 1 : ℝ)⁻¹) (k + 1 : ℝ) := by
    rw [← setOf_aeRestrict_isEllipticMatrix_eq_slicePart hU]
    ext ω
    exact aeeQuantitativeEllipticSlice_carrier_iff U hU.measurableSet k (A ω)
  rw [heq]
  simp only [slicePart, Set.preimage_iInter]
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun r =>
    MeasurableSet.iInter fun _hpos => MeasurableSet.iInter fun hsub => ?_
  exact (measurable_avgMat_of_entryTest A hU (isCompact_closedBall _ _) hsub hEntry)
    measurableSet_isEllipticMatrix

/-- Public slice-event measurability bridge used by the response optimizer-selection chain. -/
theorem measurableSet_aeeSlice_of_entryTest_response
    {Ω : Type*} [MeasurableSpace Ω] {U : Set (Vec d)}
    (A : Ω → RegCoeffField d) (hU : IsOpen U)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, IsLocalTest U φ →
      Measurable (fun ω ↦ entryTestR i j φ (A ω))) (k : ℕ) :
    MeasurableSet {ω | AEEQuantitativeEllipticSlice U k (A ω).toFun} :=
  measurableSet_aeeSlice_of_entryTest A hU hEntry k

private theorem Mu_eq_iInf_energy
    {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hvol : 0 < (volume U).toReal) (k : ℕ)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d) :
    Mu U P0 a.1 = ⨅ n : ℕ,
      blockEnergyAverage U a.1
        (canonicalMuGeneratorAffineField (U := U) P0
          (TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule U) n)) := by
  let system : AEEMuOperatorSystemData U a.1 :=
    { correctionSpace := (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuCorrectionSpaceData
      coeffOperatorData := AEEMuCoeffOperatorData.ofIsAEEllipticFieldOn a.2 hvol }
  let H : MuHilbertRealization U a.1 := system.toMuHilbertRealization
  have hMu : Mu U P0 a.1 = H.muCandidate P0 := by
    let gen : canonicalMuBlockCorrectionGeneratorSubmodule U →
        H.correctionSpace.correctionSpace.toSubmodule := by
      intro Y
      exact canonicalMuCorrectionGeneratorEmbedding U Y
    let s : Set ℝ := Set.range fun Y : canonicalMuBlockCorrectionGeneratorSubmodule U =>
      quadraticEnergy H.energyBilin (H.constantField P0 + (gen Y : HilbertBlockL2 U))
    have hgen_dense : DenseRange gen := by
      dsimp [gen, H, system]
      simpa [MuCorrectionSpaceData.ofSubmoduleClosures,
        AEEMuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using!
        denseRange_canonicalMuCorrectionGeneratorEmbedding U
    have hCandidate_sInf : H.muCandidate P0 = sInf s := by
      simpa [s] using
        H.muCandidate_eq_sInf_quadraticEnergy_denseRange P0 gen hgen_dense
    have hCandidateLe :
        ∀ X : BlockState d, IsBlockMuAdmissible U P0 X →
          H.muCandidate P0 ≤ blockEnergyAverage U a.1 X := by
      intro X hX
      have hXmem : MemBlockL2 U X.eval := hX.memBlockL2_eval
      have hcorr_mem :
          toHilbertBlockL2OfBlockField (U := U) hXmem - H.constantField P0 ∈
            H.correctionSpace.correctionSpace := by
        have hsplit := hX.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
        rw [hsplit]
        have hcorr := hX.toCorrectionFieldData_mem_correctionSpace
        simpa [H, system, MuCorrectionSpaceData.ofSubmoduleClosures,
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
        _ = blockEnergyAverage U a.1 X := by
          simpa [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
            MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
            system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
              (X := X) hXmem
    have hBddBelow : BddBelow (muValueSet U P0 a.1) := by
      refine ⟨H.muCandidate P0, ?_⟩
      intro m hm
      rcases hm with ⟨X, hX, rfl⟩
      simpa [blockEnergyAverage] using hCandidateLe X hX
    have hCandidate_le_Mu : H.muCandidate P0 ≤ Mu U P0 a.1 := by
      apply le_Mu_of_forall_isBlockMuAdmissible
      intro X hX
      simpa [blockEnergyAverage] using hCandidateLe X hX
    have hs_subset_mu : s ⊆ muValueSet U P0 a.1 := by
      intro m hm
      rcases hm with ⟨Y, rfl⟩
      rcases Y.property with ⟨f, g, hf, hg, hY, hpot, hsol⟩
      let X : BlockState d :=
        { potential := fun x => P0.1 + f x
          flux := fun x => P0.2 + g x }
      have hAdm : IsBlockMuAdmissible U P0 X := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [X, sub_eq_add_neg, add_assoc, add_comm] using hf
        · simpa [X, sub_eq_add_neg, add_assoc, add_comm] using hpot
        · simpa [X, sub_eq_add_neg, add_assoc, add_comm] using hg
        · simpa [X, sub_eq_add_neg, add_assoc, add_comm] using hsol
      have hGen_comp :
          (gen Y : HilbertBlockL2 U) = toHilbertBlockL2OfComponents hf hg := by
        have hblock_to_hilbert :
            blockL2ToHilbertBlockL2 (U := U) (Y : BlockL2 U) =
              toHilbertBlockL2OfComponents hf hg := by
          rw [← hY]
          simpa [toBlockL2OfComponents, toHilbertBlockL2OfComponents] using!
            (blockL2ToHilbertBlockL2_toBlockL2
              (U := U)
              (F := blockField f g)
              (memBlockL2_blockField hf hg))
        dsimp [gen, canonicalMuCorrectionGeneratorEmbedding,
          PotentialSolenoidalL2Data.submoduleClosureToMuCorrectionSpace]
        exact hblock_to_hilbert
      have hAdmCorr :
          (hAdm.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2 =
            toHilbertBlockL2OfComponents hf hg := by
        change toHilbertBlockL2OfComponents
            hAdm.potentialCorrection_memL2 hAdm.fluxCorrection_memL2 =
          toHilbertBlockL2OfComponents hf hg
        apply MeasureTheory.Lp.ext
        filter_upwards
            [coeFn_toHilbertBlockL2OfComponents (U := U)
              (f := fun x => X.potential x - P0.1)
              (g := fun x => X.flux x - P0.2)
              hAdm.potentialCorrection_memL2 hAdm.fluxCorrection_memL2,
             coeFn_toHilbertBlockL2OfComponents (U := U) (f := f) (g := g) hf hg]
          with x hleft hright
        rw [hleft, hright]
        apply HilbertBlockVec.ext
        · ext i
          simp [X, hilbertBlockField]
        · ext i
          simp [X, hilbertBlockField]
      have hsplit :
          toHilbertBlockL2OfBlockField (U := U) hAdm.memBlockL2_eval =
            H.constantField P0 + (gen Y : HilbertBlockL2 U) := by
        calc
          toHilbertBlockL2OfBlockField (U := U) hAdm.memBlockL2_eval
              = blockVecToHilbertBlockL2Const (U := U) P0 +
                  (hAdm.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2 :=
                hAdm.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
          _ = H.constantField P0 + (gen Y : HilbertBlockL2 U) := by
                rw [hAdmCorr, ← hGen_comp]
                simp [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
                  MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator]
      have hEnergy :
          quadraticEnergy H.energyBilin (H.constantField P0 + (gen Y : HilbertBlockL2 U)) =
            blockEnergyAverage U a.1 X := by
        rw [← hsplit]
        simpa [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
          MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
          system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
            (X := X) hAdm.memBlockL2_eval
      refine ⟨X, hAdm, ?_⟩
      simpa [blockEnergyAverage] using hEnergy
    have hs_nonempty : s.Nonempty := by
      refine ⟨quadraticEnergy H.energyBilin (H.constantField P0 + (gen 0 : HilbertBlockL2 U)), ?_⟩
      exact ⟨0, rfl⟩
    have hMu_le_sInf : Mu U P0 a.1 ≤ sInf s := by
      apply le_csInf hs_nonempty
      intro m hm
      exact csInf_le hBddBelow (hs_subset_mu hm)
    have hMu_le_candidate : Mu U P0 a.1 ≤ H.muCandidate P0 := by
      calc
        Mu U P0 a.1 ≤ sInf s := hMu_le_sInf
        _ = H.muCandidate P0 := hCandidate_sInf.symm
    have hEq : Mu U P0 a.1 = H.muCandidate P0 :=
      le_antisymm hMu_le_candidate hCandidate_le_Mu
    exact hEq
  let ξ := TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule U)
  have hξ : DenseRange ξ := TopologicalSpace.denseRange_denseSeq _
  let gen : ℕ → H.correctionSpace.correctionSpace.toSubmodule := fun n =>
    canonicalMuCorrectionGeneratorEmbedding U (ξ n)
  have hgen_dense : DenseRange gen := by
    have hEmbDense :
        DenseRange (canonicalMuCorrectionGeneratorEmbedding U) :=
      denseRange_canonicalMuCorrectionGeneratorEmbedding U
    have hEmbCont :
        Continuous (canonicalMuCorrectionGeneratorEmbedding U) :=
      continuous_canonicalMuCorrectionGeneratorEmbedding U
    have hcomp : DenseRange ((canonicalMuCorrectionGeneratorEmbedding U) ∘ ξ) :=
      DenseRange.comp hEmbDense hξ hEmbCont
    dsimp [gen, H, system]
    simpa [MuCorrectionSpaceData.ofSubmoduleClosures,
      AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
      Function.comp_def] using! hcomp
  have hCandidate :
      H.muCandidate P0 =
        sInf (Set.range fun n : ℕ =>
          quadraticEnergy H.energyBilin (H.constantField P0 + (gen n : HilbertBlockL2 U))) := by
    simpa using H.muCandidate_eq_sInf_quadraticEnergy_denseRange P0 gen hgen_dense
  have hEnergy :
      ∀ n : ℕ,
        quadraticEnergy H.energyBilin (H.constantField P0 + (gen n : HilbertBlockL2 U)) =
          blockEnergyAverage U a.1
            (canonicalMuGeneratorAffineField (U := U) P0 (ξ n)) := by
    intro n
    have hsplit :
        toHilbertBlockL2OfBlockField (U := U)
            (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 (ξ n)) =
          H.constantField P0 + (gen n : HilbertBlockL2 U) := by
      simpa [gen, H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
        canonicalMuGeneratorAffineField_hilbert_eq_const_add (U := U) P0 (ξ n)
    calc
      quadraticEnergy H.energyBilin (H.constantField P0 + (gen n : HilbertBlockL2 U))
          = quadraticEnergy H.energyBilin
              (toHilbertBlockL2OfBlockField (U := U)
                (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 (ξ n))) := by
            rw [hsplit]
      _ = blockEnergyAverage U a.1
            (canonicalMuGeneratorAffineField (U := U) P0 (ξ n)) := by
            simpa [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
              MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
              system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
                (X := canonicalMuGeneratorAffineField (U := U) P0 (ξ n))
                (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 (ξ n))
  calc
    Mu U P0 a.1 = H.muCandidate P0 := hMu
    _ = ⨅ n : ℕ,
          quadraticEnergy H.energyBilin (H.constantField P0 + (gen n : HilbertBlockL2 U)) := by
      rw [hCandidate, sInf_range]
    _ = ⨅ n : ℕ,
          blockEnergyAverage U a.1
            (canonicalMuGeneratorAffineField (U := U) P0 (ξ n)) :=
      iInf_congr hEnergy

/-- Public general-cell countable-energy presentation used by the response measurable-selection
chain.  This exposes the already established Chapter-4 argument without adding any ellipticity
constant to a downstream response statement. -/
theorem mu_eq_iInf_energy_for_responseSelection
    {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hvol : 0 < (volume U).toReal) (k : ℕ)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d) :
    Mu U P0 a.1 = ⨅ n : ℕ,
      blockEnergyAverage U a.1
        (canonicalMuGeneratorAffineField (U := U) P0
          (TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule U) n)) :=
  Mu_eq_iInf_energy hvol k a P0

/-- The chosen Borel representative already defining the coarse block
lands in CG's regular carrier. Its smooth local sigma algebra pulls back into
the support-local information supplied by the coefficient space's generators. -/
private theorem exists_measurable_regCoeffField (d : ℕ) :
    ∃ A : CoeffSpace d → RegCoeffField d,
      (∀ a, (A a).toFun = (⇑a.1 : CoeffField d)) ∧
      ∀ U, @Measurable (CoeffSpace d) (RegCoeffField d)
        (coeffSigma d U)
        (MeasurableSpace.generateFrom
          {s | ∃ (i j : Fin d) (φ : Vec d → ℝ), IsLocalTest U φ ∧
            ∃ t : Set ℝ, MeasurableSet t ∧ s = entryTestR i j φ ⁻¹' t}) A := by
  have hloc (a : CoeffSpace d) (i j : Fin d) :
      LocallyIntegrable (fun x => a.1 x i j) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨M, -, hM⟩ := ae_abs_entry_le_of_aeUniformlyEllipticField a.2 hK.isBounded
    refine Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      ((continuous_id.matrix_elem i j).comp_aestronglyMeasurable
        a.1.aestronglyMeasurable) (M := M) ?_
    filter_upwards [ae_restrict_of_ae hM, ae_restrict_mem hK.measurableSet] with x hx hxK
    simpa [Real.norm_eq_abs] using hx hxK i j
  let A : CoeffSpace d → RegCoeffField d := fun a =>
    ⟨⇑a.1, fun i j => ((continuous_id.matrix_elem i j).measurable.comp a.1.measurable), hloc a⟩
  refine ⟨A, fun _ => rfl, fun U => ?_⟩
  refine @measurable_generateFrom (CoeffSpace d) (RegCoeffField d)
    (coeffSigma d U) _ A ?_
  rintro s ⟨i, j, φ, hφ, t, ht, rfl⟩
  have heq : (fun a => entryTestR i j φ (A a)) =
      coeffPairing (Pi.single j 1) (Pi.single i 1) φ := by
    funext a
    simp [entryTestR, coeffPairing, A, vecDot_single_left, matVecMul_single]
  change MeasurableSet[coeffSigma d U] ((fun a => entryTestR i j φ (A a)) ⁻¹' t)
  rw [heq]
  exact measurable_coeffPairing_local (Pi.single j 1) (Pi.single i 1)
    hφ ht

private theorem measurable_Mu_on_open_slice
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpen U) (hvol : 0 < (volume U).toReal)
    (k : ℕ) (A : Ω → RegCoeffField d)
    (hSlice : ∀ ω, AEEQuantitativeEllipticSlice U k (A ω).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      Measurable (fun ω => entryTestR i j φ (A ω))) (P : BlockVec d) :
    Measurable (fun ω => Mu U P (A ω).toFun) := by
  have hfinite : volume U ≠ ⊤ := by
    simpa [volumeMeasureOn] using (measure_ne_top (volumeMeasureOn U) Set.univ)
  have hF := measurable_toHilbertMatrixL2_carrier (hSlice := hSlice)
    hU.measurableSet hEntry hU hfinite
  have heq : (fun ω => Mu U P (A ω).toFun) = fun ω => ⨅ n : ℕ,
      blockEnergyAverage U (A ω).toFun
        (canonicalMuGeneratorAffineField (U := U) P
          (TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule U) n)) := by
    funext ω
    exact Mu_eq_iInf_energy hvol k ⟨(A ω).toFun, hSlice ω⟩ P
  rw [heq]
  exact Measurable.iInf fun n => measurable_blockEnergyAverage_carrier hF
    (canonicalMuGeneratorAffineField (U := U) P
      (TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule U) n))
    (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P
      (TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule U) n))

/-- Strict measurability of the variational value on an open bounded
set of positive volume. Ellipticity slices cover every coefficient field. -/
private theorem measurable_Mu_coeffSigma_open
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hvol : 0 < (volume U).toReal) (P : BlockVec d) :
    @Measurable (CoeffSpace d) ℝ (coeffSigma d U) _
      (fun a => Mu U P (⇑a.1)) := by
  classical
  let : MeasurableSpace (CoeffSpace d) := coeffSigma d U
  let : IsFiniteMeasure (volumeMeasureOn U) :=
    ⟨by simpa [volumeMeasureOn] using hUb.measure_lt_top⟩
  obtain ⟨A, hA, hAm⟩ := exists_measurable_regCoeffField d
  have hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, IsLocalTest U φ →
      Measurable (fun a => entryTestR i j φ (A a)) := by
    intro i j φ hφ t ht
    exact (hAm U) (MeasurableSpace.measurableSet_generateFrom ⟨i, j, φ, hφ, t, ht, rfl⟩)
  let t : ℕ → Set (CoeffSpace d) :=
    fun k => {a | AEEQuantitativeEllipticSlice U k (A a).toFun}
  have ht : ∀ k, MeasurableSet (t k) := fun k =>
    measurableSet_aeeSlice_of_entryTest A hU hEntry k
  have hc : ∀ a : CoeffSpace d, ∃ k, a ∈ t k := by
    intro a
    obtain ⟨lam, Lam, hlam, -, hell⟩ :=
      a.2.exists_ae_isEllipticMatrix_of_isBounded hUb
    have hEll : IsAEEllipticFieldOn lam Lam U (A a).toFun := by
      refine ⟨hU.measurableSet,
        fun i j => aestronglyMeasurable_restrictCoeffField_carrier U hU.measurableSet (A a) i j,
        ?_⟩
      filter_upwards [ae_restrict_of_ae hell, ae_restrict_mem hU.measurableSet] with x hx hxU
      rw [hA a]
      exact hx hxU
    exact AEEQuantitativeEllipticSlice.exists_of_aeeEllipticOn hlam hEll
  have hcover : ⋃ k, t k = Set.univ := by
    ext a
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hc a
  let f : (k : ℕ) → t k → ℝ := fun _ a => Mu U P (A a.1).toFun
  have hf : ∀ k, Measurable (f k) := by
    intro k
    exact measurable_Mu_on_open_slice hU hvol k (fun a : t k => A a.1)
      (fun a => a.2) (fun i j _ hφ hcpt hsupp =>
        (hEntry i j ⟨hφ, hcpt, hsupp⟩).comp measurable_subtype_coe) P
  have hagree : ∀ (i j : ℕ) (a : CoeffSpace d) (hi : a ∈ t i) (hj : a ∈ t j),
      f i ⟨a, hi⟩ = f j ⟨a, hj⟩ := fun _ _ _ _ _ => rfl
  have hm := measurable_liftCover t ht f hf hagree hcover
  have heq : (fun a : CoeffSpace d => Mu U P (⇑a.1)) =
      Set.liftCover t f hagree hcover := by
    funext a
    obtain ⟨k, hk⟩ := hc a
    rw [Set.liftCover_of_mem (S := t) (f := f) (hf := hagree) (hS := hcover) hk]
    dsimp [f]
    rw [hA a]
  rw [heq]
  exact hm

/-- Every entry of the coarse block on an invertible adapted cell is
measurable for its support-local coefficient sigma algebra. The proof
uses CG's countable variational infimum and proves the carrier comparison. -/
theorem measurable_coarseBlock_entry_adapted
    {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d)
    (α β : BlockCoord d) :
    @Measurable (CoeffSpace d) ℝ
      (coeffSigma d (HighContrast.adaptedCellTranslate q j y)) inferInstance
      (fun a => blockMatEntry
        (coarseBlock (HighContrast.adaptedCellTranslate q j y) a) α β) := by
  let U := HighContrast.adaptedCellTranslate q j y
  have hU : IsOpen U := Geometry.isOpen_adaptedCellTranslate hq j y
  have hUb : Bornology.IsBounded U := by
    rw [show U = (fun v => y + matVecMul q v) '' HighContrast.centeredCube d j from
      Transport.adaptedCellTranslate_eq_image q j y]
    have hlin : Continuous (fun v : Vec d => y + matVecMul q v) :=
      continuous_const.add (Matrix.toLin' q).continuous_of_finiteDimensional
    exact (((isBounded_openCubeSet (originCube d j)).isCompact_closure).image hlin).isBounded.subset
      (Set.image_mono subset_closure)
  have hvol : 0 < (volume U).toReal := by
    have hdet : q.det ≠ 0 :=
      isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det q).mp hq)
    rw [show U = HighContrast.adaptedCellTranslate q j y from rfl,
      Geometry.volume_adaptedCellTranslate, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (by positivity)]
    exact mul_pos (abs_pos.mpr hdet) (by positivity)
  let : MeasurableSpace (CoeffSpace d) := coeffSigma d U
  have hMu := measurable_Mu_coeffSigma_open hU hUb hvol
  have heq : (fun a : CoeffSpace d => blockMatEntry (coarseBlock U a) α β) =
      fun a : CoeffSpace d => if α = β then 2 * Mu U (blockBasis α) (⇑a.1)
        else Mu U (blockBasis α + blockBasis β) (⇑a.1) -
          Mu U (blockBasis α) (⇑a.1) - Mu U (blockBasis β) (⇑a.1) := by
    funext a
    exact blockMatEntry_coarseBlockMatrix U (⇑a.1) α β
  change Measurable (fun a : CoeffSpace d => blockMatEntry (coarseBlock U a) α β)
  rw [heq]
  split_ifs
  · exact (hMu (blockBasis α)).const_mul 2
  · exact ((hMu (blockBasis α + blockBasis β)).sub (hMu (blockBasis α))).sub (hMu (blockBasis β))

/-- The full unfolded matrix retains the same local sigma algebra. -/
theorem measurable_coarseBlock_matrix_adapted
    {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d) :
    @Measurable (CoeffSpace d) (FullBlockMat d)
      (coeffSigma d (HighContrast.adaptedCellTranslate q j y)) inferInstance
      (fun a => toFullBlockMat (coarseBlock (HighContrast.adaptedCellTranslate q j y) a)) := by
  let : MeasurableSpace (CoeffSpace d) :=
    coeffSigma d (HighContrast.adaptedCellTranslate q j y)
  apply Measurable.of_eval
  intro α
  apply Measurable.of_eval
  intro β
  exact measurable_coarseBlock_entry_adapted q hq j y α β

end

end HCPolySupport.HighContrast.Annealed
