/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Block
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.MuRecoveryBlockResponse
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.OriginCubeEllipticRecovery.Existence
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2Realization

/-!
# High-contrast homogenization: Entry.CG.Proofs.AdaptedDomainRecovery

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Convex-domain recovery and affine open cubes

On every bounded open convex domain with positive real volume, the canonical
potential/solenoidal recovery data realizes the `Mu` infimum. This module proves
that identification from CG's Hilbert minimizer and representative realization,
then obtains the full coarse quadratic characterization and mixed response formula,
which serve the response transfer `p.response.transfer`.
Strict positivity uses pointwise ellipticity and the zero mean of both corrections.

The affine open-cube theorems discharge geometry and volume assumptions for every
invertible matrix, integer scale, and real translation. All imports and declarations
stay on CG's carriers. The sigma-matrix recovery package is not assumed: the direct
mixed response/Mu route supplies the needed characterization. Their adapted-cell
instances serve the fixed-geometry recurrence `p.fixed.geometry.parent.child.recurrence`.
-/

namespace HCPolySupport.HighContrast.CG

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-- On any bounded open convex domain, the canonical closure-based recovery package realizes
the Hilbert minimizer value `muCandidate`. -/
theorem exists_recoveryData_of_mu_eq_muCandidate_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)} {lam Lam : ℝ} {a : CoeffField d}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (volume U).toReal) :
    ∃ R : PotentialSolenoidalL2RecoveryData U,
      ∀ P : BlockVec d,
        Mu U P a =
          ((R.toMuHilbertRealization
            (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)).muCandidate P) := by
  have hRealize : PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      hConv
  let R : PotentialSolenoidalL2RecoveryData U :=
    potentialSolenoidalL2RecoveryData_ofSubmoduleClosures_of_potentialZeroTraceClosureRealization
      (U := U) hRealize
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol
  refine ⟨R, ?_⟩
  intro P
  have hCandidateLe :
      ∀ X : BlockState d, IsBlockMuAdmissible U P X →
        (R.toMuHilbertRealization system).muCandidate P ≤ blockEnergyAverage U a X := by
    intro X hX
    let Y : CorrectionFieldData U := hX.toCorrectionFieldDataOfAdmissible
    have hXmemBlock : MemBlockL2 U X.eval := hX.memBlockL2_eval
    have hcorr :
        Y.toHilbertBlockL2 ∈ R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData.correctionSpace := by
      exact
        R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData.mem_correctionSpace
          Y.potential_memL2 Y.flux_memL2 Y.isPotentialZeroTrace Y.isSolenoidalZeroNormalTrace
    have hconst_add :
        toHilbertBlockL2OfBlockField (U := U) hXmemBlock =
          blockVecToHilbertBlockL2Const (U := U) P + Y.toHilbertBlockL2 := by
      simpa [Y] using hX.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
    have hcorr_mem :
        toHilbertBlockL2OfBlockField (U := U) hXmemBlock -
            (R.toMuHilbertRealization system).constantField P ∈
          (R.toMuHilbertRealization system).correctionSpace.correctionSpace := by
      rw [hconst_add]
      simpa [R, system, PotentialSolenoidalL2RecoveryData.toMuHilbertRealization,
        MuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcorr
    have hMin :
        (R.toMuHilbertRealization system).muCandidate P ≤
          quadraticEnergy
            (energyBilinOfOperator system.toMuOperatorRealization.operator)
            (toHilbertBlockL2OfBlockField (U := U) hXmemBlock) := by
      simpa [R, system, PotentialSolenoidalL2RecoveryData.toMuHilbertRealization,
        MuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
        (R.toMuHilbertRealization system).muCandidate_le_quadraticEnergy P
          (toHilbertBlockL2OfBlockField (U := U) hXmemBlock) hcorr_mem
    calc
      (R.toMuHilbertRealization system).muCandidate P ≤
          quadraticEnergy
            (energyBilinOfOperator system.toMuOperatorRealization.operator)
            (toHilbertBlockL2OfBlockField (U := U) hXmemBlock) := hMin
      _ = blockEnergyAverage U a X := by
            exact
              system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
                (X := X) hXmemBlock
  have hrecEnergy :
      blockEnergyAverage U a ((R.toMuCorrectionSpaceRecoveryData).recoveredField system P) =
        (R.toMuHilbertRealization system).muCandidate P := by
    let H : MuHilbertRealization U a := R.toMuHilbertRealization system
    have hminim :
        toHilbertBlockL2OfBlockField (U := U)
            ((R.toMuCorrectionSpaceRecoveryData).recoveredField_memBlockL2 system P) =
          H.minimizerMap P := by
      simpa [H, R, system, PotentialSolenoidalL2RecoveryData.toMuHilbertRealization] using!
        (R.toMuCorrectionSpaceRecoveryData).recoveredField_minimizer_eq system P
    calc
      blockEnergyAverage U a ((R.toMuCorrectionSpaceRecoveryData).recoveredField system P)
          = quadraticEnergy
              (energyBilinOfOperator system.toMuOperatorRealization.operator)
              (toHilbertBlockL2OfBlockField (U := U)
                ((R.toMuCorrectionSpaceRecoveryData).recoveredField_memBlockL2 system P)) := by
                symm
                exact
                  system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
                    (X := (R.toMuCorrectionSpaceRecoveryData).recoveredField system P)
                    ((R.toMuCorrectionSpaceRecoveryData).recoveredField_memBlockL2 system P)
      _ = quadraticEnergy H.energyBilin (H.minimizerMap P) := by
            rw [hminim]
            rfl
      _ = H.muCandidate P := by
            rfl
      _ = (R.toMuHilbertRealization system).muCandidate P := by
            rfl
  have hBddBelow : BddBelow (muValueSet U P a) := by
    refine ⟨vecDot P.1 P.2, ?_⟩
    intro m hm
    rcases hm with ⟨X, hX, rfl⟩
    exact
      hX.blockEnergyAverage_ge_vecDot_of_integral_eq_zero_of_isEllipticFieldOn
        (a := a)
        (hX.toBlockMuIntegrabilityDataOfIsEllipticFieldOn (a := a) hEll)
        hEll
        (by
          simpa [sub_eq_add_neg] using
            (IsPotentialZeroTraceOn.integral_eq_zero hX.isPotentialZeroTrace))
        (by
          simpa [sub_eq_add_neg] using
            (IsSolenoidalZeroNormalTraceOn.integral_eq_zero hConv.isSobolevRegularDomain
              hX.isSolenoidalZeroNormalTrace))
        hvol.ne'
  have hUpper :
      Mu U P a ≤ (R.toMuHilbertRealization system).muCandidate P := by
    let Xrec : BlockState d := (R.toMuCorrectionSpaceRecoveryData).recoveredField system P
    have hAdm : IsBlockMuAdmissible U P Xrec := by
      simpa [Xrec] using (R.toMuCorrectionSpaceRecoveryData).recoveredField_admissible system P
    calc
      Mu U P a ≤ blockEnergyAverage U a Xrec := by
        exact csInf_le hBddBelow (muValueSet_mem hAdm)
      _ = (R.toMuHilbertRealization system).muCandidate P := hrecEnergy
  have hLower :
      (R.toMuHilbertRealization system).muCandidate P ≤ Mu U P a := by
    apply le_Mu_of_forall_isBlockMuAdmissible
    intro X hX
    exact hCandidateLe X hX
  exact le_antisymm hUpper hLower

/-- The recovery compatibility package on any bounded open convex domain. -/
theorem exists_recovery_compatibility_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)} {lam Lam : ℝ} {a : CoeffField d}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (volume U).toReal) :
    ∃ R : PotentialSolenoidalL2RecoveryData U,
      Nonempty (PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData
        (a := a) R (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) := by
  rcases exists_recoveryData_of_mu_eq_muCandidate_of_isOpenBoundedConvexDomain
      hConv hEll hvol with
    ⟨R, hmu⟩
  exact
    ⟨R,
      ⟨PotentialSolenoidalL2RecoveryData.muRecoveryCompatibilityData_of_isEllipticFieldOn_of_mu_eq_muCandidate
          R hEll hvol hmu⟩⟩

/-- The canonical coarse block matrix is characterized by the variational quadratic identity
on any bounded open convex domain. -/
theorem isCoarseBlockMatrix_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)} {lam Lam : ℝ} {a : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain U) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (volume U).toReal) :
    IsCoarseBlockMatrix U a (coarseBlockMatrix U a) := by
  let : IsFiniteMeasure (volumeMeasureOn U) := hConv.isFiniteMeasure_restrict_volume
  rcases exists_recovery_compatibility_of_isOpenBoundedConvexDomain hConv hEll hvol with
    ⟨R, ⟨compat⟩⟩
  exact
    isCoarseBlockMatrix_coarseBlockMatrix
      (R.exists_coarseBlockMatrixOfIsEllipticFieldOn hEll hvol compat)

/-- Mixed scalar response as the canonical coarse-block quadratic expression on any bounded
open convex domain. -/
theorem responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)} {lam Lam : ℝ} {a : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain U) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (volume U).toReal) (p r : Vec d) :
    ResponseJ U p r a =
    (1 / 2 : ℝ) * blockVecDot (-p, r)
      (blockMatVecMul (coarseBlockMatrix U a) (-p, r)) - vecDot p r := by
  let : IsFiniteMeasure (volumeMeasureOn U) := hConv.isFiniteMeasure_restrict_volume
  rcases exists_recovery_compatibility_of_isOpenBoundedConvexDomain hConv hEll hvol with
    ⟨R, ⟨compat⟩⟩
  have hResp :
      ResponseJ U p r a = Mu U (-p, r) a - vecDot p r :=
    R.responseJ_eq_mu_neg_left_sub_vecDot_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      hConv hEll hvol compat p r
  have hMu :=
    R.mu_eq_half_blockVecDot_coarseBlockMatrixOfIsEllipticFieldOn hEll hvol compat (-p, r)
  rw [hResp, hMu]

/-- Strict positivity follows from an attained energy minimum. Pointwise ellipticity makes
zero energy force the minimizer to vanish a.e.; the zero-mean corrections then force its
prescribed block vector to vanish. No sigma-matrix recovery premise is needed. -/
theorem blockPosDef_coarseBlockMatrix_of_isOpenBoundedConvexDomain
    {d : ℕ} [NeZero d] {U : Set (Vec d)} {lam Lam : ℝ} {a : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain U) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (volume U).toReal) :
    Book.Ch02.BlockPosDef (coarseBlockMatrix U a) := by
  let : IsFiniteMeasure (volumeMeasureOn U) := hConv.isFiniteMeasure_restrict_volume
  have henergy : ∀ (P : BlockVec d), P ≠ 0 → ∀ X : BlockState d,
      IsBlockMuAdmissible U P X → 0 < blockEnergyAverage U a X := by
    intro P hP X hX
    have hnonneg : 0 ≤ᵐ[volume.restrict U] blockEnergyDensity a X := by
      filter_upwards [ae_restrict_mem hConv.isOpen.measurableSet] with x hx
      by_cases hz : X.eval x = 0
      · simp [blockEnergyDensity, hz, blockVecDot, vecDot]
      · exact (mul_pos (by norm_num)
          (blockMatrixOfCoeff_quadratic_pos_of_isEllipticMatrix (hEll.2 x hx) hz)).le
    have hint := (hX.toBlockMuIntegrabilityDataOfIsEllipticFieldOn hEll).energyIntegrable
    have hpos : 0 < ∫ x in U, blockEnergyDensity a X x := by
      apply lt_of_le_of_ne (integral_nonneg_of_ae hnonneg)
      intro hzero
      have hzeroae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).1 hzero.symm
      have hXzero : X.eval =ᵐ[volume.restrict U] 0 := by
        filter_upwards [hzeroae, ae_restrict_mem hConv.isOpen.measurableSet] with x hx hxU
        by_contra hne
        have hp := blockMatrixOfCoeff_quadratic_pos_of_isEllipticMatrix
          (hEll.2 x hxU) hne
        change (1 / 2 : ℝ) * blockVecDot (X.eval x)
          (blockMatVecMul (blockMatrixOfCoeff (a x)) (X.eval x)) = 0 at hx
        change (1 / 2 : ℝ) * blockVecDot (X.potential x, X.flux x)
          (blockMatVecMul (blockMatrixOfCoeff (a x)) (X.potential x, X.flux x)) = 0 at hx
        linarith only [hp, hx]
      have hpzero := IsPotentialZeroTraceOn.integral_eq_zero hX.isPotentialZeroTrace
      have hqzero := IsSolenoidalZeroNormalTraceOn.integral_eq_zero
        hConv.isSobolevRegularDomain hX.isSolenoidalZeroNormalTrace
      apply hP
      apply Prod.ext
      · funext i
        have hi := congrFun hpzero i
        have heq : (∫ x in U, (X.potential x - P.1) i) =
            (volume U).toReal * (-P.1 i) := by
          calc
            _ = ∫ _x in U, -P.1 i := integral_congr_ae (hXzero.mono fun x hx => by
              have hx' := congrArg (fun v : BlockVec d => v.1 i) hx
              simp only [BlockState.eval, Pi.zero_apply, Prod.fst_zero] at hx'
              simp [hx'])
            _ = _ := by simp [Measure.real]
        rw [heq] at hi
        simpa using (mul_eq_zero.mp hi).resolve_left hvol.ne'
      · funext i
        have hi := congrFun hqzero i
        have heq : (∫ x in U, (X.flux x - P.2) i) =
            (volume U).toReal * (-P.2 i) := by
          calc
            _ = ∫ _x in U, -P.2 i := integral_congr_ae (hXzero.mono fun x hx => by
              have hx' := congrArg (fun v : BlockVec d => v.2 i) hx
              simp only [BlockState.eval, Pi.zero_apply, Prod.snd_zero] at hx'
              simp [hx'])
            _ = _ := by simp [Measure.real]
        rw [heq] at hi
        simpa using (mul_eq_zero.mp hi).resolve_left hvol.ne'
    exact mul_pos (inv_pos.mpr hvol) hpos
  rcases exists_recoveryData_of_mu_eq_muCandidate_of_isOpenBoundedConvexDomain
    hConv hEll hvol with ⟨R, hmu⟩
  let system := R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol
  have hcoarse := isCoarseBlockMatrix_of_isOpenBoundedConvexDomain hConv hEll hvol
  intro P hP
  have hpos := henergy P hP (R.toMuCorrectionSpaceRecoveryData.recoveredField system P)
    (R.toMuCorrectionSpaceRecoveryData.recoveredField_admissible system P)
  rw [R.toMuCorrectionSpaceRecoveryData.recoveredField_blockEnergyAverage_eq_mu system hmu P]
    at hpos
  rw [hcoarse.2 P] at hpos
  linarith only [hpos]

/-- Invertible affine images of open triadic cubes are bounded open convex domains. -/
theorem isOpenBoundedConvexDomain_affine_openCube
    {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d) :
    IsOpenBoundedConvexDomain
      (translateSet y (matVecMul q '' openCubeSet (originCube d j))) := by
  apply IsOpenBoundedConvexDomain.translateSet
  have hcube := isOpenBoundedConvexDomain_openCubeSet (originCube d j)
  let L := (Matrix.toLin' q).toContinuousLinearMap
  refine ⟨?_, ?_, ?_⟩
  · exact (Matrix.toLin' q).isOpenMap_of_finiteDimensional
      (Matrix.mulVec_surjective_iff_isUnit.mpr hq) _ hcube.isOpen
  · exact Bornology.IsBounded.isBoundedDomain
      (L.lipschitzWith.isBounded_image hcube.isBoundedDomain.isBounded)
  · exact hcube.convex.linear_image (Matrix.toLin' q)

/-- Every invertible affine open cube has positive finite real volume, for every integer scale. -/
theorem volume_affine_openCube_toReal_pos
    {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d) :
    0 < (volume (translateSet y (matVecMul q '' openCubeSet (originCube d j)))).toReal := by
  have hdomain := isOpenBoundedConvexDomain_affine_openCube q hq j y
  apply ENNReal.toReal_pos (hdomain.isOpen.measure_ne_zero volume ?_) hdomain.volume_lt_top.ne
  have hzero : (0 : Vec d) ∈ openCubeSet (originCube d j) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
    constructor <;> dsimp <;> nlinarith only [h3]
  exact ⟨matVecMul q 0 + y, matVecMul q 0, ⟨0, hzero, rfl⟩, rfl⟩

/-- The scalar response depends only on the coefficient a.e. class on its domain. -/
theorem responseJ_congr_of_ae_eq {d : ℕ} {U : Set (Vec d)} {a b : CoeffField d}
    (hab : a =ᵐ[volume.restrict U] b) (p r : Vec d) :
    ResponseJ U p r a = ResponseJ U p r b := by
  have hsub : ∀ {a b : CoeffField d}, a =ᵐ[volume.restrict U] b →
      responseJValueSet U p r a ⊆ responseJValueSet U p r b := by
    intro a b hab m hm
    rcases hm with ⟨u, rfl⟩
    let v : AHarmonicFunction b U :=
      ⟨u.toH1, IsAHarmonicGradient.of_ae_eq_coeff hab u.isHarmonic⟩
    refine ⟨v, ?_⟩
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hab] with x hx
    simp only [scalarResponseIntegrand, v, hx]
  exact congrArg sSup (Set.Subset.antisymm (hsub hab) (hsub hab.symm))

/-- The variational characterization on an arbitrary invertible affine open cube. -/
theorem isCoarseBlockMatrix_affine_openCube
    {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d)
    (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam
      (translateSet y (matVecMul q '' openCubeSet (originCube d j))) a) :
    IsCoarseBlockMatrix (translateSet y (matVecMul q '' openCubeSet (originCube d j))) a
      (coarseBlockMatrix (translateSet y (matVecMul q '' openCubeSet (originCube d j))) a) :=
  isCoarseBlockMatrix_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_affine_openCube q hq j y) hEll
    (volume_affine_openCube_toReal_pos q hq j y)

/-- Strict positivity on an arbitrary invertible affine open cube. -/
theorem blockPosDef_coarseBlockMatrix_affine_openCube
    {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d)
    (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam
      (translateSet y (matVecMul q '' openCubeSet (originCube d j))) a) :
    Book.Ch02.BlockPosDef
      (coarseBlockMatrix (translateSet y (matVecMul q '' openCubeSet (originCube d j))) a) :=
  blockPosDef_coarseBlockMatrix_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_affine_openCube q hq j y) hEll
    (volume_affine_openCube_toReal_pos q hq j y)

/-- The full mixed response identity on an arbitrary invertible affine open cube. -/
theorem responseJ_eq_block_quadratic_affine_openCube
    {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d)
    (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam
      (translateSet y (matVecMul q '' openCubeSet (originCube d j))) a) (p r : Vec d) :
    ResponseJ (translateSet y (matVecMul q '' openCubeSet (originCube d j))) p r a =
      (1 / 2 : ℝ) * blockVecDot (-p, r)
        (blockMatVecMul
          (coarseBlockMatrix (translateSet y (matVecMul q '' openCubeSet (originCube d j))) a)
          (-p, r)) - vecDot p r :=
  responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_affine_openCube q hq j y) hEll
    (volume_affine_openCube_toReal_pos q hq j y) p r

end

end HCPolySupport.HighContrast.CG
