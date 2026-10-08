/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungRecentDefectPointwise
public import LeanPool.HighContrastHomogenization.Provider.Response.RecentDifferenceEnergyIntegrability

/-!
# High-contrast homogenization: Provider.Response.PreYoungRecentDefectRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A pointwise pairing bound against the square root of twice an energy
passes through law-space Cauchy--Schwarz. -/
theorem integral_abs_pairing_le_sqrt_two_mul_energy
    {P : Measure (CoeffSpace d)} {pair energy load : CoeffSpace d → ℝ}
    {annealedLoad : ℝ}
    (henergy : ∀ a, 0 ≤ energy a) (hload : ∀ a, 0 ≤ load a)
    (hannealedLoad : 0 ≤ annealedLoad)
    (hpoint : ∀ a, |pair a| ≤ Real.sqrt (2 * energy a) * load a)
    (hmeasPair : AEStronglyMeasurable pair P)
    (hintEnergy : Integrable energy P)
    (hintLoadSq : Integrable (fun a ↦ load a ^ 2) P)
    (hloadIntegral : ∫ a, load a ^ 2 ∂P = annealedLoad ^ 2) :
    ∫ a, |pair a| ∂P ≤
      Real.sqrt (2 * ∫ a, energy a ∂P) * annealedLoad := by
  let root : CoeffSpace d → ℝ := fun a ↦ Real.sqrt (2 * energy a)
  have hrootMeas : AEStronglyMeasurable root P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (hintEnergy.const_mul 2).aestronglyMeasurable
  have hrootSq : (fun a ↦ root a ^ (2 : ℕ)) =ᵐ[P]
      fun a ↦ 2 * energy a :=
    _root_.Filter.Eventually.of_forall fun a ↦
      Real.sq_sqrt (mul_nonneg (by norm_num) (henergy a))
  have hintRootSq : Integrable (fun a ↦ root a ^ (2 : ℕ)) P :=
    (hintEnergy.const_mul 2).congr hrootSq.symm
  have hrootL2 : MemLp root 2 P :=
    (memLp_two_iff_integrable_sq hrootMeas).2 hintRootSq
  have hloadMeas : AEStronglyMeasurable load P := by
    apply AEStronglyMeasurable.congr
      hintLoadSq.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
    exact _root_.Filter.Eventually.of_forall fun a ↦ Real.sqrt_sq (hload a)
  have hloadL2 : MemLp load 2 P :=
    (memLp_two_iff_integrable_sq hloadMeas).2 hintLoadSq
  have hintProd : Integrable (fun a ↦ root a * load a) P :=
    hrootL2.integrable_mul hloadL2
  have hmeasAbs : AEStronglyMeasurable (fun a ↦ |pair a|) P := by
    simpa only [Real.norm_eq_abs] using hmeasPair.norm
  have hintAbs : Integrable (fun a ↦ |pair a|) P := by
    refine Integrable.mono' hintProd hmeasAbs
      (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
    have hprod : 0 ≤ root a * load a :=
      mul_nonneg (Real.sqrt_nonneg _) (hload a)
    simpa only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hprod, root] using hpoint a
  have hmono : ∫ a, |pair a| ∂P ≤ ∫ a, root a * load a ∂P :=
    integral_mono hintAbs hintProd hpoint
  have hcs := integral_mul_le_sqrt_mul_sqrt hintRootSq hintLoadSq hintProd
  have hrootIntegral : ∫ a, root a ^ (2 : ℕ) ∂P =
      2 * ∫ a, energy a ∂P := by
    calc
      ∫ a, root a ^ (2 : ℕ) ∂P = ∫ a, 2 * energy a ∂P :=
        integral_congr_ae hrootSq
      _ = 2 * ∫ a, energy a ∂P := integral_const_mul 2 energy
  rw [hrootIntegral, hloadIntegral, Real.sqrt_sq hannealedLoad] at hcs
  exact hmono.trans hcs

private theorem integrable_mat_vec_mul_of_integrable
    {P : Measure (CoeffSpace d)} (g : Mat d) {F : CoeffSpace d → Vec d}
    (hF : Integrable F P) : Integrable (fun a ↦ matVecMul g (F a)) P := by
  apply Integrable.of_eval
  intro i
  simpa only [matVecMul] using integrable_finsetSum Finset.univ
    (fun j _ ↦ (hF.eval j).const_mul (g i j))

private theorem integrable_central_sub_skew_readout
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (s : ℤ)
    (hint : HasFiniteAdaptedMean P q s)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) (alpha : BlockCoord d) :
    Integrable (fun a ↦ toFullBlockVec (blockCellAverage (adaptedCell q s)
      (diagonalWeakState hq s (a.subSkew g hg) p r)) alpha) P := by
  let Y := fun a : CoeffSpace d ↦ blockCellAverage (adaptedCell q s)
    (diagonalWeakState hq s a p (r - matVecMul g p))
  have hY1 : Integrable (fun a ↦ (Y a).1) P := Integrable.of_eval fun i ↦ by
    let X : BlockVec d := (-p, r - matVecMul g p)
    have hmul := integrable_coarseBlock_mulVec_apply hint X (Sum.inr i)
    have hadd := hmul.add (integrable_const (X.1 i))
    refine hadd.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
    change toFullBlockVec (blockMatVecMul (coarseBlock (adaptedCell q s) a) X)
        (Sum.inr i) + X.1 i = (Y a).1 i
    dsimp only [Y]
    rw [blockCellAverage_diagonalWeakState_eq_response]
    simp only [blockMatVecMul_blockR, Prod.fst_add, Pi.add_apply,
      toFullBlockVec, X]
  have hY2 : Integrable (fun a ↦ (Y a).2) P := Integrable.of_eval fun i ↦ by
    let X : BlockVec d := (-p, r - matVecMul g p)
    have hmul := integrable_coarseBlock_mulVec_apply hint X (Sum.inl i)
    have hadd := hmul.add (integrable_const (X.2 i))
    refine hadd.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
    change toFullBlockVec (blockMatVecMul (coarseBlock (adaptedCell q s) a) X)
        (Sum.inl i) + X.2 i = (Y a).2 i
    dsimp only [Y]
    rw [blockCellAverage_diagonalWeakState_eq_response]
    simp only [blockMatVecMul_blockR, Prod.snd_add, Pi.add_apply,
      toFullBlockVec, X]
  have hY : Integrable Y P := integrable_prod.mpr ⟨hY1, hY2⟩
  have hfull := hY.fst.prodMk
    (hY.snd.sub (integrable_mat_vec_mul_of_integrable g hY.fst))
  have hfull' : Integrable (fun a ↦ blockCellAverage (adaptedCell q s)
      (diagonalWeakState hq s (a.subSkew g hg) p r)) P :=
    hfull.congr (_root_.Filter.Eventually.of_forall fun a ↦
      (blockCellAverage_diagonalWeakState_subSkew hq s a g hg p r).symm)
  cases alpha with
  | inl i => simpa only [toFullBlockVec] using hfull'.fst.eval i
  | inr i => simpa only [toFullBlockVec] using hfull'.snd.eval i

private theorem integrable_central_adjoint_sub_skew_readout
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (s : ℤ)
    (hint : HasFiniteAdaptedMean P q s)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d) (alpha : BlockCoord d) :
    Integrable (fun a ↦ toFullBlockVec (blockCellAverage (adaptedCell q s)
      (diagonalWeakState hq s (a.subSkew g hg).transpose p r)) alpha) P := by
  let Y := fun a : CoeffSpace d ↦ blockCellAverage (adaptedCell q s)
    (diagonalWeakState hq s a.transpose p (r + matVecMul g p))
  have hY1 : Integrable (fun a ↦ (Y a).1) P := Integrable.of_eval fun i ↦ by
    let X : BlockVec d := (-p, r + matVecMul g p)
    have hmul := integrable_adjoint_coarseBlock_mulVec_apply
      (adaptedDomain hq s) hint X (Sum.inr i)
    have hadd := hmul.add (integrable_const (X.1 i))
    refine hadd.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
    change toFullBlockVec
        (blockMatVecMul (coarseBlock (adaptedCell q s) a.transpose) X)
          (Sum.inr i) + X.1 i = (Y a).1 i
    dsimp only [Y]
    rw [blockCellAverage_diagonalWeakState_eq_response]
    simp only [blockMatVecMul_blockR, Prod.fst_add, Pi.add_apply,
      toFullBlockVec, X]
  have hY2 : Integrable (fun a ↦ (Y a).2) P := Integrable.of_eval fun i ↦ by
    let X : BlockVec d := (-p, r + matVecMul g p)
    have hmul := integrable_adjoint_coarseBlock_mulVec_apply
      (adaptedDomain hq s) hint X (Sum.inl i)
    have hadd := hmul.add (integrable_const (X.2 i))
    refine hadd.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
    change toFullBlockVec
        (blockMatVecMul (coarseBlock (adaptedCell q s) a.transpose) X)
          (Sum.inl i) + X.2 i = (Y a).2 i
    dsimp only [Y]
    rw [blockCellAverage_diagonalWeakState_eq_response]
    simp only [blockMatVecMul_blockR, Prod.snd_add, Pi.add_apply,
      toFullBlockVec, X]
  have hY : Integrable Y P := integrable_prod.mpr ⟨hY1, hY2⟩
  have hfull := hY.fst.prodMk
    (hY.snd.add (integrable_mat_vec_mul_of_integrable g hY.fst))
  have hfull' : Integrable (fun a ↦ blockCellAverage (adaptedCell q s)
      (diagonalWeakState hq s (a.subSkew g hg).transpose p r)) P :=
    hfull.congr (_root_.Filter.Eventually.of_forall fun a ↦ by
      change ((Y a).1, (Y a).2 + matVecMul g (Y a).1) =
        blockCellAverage (adaptedCell q s)
          (diagonalWeakState hq s (a.subSkew g hg).transpose p r)
      symm
      dsimp only [Y]
      rw [blockCellAverage_diagonalWeakState,
        blockCellAverage_diagonalWeakState]
      apply Prod.ext
      · exact averageGradient_centeredAdjointOptimizer_subSkew
          (adaptedDomain hq s) a g hg p r
      · exact averageFlux_centeredAdjointOptimizer_subSkew
          (adaptedDomain hq s) a g hg p r)
  cases alpha with
  | inl i => simpa only [toFullBlockVec] using hfull'.fst.eval i
  | inr i => simpa only [toFullBlockVec] using hfull'.snd.eval i

theorem integrable_child_sub_skew_readout
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l s : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q) (hls : l ≤ s)
    (hints : HasFiniteAdaptedMean P q s)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (w : Fin d → ℤ) (alpha : BlockCoord d) :
    Integrable (fun a ↦ toFullBlockVec
      (blockCellAverage (adaptedCellAt q s w)
        (diagonalWeakChildState (Recurrence.posDef_of_isRoundedGrid hgrid)
          s w (a.subSkew g hg) p r)) alpha) P := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  obtain ⟨z, _hz, hcov⟩ :=
    exists_blockCellAverage_diagonalWeakChildState_subSkew_eq_translateCoeff
      hgrid hls w g hg p r
  let G := fun a : CoeffSpace d ↦ toFullBlockVec
    (blockCellAverage (adaptedCell q s)
      (diagonalWeakState hq s (a.subSkew g hg) p r)) alpha
  have hG : Integrable G P :=
    integrable_central_sub_skew_readout hq s hints g hg p r alpha
  have hcomp : Integrable (G ∘ translateCoeff z) P :=
    ((Recurrence.measurePreserving_translateCoeff hstat z).integrable_comp
      hG.aestronglyMeasurable).2 hG
  refine hcomp.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  exact congrArg (fun X : BlockVec d ↦ toFullBlockVec X alpha) (hcov a).symm

theorem integrable_child_adjoint_sub_skew_readout
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l s : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q) (hls : l ≤ s)
    (hints : HasFiniteAdaptedMean P q s)
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (w : Fin d → ℤ) (alpha : BlockCoord d) :
    Integrable (fun a ↦ toFullBlockVec
      (blockCellAverage (adaptedCellAt q s w)
        (diagonalWeakChildState (Recurrence.posDef_of_isRoundedGrid hgrid)
          s w (a.subSkew g hg).transpose p r)) alpha) P := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  obtain ⟨z, _hz, hcov⟩ :=
    exists_blockCellAverage_diagonalWeakChildState_adjointSubSkew_eq_translateCoeff
      hgrid hls w g hg p r
  let G := fun a : CoeffSpace d ↦ toFullBlockVec
    (blockCellAverage (adaptedCell q s)
      (diagonalWeakState hq s (a.subSkew g hg).transpose p r)) alpha
  have hG : Integrable G P :=
    integrable_central_adjoint_sub_skew_readout hq s hints g hg p r alpha
  have hcomp : Integrable (G ∘ translateCoeff z) P :=
    ((Recurrence.measurePreserving_translateCoeff hstat z).integrable_comp
      hG.aestronglyMeasurable).2 hG
  refine hcomp.congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  exact congrArg (fun X : BlockVec d ↦ toFullBlockVec X alpha) (hcov a).symm

private theorem upper_left_pos_semidef {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpos : BlockPosDef H) :
    H.upperLeft.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simpa only [Matrix.conjTranspose, RCLike.star_def, Matrix.map_apply,
      Matrix.transpose_apply, conj_trivial, blockMatEntry] using
        hsymm (Sum.inl j) (Sum.inl i)
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp only [Matrix.mulVec_zero, dotProduct_zero, le_rfl]
    · have hX : ((x, 0) : BlockVec d) ≠ 0 := by
        intro hzero
        exact hx (congrArg Prod.fst hzero)
      have hquad := (hpos ((x, 0) : BlockVec d) hX).le
      simpa only [star_trivial, ge_iff_le, blockVecDot, blockMatVecMul,
        matVecMul_zero, add_zero, vecDot_zero_left] using! hquad

private theorem integrable_sq_schur_load_flux_hatted
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (k : ℤ) (w : Fin d → ℤ)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAt q k w))
    (g : Mat d) (Qcen : Vec d) :
    Integrable (fun a : CoeffSpace d ↦
      profileSchurLoadFlux
        (profileHattedBlock g (coarseBlock (adaptedCellAt q k w) a)) Qcen ^ 2) P := by
  refine (integrable_coarseBlock_quadratic hint
    ((0, Qcen) : BlockVec d)).congr
      (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  have hsymm := isSymmetricBlockMat_skewBlockCongr (g := g)
    (Recurrence.isSymmetricBlockMat_coarseBlock_adaptedCellAt q k w a)
  have hpos := blockPosDef_skewBlockCongr (g := g)
    (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq k w a)
  exact (sq_profileSchurLoadFlux_hatted_eq_blockQuadratic g _
    (posSemidef_lowerRight hsymm hpos)
    (isUnit_det_lowerRight hpos) Qcen).symm

private theorem integrable_sq_schur_load_gradient_hatted
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (k : ℤ) (w : Fin d → ℤ)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAt q k w))
    (g : Mat d) (Pcen : Vec d) :
    Integrable (fun a : CoeffSpace d ↦
      profileSchurLoadGradient
        (profileHattedBlock g (coarseBlock (adaptedCellAt q k w) a)) Pcen ^ 2) P := by
  refine (integrable_coarseBlock_quadratic hint
    ((Pcen, matVecMul g Pcen) : BlockVec d)).congr
      (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
  have hsymm := isSymmetricBlockMat_skewBlockCongr (g := g)
    (Recurrence.isSymmetricBlockMat_coarseBlock_adaptedCellAt q k w a)
  have hpos := blockPosDef_skewBlockCongr (g := g)
    (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq k w a)
  exact (sq_profileSchurLoadGradient_hatted_eq_blockQuadratic g _
    (upper_left_pos_semidef hsymm hpos) Pcen).symm

private theorem integral_sq_schur_load_flux_hatted_eq
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAt q k w))
    (g : Mat d) (Qcen : Vec d) :
    ∫ a, profileSchurLoadFlux
        (profileHattedBlock g (coarseBlock (adaptedCellAt q k w) a)) Qcen ^ 2 ∂P =
      profileSchurLoadFlux
        (profileHattedBlock g (annealedBlock P (adaptedCellAt q k w))) Qcen ^ 2 := by
  have hsymmA := isSymmetricBlockMat_skewBlockCongr (g := g)
    (Recurrence.isSymmetricBlockMat_annealedBlock P (adaptedCellAt q k w))
  have hposA := blockPosDef_skewBlockCongr (g := g)
    (Recurrence.blockPosDef_annealedBlock_adaptedCellAt hq k w hint)
  exact (integral_sq_profileSchurLoadFlux_hatted_eq hint g Qcen
    (posSemidef_lowerRight hsymmA hposA) (isUnit_det_lowerRight hposA)
    (fun a ↦ posSemidef_lowerRight
      (isSymmetricBlockMat_skewBlockCongr (g := g)
        (Recurrence.isSymmetricBlockMat_coarseBlock_adaptedCellAt q k w a))
      (blockPosDef_skewBlockCongr (g := g)
        (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq k w a)))
    (fun a ↦ isUnit_det_lowerRight
      (blockPosDef_skewBlockCongr (g := g)
        (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq k w a)))).symm

private theorem integral_sq_schur_load_gradient_hatted_eq
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAt q k w))
    (g : Mat d) (Pcen : Vec d) :
    ∫ a, profileSchurLoadGradient
        (profileHattedBlock g (coarseBlock (adaptedCellAt q k w) a)) Pcen ^ 2 ∂P =
      profileSchurLoadGradient
        (profileHattedBlock g (annealedBlock P (adaptedCellAt q k w))) Pcen ^ 2 := by
  have hsymmA := isSymmetricBlockMat_skewBlockCongr (g := g)
    (Recurrence.isSymmetricBlockMat_annealedBlock P (adaptedCellAt q k w))
  have hposA := blockPosDef_skewBlockCongr (g := g)
    (Recurrence.blockPosDef_annealedBlock_adaptedCellAt hq k w hint)
  exact (integral_sq_profileSchurLoadGradient_hatted_eq hint g Pcen
    (upper_left_pos_semidef hsymmA hposA)
    (fun a ↦ upper_left_pos_semidef
      (isSymmetricBlockMat_skewBlockCongr (g := g)
        (Recurrence.isSymmetricBlockMat_coarseBlock_adaptedCellAt q k w a))
      (blockPosDef_skewBlockCongr (g := g)
        (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq k w a)))).symm

private theorem primal_recent_cell_pairings_le
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l s t : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    (hls : l ≤ s) (hst : s ≤ t) (hints : HasFiniteAdaptedMean P q s)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q s t)
    (hparent : ∀ alpha, Integrable (fun a ↦ toFullBlockVec
      (blockCellAverage (adaptedCellAt q s w)
        (diagonalWeakState (Recurrence.posDef_of_isRoundedGrid hgrid)
          t (a.subSkew g hg) p r)) alpha) P) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let energy := fun a : CoeffSpace d ↦ (1 / 2 : ℝ) *
      average (adaptedDomainAt hq s w) (fun x ↦
        blockVecDot
          (diagonalWeakChildState hq s w (a.subSkew g hg) p r x -
            diagonalWeakState hq t (a.subSkew g hg) p r x)
          (blockMatVecMul (blockMatrixOfCoeff
              ((⇑(a.subSkew g hg).1 : CoeffField d) x))
            (diagonalWeakChildState hq s w (a.subSkew g hg) p r x -
              diagonalWeakState hq t (a.subSkew g hg) p r x)))
    |∑ i, Qcen i *
        ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
            (diagonalWeakChildState hq s w (a.subSkew g hg) p r))
              (Sum.inl i) ∂P) -
          ∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
            (diagonalWeakState hq t (a.subSkew g hg) p r))
              (Sum.inl i) ∂P)| ≤
        Real.sqrt (2 * ∫ a, energy a ∂P) *
          profileSchurLoadFlux
            (profileHattedBlock g (adaptedMean P q s)) Qcen ∧
      |∑ i, Pcen i *
        ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
            (diagonalWeakChildState hq s w (a.subSkew g hg) p r))
              (Sum.inr i) ∂P) -
          ∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
            (diagonalWeakState hq t (a.subSkew g hg) p r))
              (Sum.inr i) ∂P)| ≤
        Real.sqrt (2 * ∫ a, energy a ∂P) *
          profileSchurLoadGradient
            (profileHattedBlock g (adaptedMean P q s)) Pcen := by
  classical
  dsimp only
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let energy := fun a : CoeffSpace d ↦ (1 / 2 : ℝ) *
    average (adaptedDomainAt hq s w) (fun x ↦
      blockVecDot
        (diagonalWeakChildState hq s w (a.subSkew g hg) p r x -
          diagonalWeakState hq t (a.subSkew g hg) p r x)
        (blockMatVecMul (blockMatrixOfCoeff
            ((⇑(a.subSkew g hg).1 : CoeffField d) x))
          (diagonalWeakChildState hq s w (a.subSkew g hg) p r x -
            diagonalWeakState hq t (a.subSkew g hg) p r x)))
  let diff := fun a : CoeffSpace d ↦ blockCellAverage
    (adaptedCellAt q s w) (fun x ↦
      diagonalWeakChildState hq s w (a.subSkew g hg) p r x -
        diagonalWeakState hq t (a.subSkew g hg) p r x)
  let pairQ := fun a : CoeffSpace d ↦ vecDot Qcen (diff a).1
  let pairP := fun a : CoeffSpace d ↦ vecDot Pcen (diff a).2
  let loadQ := fun a : CoeffSpace d ↦ profileSchurLoadFlux
    (profileHattedBlock g (coarseBlock (adaptedCellAt q s w) a)) Qcen
  let loadP := fun a : CoeffSpace d ↦ profileSchurLoadGradient
    (profileHattedBlock g (coarseBlock (adaptedCellAt q s w) a)) Pcen
  have hintCell := Recurrence.hasIntegrableCoarseBlock_adaptedCellAt
    hstat hgrid hls hints w
  have henergyInt := profilePrimalRecentEnergy_integrable
    hstat hgrid hls hst hints g hg p r w hw
  have henergyNonneg : ∀ a, 0 ≤ energy a := fun a ↦
    mul_nonneg (by norm_num) (diagonalWeak_recent_difference_energy_nonneg
      hq hst hw (a.subSkew g hg) p r)
  have hpairInt : Integrable pairQ P ∧ Integrable pairP P := by
    constructor
    · refine (integrable_finsetSum Finset.univ (fun i _ ↦
          ((integrable_child_sub_skew_readout hstat hgrid hls hints g hg p r w
            (Sum.inl i)).sub (hparent (Sum.inl i))).const_mul (Qcen i))).congr
        (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
      dsimp only [pairQ, diff, vecDot]
      rw [blockCellAverage_recent_difference hq hst hw]
      rfl
    · refine (integrable_finsetSum Finset.univ (fun i _ ↦
          ((integrable_child_sub_skew_readout hstat hgrid hls hints g hg p r w
            (Sum.inr i)).sub (hparent (Sum.inr i))).const_mul (Pcen i))).congr
        (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
      dsimp only [pairP, diff, vecDot]
      rw [blockCellAverage_recent_difference hq hst hw]
      rfl
  have hpoint : ∀ a, |pairQ a| ≤ Real.sqrt (2 * energy a) * loadQ a ∧
      |pairP a| ≤ Real.sqrt (2 * energy a) * loadP a := by
    intro a
    have hbase := abs_vec_dot_recent_difference_le hq hst hw
      (a.subSkew g hg) p r Pcen Qcen
    have hcov := adaptedResponse_subSkew hq s w a g hg
    change coarseBlock (adaptedCellAt q s w) (a.subSkew g hg) =
      profileHattedBlock g (coarseBlock (adaptedCellAt q s w) a) at hcov
    rw [hcov] at hbase
    simpa only [energy, pairQ, pairP, diff, loadQ, loadP] using hbase
  have hmean := Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean hstat hgrid hls
    (fun alpha beta ↦ (hints alpha beta).aestronglyMeasurable) w
  have hQsq := integral_sq_schur_load_flux_hatted_eq hq s w hintCell g Qcen
  have hPsq := integral_sq_schur_load_gradient_hatted_eq hq s w hintCell g Pcen
  rw [hmean] at hQsq hPsq
  have hQlaw := integral_abs_pairing_le_sqrt_two_mul_energy henergyNonneg
    (fun a ↦ profileSchurLoadFlux_nonneg _ _) (profileSchurLoadFlux_nonneg _ _)
    (fun a ↦ (hpoint a).1) hpairInt.1.aestronglyMeasurable henergyInt
    (integrable_sq_schur_load_flux_hatted hq s w hintCell g Qcen) hQsq
  have hPlaw := integral_abs_pairing_le_sqrt_two_mul_energy henergyNonneg
    (fun a ↦ profileSchurLoadGradient_nonneg _ _)
    (profileSchurLoadGradient_nonneg _ _) (fun a ↦ (hpoint a).2)
    hpairInt.2.aestronglyMeasurable henergyInt
    (integrable_sq_schur_load_gradient_hatted hq s w hintCell g Pcen) hPsq
  have hQeq : (∫ a, pairQ a ∂P) = ∑ i, Qcen i *
      ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakChildState hq s w (a.subSkew g hg) p r))
            (Sum.inl i) ∂P) -
        ∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakState hq t (a.subSkew g hg) p r))
            (Sum.inl i) ∂P) := by
    rw [show (fun a ↦ pairQ a) = fun a ↦ ∑ i, Qcen i *
        (toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakChildState hq s w (a.subSkew g hg) p r)) (Sum.inl i) -
        toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakState hq t (a.subSkew g hg) p r)) (Sum.inl i)) by
      funext a
      dsimp only [pairQ, diff, vecDot]
      rw [blockCellAverage_recent_difference hq hst hw]
      rfl]
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul, integral_sub
        (integrable_child_sub_skew_readout hstat hgrid hls hints g hg p r w
          (Sum.inl i)) (hparent (Sum.inl i))]
    · intro i hi
      exact ((integrable_child_sub_skew_readout hstat hgrid hls hints g hg p r w
        (Sum.inl i)).sub (hparent (Sum.inl i))).const_mul (Qcen i)
  have hPeq : (∫ a, pairP a ∂P) = ∑ i, Pcen i *
      ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakChildState hq s w (a.subSkew g hg) p r))
            (Sum.inr i) ∂P) -
        ∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakState hq t (a.subSkew g hg) p r))
            (Sum.inr i) ∂P) := by
    rw [show (fun a ↦ pairP a) = fun a ↦ ∑ i, Pcen i *
        (toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakChildState hq s w (a.subSkew g hg) p r)) (Sum.inr i) -
        toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakState hq t (a.subSkew g hg) p r)) (Sum.inr i)) by
      funext a
      dsimp only [pairP, diff, vecDot]
      rw [blockCellAverage_recent_difference hq hst hw]
      rfl]
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul, integral_sub
        (integrable_child_sub_skew_readout hstat hgrid hls hints g hg p r w
          (Sum.inr i)) (hparent (Sum.inr i))]
    · intro i hi
      exact ((integrable_child_sub_skew_readout hstat hgrid hls hints g hg p r w
        (Sum.inr i)).sub (hparent (Sum.inr i))).const_mul (Pcen i)
  constructor
  · rw [← hQeq]
    exact abs_integral_le_integral_abs.trans hQlaw
  · rw [← hPeq]
    exact abs_integral_le_integral_abs.trans hPlaw

private theorem abs_avsum_le_avsum_abs {ι : Type*} (Z : Finset ι)
    (f : ι → ℝ) : |avsum Z f| ≤ avsum Z fun z ↦ |f z| := by
  unfold avsum
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- The two literal primal recent-defect rows have the full-energy
normalization dictated by the half-energy response defect. -/
theorem profile_primal_recent_defect_rows_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l s t : ℤ} {q m0 : Mat d} (hgrid : IsRoundedGrid l q)
    (hls : l ≤ s) (hst : s ≤ t)
    (hints : HasFiniteAdaptedMean P q s)
    (hintt : HasFiniteAdaptedMean P q t) (hm0 : m0.PosDef)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d)
    (hweak : profilePrimalWeakQuantity P m0
      (Recurrence.posDef_of_isRoundedGrid hgrid) t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let X := fun a ↦ diagonalWeakState hq t (a.subSkew g hg) p r
    let Y := fun w a ↦ diagonalWeakChildState hq s w (a.subSkew g hg) p r
    |avsum (alignedIndex q s t) (fun w ↦
        (1 - volumeAverage (adaptedCellAt q s w)
          (adaptedPreYoungCutoff q hq t)) *
        ∑ i, Qcen i *
          ((∫ a, toFullBlockVec
            (blockCellAverage (adaptedCellAt q s w) (Y w a))
              (Sum.inl i) ∂P) -
           ∫ a, toFullBlockVec
            (blockCellAverage (adaptedCellAt q s w) (X a))
              (Sum.inl i) ∂P))| ≤
      Real.sqrt (4 * profilePrimalResponseDefect P hq g hg s t p r) *
        profileSchurLoadFlux
          (profileHattedBlock g (adaptedMean P q s)) Qcen ∧
    |avsum (alignedIndex q s t) (fun w ↦
        (1 - volumeAverage (adaptedCellAt q s w)
          (adaptedPreYoungCutoff q hq t)) *
        ∑ i, Pcen i *
          ((∫ a, toFullBlockVec
            (blockCellAverage (adaptedCellAt q s w) (Y w a))
              (Sum.inr i) ∂P) -
           ∫ a, toFullBlockVec
            (blockCellAverage (adaptedCellAt q s w) (X a))
              (Sum.inr i) ∂P))| ≤
      Real.sqrt (4 * profilePrimalResponseDefect P hq g hg s t p r) *
        profileSchurLoadGradient
          (profileHattedBlock g (adaptedMean P q s)) Pcen := by
  classical
  dsimp only
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let Z := alignedIndex q s t
  let energy := fun (w : Fin d → ℤ) (a : CoeffSpace d) ↦ (1 / 2 : ℝ) *
    average (adaptedDomainAt hq s w) (fun x ↦
      blockVecDot
        (diagonalWeakChildState hq s w (a.subSkew g hg) p r x -
          diagonalWeakState hq t (a.subSkew g hg) p r x)
        (blockMatVecMul (blockMatrixOfCoeff
            ((⇑(a.subSkew g hg).1 : CoeffField d) x))
          (diagonalWeakChildState hq s w (a.subSkew g hg) p r x -
            diagonalWeakState hq t (a.subSkew g hg) p r x)))
  let defect := fun w : Fin d → ℤ ↦ ∫ a, energy w a ∂P
  let weight := fun w : Fin d → ℤ ↦ 1 - volumeAverage
    (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)
  let pairQ := fun w : Fin d → ℤ ↦ ∑ i, Qcen i *
    ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
      (diagonalWeakChildState hq s w (a.subSkew g hg) p r))
        (Sum.inl i) ∂P) -
     ∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
      (diagonalWeakState hq t (a.subSkew g hg) p r)) (Sum.inl i) ∂P)
  let pairP := fun w : Fin d → ℤ ↦ ∑ i, Pcen i *
    ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
      (diagonalWeakChildState hq s w (a.subSkew g hg) p r))
        (Sum.inr i) ∂P) -
     ∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
      (diagonalWeakState hq t (a.subSkew g hg) p r)) (Sum.inr i) ∂P)
  have henergyInt : ∀ w ∈ Z, Integrable (energy w) P :=
    profilePrimalRecentEnergy_integrable
      hstat hgrid hls hst hints g hg p r
  have hdefect := profilePrimalRecentEnergyDefect hstat hgrid hls hst
    hints hintt g hg p r henergyInt
  have hread := integrable_primal_adaptedFiveTermSplit_readouts
    hq hm0 hst g hg p r hweak
  have hcell : ∀ w ∈ Z,
      |pairQ w| ≤ Real.sqrt (2 * defect w) *
          profileSchurLoadFlux
            (profileHattedBlock g (adaptedMean P q s)) Qcen ∧
        |pairP w| ≤ Real.sqrt (2 * defect w) *
          profileSchurLoadGradient
            (profileHattedBlock g (adaptedMean P q s)) Pcen := by
    intro w hw
    simpa only [pairQ, pairP, defect, energy] using
      (primal_recent_cell_pairings_le hstat hgrid hls hst hints
        g hg p r Pcen Qcen hw (hread.1 w hw))
  have hweight : ∀ w ∈ Z, |weight w| ≤ 1 := by
    intro w hw
    dsimp only [weight]
    rw [volumeAverage_adaptedCellAt_eq_cubeAverage_pullback hq s w]
    exact abs_one_sub_cubeAverage_adaptedPreYoungCutoff_le_one hq t
      (translateCube w (originCube d s))
  have hdouble : avsum Z (fun w ↦ 2 * defect w) =
      2 * (2 * profilePrimalResponseDefect P hq g hg s t p r) := by
    rw [avsum_const_mul, hdefect.2]
  have hQ := avsum_weighted_le_sqrt_two_mul_defect
    (alignedIndex_nonempty hq hst)
    (profileSchurLoadFlux_nonneg _ _)
    (fun w hw ↦ mul_nonneg (by norm_num) (hdefect.1 w hw)) hweight
    (fun w hw ↦ by simpa only using (hcell w hw).1) hdouble
  have hP := avsum_weighted_le_sqrt_two_mul_defect
    (alignedIndex_nonempty hq hst)
    (profileSchurLoadGradient_nonneg _ _)
    (fun w hw ↦ mul_nonneg (by norm_num) (hdefect.1 w hw)) hweight
    (fun w hw ↦ by simpa only using (hcell w hw).2) hdouble
  constructor
  · have htri := abs_avsum_le_avsum_abs Z (fun w ↦ weight w * pairQ w)
    exact htri.trans (by
      simpa only [show 2 * (2 * profilePrimalResponseDefect P hq g hg s t p r) =
          4 * profilePrimalResponseDefect P hq g hg s t p r by ring] using hQ)
  · have htri := abs_avsum_le_avsum_abs Z (fun w ↦ weight w * pairP w)
    exact htri.trans (by
      simpa only [show 2 * (2 * profilePrimalResponseDefect P hq g hg s t p r) =
          4 * profilePrimalResponseDefect P hq g hg s t p r by ring] using hP)

private theorem profile_schur_load_flux_adjoint_eq
    (H : BlockMat d) (Qcen : Vec d) :
    profileSchurLoadFlux (profileAdjointBlock H) Qcen =
      profileSchurLoadFlux H Qcen := by
  rw [profileSchurLoadFlux, profileAdjointBlock,
    blockMatMul_blockDiag_one_neg_one]
  rfl

private theorem profile_schur_load_gradient_adjoint_eq
    (H : BlockMat d) (Pcen : Vec d) :
    profileSchurLoadGradient (profileAdjointBlock H) Pcen =
      profileSchurLoadGradient H Pcen := by
  rw [profileSchurLoadGradient, profileAdjointBlock,
    blockMatMul_blockDiag_one_neg_one]
  rfl

private theorem adjoint_recent_cell_pairings_le
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l s t : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    (hls : l ≤ s) (hst : s ≤ t) (hints : HasFiniteAdaptedMean P q s)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q s t)
    (hparent : ∀ alpha, Integrable (fun a ↦ toFullBlockVec
      (blockCellAverage (adaptedCellAt q s w)
        (diagonalWeakState (Recurrence.posDef_of_isRoundedGrid hgrid)
          t (a.subSkew g hg).transpose p r)) alpha) P) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let energy := fun a : CoeffSpace d ↦ (1 / 2 : ℝ) *
      average (adaptedDomainAt hq s w) (fun x ↦
        blockVecDot
          (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r x -
            diagonalWeakState hq t (a.subSkew g hg).transpose p r x)
          (blockMatVecMul (blockMatrixOfCoeff
              ((⇑(a.subSkew g hg).transpose.1 : CoeffField d) x))
            (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r x -
              diagonalWeakState hq t (a.subSkew g hg).transpose p r x)))
    |∑ i, Qcen i *
        ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
            (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r))
              (Sum.inl i) ∂P) -
          ∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
            (diagonalWeakState hq t (a.subSkew g hg).transpose p r))
              (Sum.inl i) ∂P)| ≤
        Real.sqrt (2 * ∫ a, energy a ∂P) *
          profileSchurLoadFlux
            (profileHattedAdjointBlock g (adaptedMean P q s)) Qcen ∧
      |∑ i, Pcen i *
        ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
            (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r))
              (Sum.inr i) ∂P) -
          ∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
            (diagonalWeakState hq t (a.subSkew g hg).transpose p r))
              (Sum.inr i) ∂P)| ≤
        Real.sqrt (2 * ∫ a, energy a ∂P) *
          profileSchurLoadGradient
            (profileHattedAdjointBlock g (adaptedMean P q s)) Pcen := by
  classical
  dsimp only
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let energy := fun a : CoeffSpace d ↦ (1 / 2 : ℝ) *
    average (adaptedDomainAt hq s w) (fun x ↦
      blockVecDot
        (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r x -
          diagonalWeakState hq t (a.subSkew g hg).transpose p r x)
        (blockMatVecMul (blockMatrixOfCoeff
            ((⇑(a.subSkew g hg).transpose.1 : CoeffField d) x))
          (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r x -
            diagonalWeakState hq t (a.subSkew g hg).transpose p r x)))
  let diff := fun a : CoeffSpace d ↦ blockCellAverage
    (adaptedCellAt q s w) (fun x ↦
      diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r x -
        diagonalWeakState hq t (a.subSkew g hg).transpose p r x)
  let pairQ := fun a : CoeffSpace d ↦ vecDot Qcen (diff a).1
  let pairP := fun a : CoeffSpace d ↦ vecDot Pcen (diff a).2
  let loadQ := fun a : CoeffSpace d ↦ profileSchurLoadFlux
    (profileHattedAdjointBlock g
      (coarseBlock (adaptedCellAt q s w) a)) Qcen
  let loadP := fun a : CoeffSpace d ↦ profileSchurLoadGradient
    (profileHattedAdjointBlock g
      (coarseBlock (adaptedCellAt q s w) a)) Pcen
  have hintCell := Recurrence.hasIntegrableCoarseBlock_adaptedCellAt
    hstat hgrid hls hints w
  have henergyInt := profileAdjointRecentEnergy_integrable
    hstat hgrid hls hst hints g hg p r w hw
  have henergyNonneg : ∀ a, 0 ≤ energy a := fun a ↦
    mul_nonneg (by norm_num) (diagonalWeak_recent_difference_energy_nonneg
      hq hst hw (a.subSkew g hg).transpose p r)
  have hpairInt : Integrable pairQ P ∧ Integrable pairP P := by
    constructor
    · refine (integrable_finsetSum Finset.univ (fun i _ ↦
          ((integrable_child_adjoint_sub_skew_readout hstat hgrid hls hints
            g hg p r w (Sum.inl i)).sub (hparent (Sum.inl i))).const_mul
            (Qcen i))).congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
      dsimp only [pairQ, diff, vecDot]
      rw [blockCellAverage_recent_difference hq hst hw]
      rfl
    · refine (integrable_finsetSum Finset.univ (fun i _ ↦
          ((integrable_child_adjoint_sub_skew_readout hstat hgrid hls hints
            g hg p r w (Sum.inr i)).sub (hparent (Sum.inr i))).const_mul
            (Pcen i))).congr (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
      dsimp only [pairP, diff, vecDot]
      rw [blockCellAverage_recent_difference hq hst hw]
      rfl
  have hpoint : ∀ a, |pairQ a| ≤ Real.sqrt (2 * energy a) * loadQ a ∧
      |pairP a| ≤ Real.sqrt (2 * energy a) * loadP a := by
    intro a
    have hbase := abs_vec_dot_recent_difference_le hq hst hw
      (a.subSkew g hg).transpose p r Pcen Qcen
    have htrans := adaptedResponse_transpose hq s w (a.subSkew g hg)
    change coarseBlock (adaptedCellAt q s w) (a.subSkew g hg).transpose =
      profileAdjointBlock
        (coarseBlock (adaptedCellAt q s w) (a.subSkew g hg)) at htrans
    have hsub := adaptedResponse_subSkew hq s w a g hg
    change coarseBlock (adaptedCellAt q s w) (a.subSkew g hg) =
      profileHattedBlock g (coarseBlock (adaptedCellAt q s w) a) at hsub
    rw [htrans, hsub] at hbase
    simpa only [energy, pairQ, pairP, diff, loadQ, loadP,
      profileHattedAdjointBlock] using hbase
  have hmean := Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean hstat hgrid hls
    (fun alpha beta ↦ (hints alpha beta).aestronglyMeasurable) w
  have hQsq := integral_sq_schur_load_flux_hatted_eq hq s w hintCell g Qcen
  have hPsq := integral_sq_schur_load_gradient_hatted_eq hq s w hintCell g Pcen
  rw [hmean] at hQsq hPsq
  have hQlaw := integral_abs_pairing_le_sqrt_two_mul_energy henergyNonneg
    (fun a ↦ profileSchurLoadFlux_nonneg _ _) (profileSchurLoadFlux_nonneg _ _)
    (fun a ↦ (hpoint a).1) hpairInt.1.aestronglyMeasurable henergyInt
    (by simpa only [loadQ, profileHattedAdjointBlock,
        profile_schur_load_flux_adjoint_eq] using
      integrable_sq_schur_load_flux_hatted hq s w hintCell g Qcen)
    (by simpa only [loadQ, profileHattedAdjointBlock,
        profile_schur_load_flux_adjoint_eq] using hQsq)
  have hPlaw := integral_abs_pairing_le_sqrt_two_mul_energy henergyNonneg
    (fun a ↦ profileSchurLoadGradient_nonneg _ _)
    (profileSchurLoadGradient_nonneg _ _) (fun a ↦ (hpoint a).2)
    hpairInt.2.aestronglyMeasurable henergyInt
    (by simpa only [loadP, profileHattedAdjointBlock,
        profile_schur_load_gradient_adjoint_eq] using
      integrable_sq_schur_load_gradient_hatted hq s w hintCell g Pcen)
    (by simpa only [loadP, profileHattedAdjointBlock,
        profile_schur_load_gradient_adjoint_eq] using hPsq)
  have hQeq : (∫ a, pairQ a ∂P) = ∑ i, Qcen i *
      ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r))
            (Sum.inl i) ∂P) -
        ∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakState hq t (a.subSkew g hg).transpose p r))
            (Sum.inl i) ∂P) := by
    rw [show (fun a ↦ pairQ a) = fun a ↦ ∑ i, Qcen i *
        (toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r))
            (Sum.inl i) -
        toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakState hq t (a.subSkew g hg).transpose p r))
            (Sum.inl i)) by
      funext a
      dsimp only [pairQ, diff, vecDot]
      rw [blockCellAverage_recent_difference hq hst hw]
      rfl]
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul, integral_sub
        (integrable_child_adjoint_sub_skew_readout hstat hgrid hls hints
          g hg p r w (Sum.inl i)) (hparent (Sum.inl i))]
    · intro i hi
      exact ((integrable_child_adjoint_sub_skew_readout hstat hgrid hls hints
        g hg p r w (Sum.inl i)).sub (hparent (Sum.inl i))).const_mul (Qcen i)
  have hPeq : (∫ a, pairP a ∂P) = ∑ i, Pcen i *
      ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r))
            (Sum.inr i) ∂P) -
        ∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakState hq t (a.subSkew g hg).transpose p r))
            (Sum.inr i) ∂P) := by
    rw [show (fun a ↦ pairP a) = fun a ↦ ∑ i, Pcen i *
        (toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r))
            (Sum.inr i) -
        toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakState hq t (a.subSkew g hg).transpose p r))
            (Sum.inr i)) by
      funext a
      dsimp only [pairP, diff, vecDot]
      rw [blockCellAverage_recent_difference hq hst hw]
      rfl]
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul, integral_sub
        (integrable_child_adjoint_sub_skew_readout hstat hgrid hls hints
          g hg p r w (Sum.inr i)) (hparent (Sum.inr i))]
    · intro i hi
      exact ((integrable_child_adjoint_sub_skew_readout hstat hgrid hls hints
        g hg p r w (Sum.inr i)).sub (hparent (Sum.inr i))).const_mul (Pcen i)
  constructor
  · rw [← hQeq]
    exact abs_integral_le_integral_abs.trans (by
      simpa only [profileHattedAdjointBlock,
        profile_schur_load_flux_adjoint_eq] using hQlaw)
  · rw [← hPeq]
    exact abs_integral_le_integral_abs.trans (by
      simpa only [profileHattedAdjointBlock,
        profile_schur_load_gradient_adjoint_eq] using hPlaw)

/-- The two literal adjoint recent-defect rows have the full-energy
normalization dictated by the transposed half-energy response defect. -/
theorem profile_adjoint_recent_defect_rows_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l s t : ℤ} {q m0 : Mat d} (hgrid : IsRoundedGrid l q)
    (hls : l ≤ s) (hst : s ≤ t)
    (hints : HasFiniteAdaptedMean P q s)
    (hintt : HasFiniteAdaptedMean P q t) (hm0 : m0.PosDef)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d)
    (hweak : profileAdjointWeakQuantity P m0
      (Recurrence.posDef_of_isRoundedGrid hgrid) t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let X := fun a ↦ diagonalWeakState hq t (a.subSkew g hg).transpose p r
    let Y := fun w a ↦
      diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r
    |avsum (alignedIndex q s t) (fun w ↦
        (1 - volumeAverage (adaptedCellAt q s w)
          (adaptedPreYoungCutoff q hq t)) *
        ∑ i, Qcen i *
          ((∫ a, toFullBlockVec
            (blockCellAverage (adaptedCellAt q s w) (Y w a))
              (Sum.inl i) ∂P) -
           ∫ a, toFullBlockVec
            (blockCellAverage (adaptedCellAt q s w) (X a))
              (Sum.inl i) ∂P))| ≤
      Real.sqrt (4 * profileAdjointResponseDefect P hq g hg s t p r) *
        profileSchurLoadFlux
          (profileHattedAdjointBlock g (adaptedMean P q s)) Qcen ∧
    |avsum (alignedIndex q s t) (fun w ↦
        (1 - volumeAverage (adaptedCellAt q s w)
          (adaptedPreYoungCutoff q hq t)) *
        ∑ i, Pcen i *
          ((∫ a, toFullBlockVec
            (blockCellAverage (adaptedCellAt q s w) (Y w a))
              (Sum.inr i) ∂P) -
           ∫ a, toFullBlockVec
            (blockCellAverage (adaptedCellAt q s w) (X a))
              (Sum.inr i) ∂P))| ≤
      Real.sqrt (4 * profileAdjointResponseDefect P hq g hg s t p r) *
        profileSchurLoadGradient
          (profileHattedAdjointBlock g (adaptedMean P q s)) Pcen := by
  classical
  dsimp only
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let Z := alignedIndex q s t
  let energy := fun (w : Fin d → ℤ) (a : CoeffSpace d) ↦ (1 / 2 : ℝ) *
    average (adaptedDomainAt hq s w) (fun x ↦
      blockVecDot
        (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r x -
          diagonalWeakState hq t (a.subSkew g hg).transpose p r x)
        (blockMatVecMul (blockMatrixOfCoeff
            ((⇑(a.subSkew g hg).transpose.1 : CoeffField d) x))
          (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r x -
            diagonalWeakState hq t (a.subSkew g hg).transpose p r x)))
  let defect := fun w : Fin d → ℤ ↦ ∫ a, energy w a ∂P
  let weight := fun w : Fin d → ℤ ↦ 1 - volumeAverage
    (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)
  let pairQ := fun w : Fin d → ℤ ↦ ∑ i, Qcen i *
    ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
      (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r))
        (Sum.inl i) ∂P) -
     ∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
      (diagonalWeakState hq t (a.subSkew g hg).transpose p r))
        (Sum.inl i) ∂P)
  let pairP := fun w : Fin d → ℤ ↦ ∑ i, Pcen i *
    ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
      (diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r))
        (Sum.inr i) ∂P) -
     ∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
      (diagonalWeakState hq t (a.subSkew g hg).transpose p r))
        (Sum.inr i) ∂P)
  have henergyInt : ∀ w ∈ Z, Integrable (energy w) P :=
    profileAdjointRecentEnergy_integrable
      hstat hgrid hls hst hints g hg p r
  have hdefect := profileAdjointRecentEnergyDefect hstat hgrid hls hst
    hints hintt g hg p r henergyInt
  have hread := integrable_adjoint_adaptedFiveTermSplit_readouts
    hq hm0 hst g hg p r hweak
  have hcell : ∀ w ∈ Z,
      |pairQ w| ≤ Real.sqrt (2 * defect w) *
          profileSchurLoadFlux
            (profileHattedAdjointBlock g (adaptedMean P q s)) Qcen ∧
        |pairP w| ≤ Real.sqrt (2 * defect w) *
          profileSchurLoadGradient
            (profileHattedAdjointBlock g (adaptedMean P q s)) Pcen := by
    intro w hw
    have hparent : ∀ alpha, Integrable (fun a ↦ toFullBlockVec
        (blockCellAverage (adaptedCellAt q s w)
          (diagonalWeakState hq t (a.subSkew g hg).transpose p r)) alpha) P := by
      intro alpha
      simpa only [diagonalWeakAdjointState_eq] using hread.1 w hw alpha
    simpa only [pairQ, pairP, defect, energy] using
      (adjoint_recent_cell_pairings_le hstat hgrid hls hst hints
        g hg p r Pcen Qcen hw hparent)
  have hweight : ∀ w ∈ Z, |weight w| ≤ 1 := by
    intro w hw
    dsimp only [weight]
    rw [volumeAverage_adaptedCellAt_eq_cubeAverage_pullback hq s w]
    exact abs_one_sub_cubeAverage_adaptedPreYoungCutoff_le_one hq t
      (translateCube w (originCube d s))
  have hdouble : avsum Z (fun w ↦ 2 * defect w) =
      2 * (2 * profileAdjointResponseDefect P hq g hg s t p r) := by
    rw [avsum_const_mul, hdefect.2]
  have hQ := avsum_weighted_le_sqrt_two_mul_defect
    (alignedIndex_nonempty hq hst)
    (profileSchurLoadFlux_nonneg _ _)
    (fun w hw ↦ mul_nonneg (by norm_num) (hdefect.1 w hw)) hweight
    (fun w hw ↦ by simpa only using (hcell w hw).1) hdouble
  have hP := avsum_weighted_le_sqrt_two_mul_defect
    (alignedIndex_nonempty hq hst)
    (profileSchurLoadGradient_nonneg _ _)
    (fun w hw ↦ mul_nonneg (by norm_num) (hdefect.1 w hw)) hweight
    (fun w hw ↦ by simpa only using (hcell w hw).2) hdouble
  constructor
  · have htri := abs_avsum_le_avsum_abs Z (fun w ↦ weight w * pairQ w)
    exact htri.trans (by
      simpa only [show 2 * (2 * profileAdjointResponseDefect P hq g hg s t p r) =
          4 * profileAdjointResponseDefect P hq g hg s t p r by ring] using hQ)
  · have htri := abs_avsum_le_avsum_abs Z (fun w ↦ weight w * pairP w)
    exact htri.trans (by
      simpa only [show 2 * (2 * profileAdjointResponseDefect P hq g hg s t p r) =
          4 * profileAdjointResponseDefect P hq g hg s t p r by ring] using hP)

end

end HCPolySupport.HighContrast.Response
