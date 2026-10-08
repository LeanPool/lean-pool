/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AdaptedDomainBridge
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseCalibrationBundles

/-!
# High-contrast homogenization: Entry.Response.Core.RecentredCoeffIntegrability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Integrability of the recentred coarse block

This file proves that the recentred coefficients `respCoeffMinus F a` and `respCoeffPlus F a` have
an integrable coarse block on the response cell, and that their annealed blocks agree with the
coefficient functional `respJ` evaluated at them. It shows the corresponding energies `respEJ^∓`
and trace term `respTau^+` are nonnegative, that the response mean is ordered correctly relative to
the raw sample, and that the recentred energy `respEhatPlus` is monotone. Supporting matrix and
domain-geometry facts about ellipticity under a skew correction and about the block congruence of
the coarse block are proved along the way. Together these supply the response-transfer result
`p.response.transfer`.
-/

section
open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock annealedBlock coarseBlock
  posDef_lowerRight schurSigma)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped ENNReal BigOperators
open scoped Matrix MatrixOrder

variable {d : ℕ}
/-- The adjoint congruence is Loewner-monotone too. -/
theorem respEhatPlus_mono (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ) (h : BlockMatLoewnerLE (respMean P jStar F t) (respMean P jStar F s)) :
    BlockMatLoewnerLE (respEhatPlus P jStar F t) (respEhatPlus P jStar F s) :=
  blockCongr_mono _ (blockCongr_mono _ h)

/-- `E_t <= E_s` at the two selected scales, straight from the raw output: `jStar < s < t`
and `Annealed.adaptedMean_antitone` (`e.response.imbalance.comparison`, `p.response.transfer`). -/
theorem respMean_order_of_raw (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (ε σ Cglob Cprof Csrc Bresp : ℝ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0) (hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
    (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
    (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ)
    (raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t) :
    BlockMatLoewnerLE (respMean P jStar F t) (respMean P jStar F s) := by
  have := raw.prob
  let : NeZero d := ⟨by omega⟩
  have hjs : (jStar : ℤ) < s :=
    jStar_lt_s_of_raw d hd γ hγ S ε σ Cglob Cprof Csrc Bresp hε hσ H P E Ψ Kg Src B jStar F s t raw
  have hm : (explicitCanonicalMetric F).PosDef :=
    HCPolySupport.HighContrast.Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos
  exact HCPolySupport.HighContrast.Annealed.adaptedMean_antitone d hd P γ E Ψ Kg Src raw.stat
    raw.ell
    jStar raw.hj (explicitCanonicalMetric F) hm s t (le_of_lt hjs) (le_of_lt raw.hst)

/-! ### Congruence helpers.

The annealed identification and the pathwise ellipticity inputs are derived here from the
skew-shear congruence `coarseBlockMatrix_sub_skew_eq_blockCongr`. -/

/-! #### Ellipticity under a constant skew shift -/

private theorem vecNormSq_matVecMul_le_opNormSq_of_norm (M : Mat d) (v : Vec d) :
    vecNormSq (matVecMul M v) ≤ ‖M‖ ^ 2 * vecNormSq v := by
  simpa [matVecMul] using! Geometry.vecNormSq_mulVec_le_opNorm M v

private theorem isUnit_det_of_coercive_hlower {lam : ℝ} (hlam : 0 < lam) {B : Mat d}
    (hlower : ∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul B ξ)) :
    IsUnit B.det := by
  have hinj : Function.Injective (matVecMul B) := by
    intro ξ η hξη
    have hzero : matVecMul B (ξ - η) = 0 := by
      rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg]; simp [hξη]
    have hl := hlower (ξ - η)
    rw [hzero] at hl
    have hzero' : vecDot (ξ - η) (0 : Vec d) = 0 := by simp [vecDot]
    rw [hzero'] at hl
    have hnorm_zero : vecNormSq (ξ - η) = 0 := by
      have h0 : lam * vecNormSq (ξ - η) = 0 :=
        le_antisymm hl (mul_nonneg hlam.le (vecNormSq_nonneg _))
      exact (mul_eq_zero.mp h0).resolve_left (ne_of_gt hlam)
    exact sub_eq_zero.mp (vecNormSq_eq_zero hnorm_zero)
  have hinj' : Function.Injective (B.mulVec) := by simpa [matVecMul] using! hinj
  exact (B.isUnit_iff_isUnit_det).mp ((Matrix.mulVec_injective_iff_isUnit (A := B)).mp hinj')

private theorem opBound_of_isEllipticMatrix_matVecMul {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (η : Vec d) :
    vecNormSq (matVecMul A η) ≤ Lam * vecDot η (matVecMul A η) := by
  have hdet : IsUnit A.det := isUnit_det_of_isEllipticMatrix hA
  obtain ⟨hlam_pos, hlamLam, -, hInv⟩ := hA
  have hLam_pos : 0 < Lam := lt_of_lt_of_le hlam_pos hlamLam
  have hInvMul : matVecMul A⁻¹ (matVecMul A η) = η := by
    rw [matVecMul_mul, Matrix.nonsing_inv_mul A hdet]
    funext i; simp [matVecMul, Matrix.one_apply]
  have hInvA : Lam⁻¹ * vecNormSq (matVecMul A η) ≤ vecDot (matVecMul A η) η := by
    simpa [hInvMul] using hInv (matVecMul A η)
  have hmul := mul_le_mul_of_nonneg_left hInvA (le_of_lt hLam_pos)
  have hLamInv : Lam * Lam⁻¹ = 1 := by field_simp
  calc vecNormSq (matVecMul A η)
      = (Lam * Lam⁻¹) * vecNormSq (matVecMul A η) := by rw [hLamInv, one_mul]
    _ = Lam * (Lam⁻¹ * vecNormSq (matVecMul A η)) := by ring
    _ ≤ Lam * vecDot (matVecMul A η) η := hmul
    _ = Lam * vecDot η (matVecMul A η) := by rw [vecDot_comm]

private theorem isEllipticMatrix_sub_skew_of_matTranspose {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (g : Mat d) (hg : matTranspose g = -g) :
    IsEllipticMatrix lam (2 * Lam + 2 * ‖g‖ ^ 2 / lam) (A - g) := by
  obtain ⟨hlam_pos, hlamLam, hlower, hInv⟩ := hA
  have hA' : IsEllipticMatrix lam Lam A := ⟨hlam_pos, hlamLam, hlower, hInv⟩
  have hLam_pos : 0 < Lam := lt_of_lt_of_le hlam_pos hlamLam
  have hterm_nonneg : 0 ≤ 2 * ‖g‖ ^ 2 / lam := div_nonneg (by positivity) hlam_pos.le
  have hLam'_pos : 0 < 2 * Lam + 2 * ‖g‖ ^ 2 / lam := by
    linarith only [hLam_pos, hterm_nonneg]
  have hlam_le' : lam ≤ 2 * Lam + 2 * ‖g‖ ^ 2 / lam := by
    linarith only [hlamLam, hLam_pos, hterm_nonneg]
  have hsplit : ∀ η : Vec d, matVecMul (A - g) η = matVecMul A η - matVecMul g η := by
    intro η; change (A - g).mulVec η = A.mulVec η - g.mulVec η; exact Matrix.sub_mulVec A g η
  have hlower' : ∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul (A - g) ξ) := by
    intro ξ
    rw [hsplit ξ]
    have heq : vecDot ξ (matVecMul A ξ - matVecMul g ξ)
        = vecDot ξ (matVecMul A ξ) - vecDot ξ (matVecMul g ξ) := by
      have hh := vecDot_add_right ξ (matVecMul A ξ) (-(matVecMul g ξ))
      simpa [sub_eq_add_neg, vecDot_neg_right] using hh
    rw [heq, vecDot_skew_self_of_matTranspose g hg ξ, sub_zero]
    exact hlower ξ
  have hB_unit : IsUnit (A - g).det := isUnit_det_of_coercive_hlower hlam_pos hlower'
  have hkey : ∀ η : Vec d,
      vecNormSq (matVecMul (A - g) η) ≤
        (2 * Lam + 2 * ‖g‖ ^ 2 / lam) * vecDot η (matVecMul (A - g) η) := by
    intro η
    have hAη := opBound_of_isEllipticMatrix_matVecMul hA' η
    have hgη : vecNormSq (matVecMul g η) ≤ (‖g‖ ^ 2 / lam) * vecDot η (matVecMul A η) := by
      have hb1 : vecNormSq (matVecMul g η) ≤ ‖g‖ ^ 2 * vecNormSq η :=
        vecNormSq_matVecMul_le_opNormSq_of_norm g η
      have hb2 : vecNormSq η ≤ vecDot η (matVecMul A η) / lam := by
        rw [le_div_iff₀ hlam_pos, mul_comm]
        exact hlower η
      have hb3 : ‖g‖ ^ 2 * vecNormSq η ≤ ‖g‖ ^ 2 * (vecDot η (matVecMul A η) / lam) :=
        mul_le_mul_of_nonneg_left hb2 (sq_nonneg _)
      calc vecNormSq (matVecMul g η) ≤ ‖g‖ ^ 2 * vecNormSq η := hb1
        _ ≤ ‖g‖ ^ 2 * (vecDot η (matVecMul A η) / lam) := hb3
        _ = (‖g‖ ^ 2 / lam) * vecDot η (matVecMul A η) := by ring
    have hcross : -(2 * vecDot (matVecMul A η) (matVecMul g η))
        ≤ vecNormSq (matVecMul A η) + vecNormSq (matVecMul g η) := by
      have hnn := vecNormSq_nonneg (matVecMul A η + matVecMul g η)
      rw [vecNormSq_add] at hnn
      linarith only [hnn]
    have hexpand : vecNormSq (matVecMul (A - g) η)
        = vecNormSq (matVecMul A η) - 2 * vecDot (matVecMul A η) (matVecMul g η)
          + vecNormSq (matVecMul g η) := by rw [hsplit η, vecNormSq_sub]
    rw [hexpand]
    have hq_eq : vecDot η (matVecMul (A - g) η) = vecDot η (matVecMul A η) := by
      rw [hsplit η]
      have hh := vecDot_add_right η (matVecMul A η) (-(matVecMul g η))
      simpa [sub_eq_add_neg, vecDot_neg_right, vecDot_skew_self_of_matTranspose g hg η] using hh
    rw [hq_eq]
    have hqexp : (2 * Lam + 2 * ‖g‖ ^ 2 / lam) * vecDot η (matVecMul A η)
        = 2 * (Lam * vecDot η (matVecMul A η))
          + 2 * ((‖g‖ ^ 2 / lam) * vecDot η (matVecMul A η)) := by ring
    rw [hqexp]
    linarith only [hAη, hgη, hcross]
  have hCond4 : ∀ ξ : Vec d,
      (2 * Lam + 2 * ‖g‖ ^ 2 / lam)⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul (A - g)⁻¹ ξ) := by
    intro ξ
    have hBη : matVecMul (A - g) (matVecMul (A - g)⁻¹ ξ) = ξ := by
      rw [matVecMul_mul, Matrix.mul_nonsing_inv (A - g) hB_unit]
      funext i; simp [matVecMul, Matrix.one_apply]
    have hk := hkey (matVecMul (A - g)⁻¹ ξ)
    rw [hBη] at hk
    have hle : vecNormSq ξ ≤ (2 * Lam + 2 * ‖g‖ ^ 2 / lam) *
        vecDot (matVecMul (A - g)⁻¹ ξ) ξ := hk
    rw [vecDot_comm (matVecMul (A - g)⁻¹ ξ) ξ] at hle
    rw [inv_mul_eq_div, div_le_iff₀ hLam'_pos, mul_comm]
    exact hle
  exact ⟨hlam_pos, hlam_le', hlower', hCond4⟩

private theorem isEllipticMatrix_add_skew_of_matTranspose {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (g : Mat d) (hg : matTranspose g = -g) :
    IsEllipticMatrix lam (2 * Lam + 2 * ‖g‖ ^ 2 / lam) (A + g) := by
  have hg' : matTranspose (-g) = -(-g) := by
    have hT : matTranspose (-g) = - matTranspose g := by
      funext i j; simp [matTranspose, Matrix.neg_apply]
    rw [hT, hg]
  have h := isEllipticMatrix_sub_skew_of_matTranspose hA (-g) hg'
  rw [norm_neg, sub_neg_eq_add] at h
  exact h

private theorem adaptedCell_nonempty (q : Mat d) (j : ℤ) :
    (HighContrast.adaptedCell q j).Nonempty := by
  classical
  have hzero : (0 : Vec d) ∈ HighContrast.centeredCube d j := by
    rw [HighContrast.centeredCube, mem_openCubeSet_originCube_iff]
    intro i
    have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
    constructor <;> dsimp <;> nlinarith only [h3]
  exact ⟨matVecMul q 0, 0, hzero, rfl⟩

private theorem volume_adaptedCell_toReal_pos (q : Mat d) (hq : IsUnit q) (j : ℤ) :
    0 < (volume (HighContrast.adaptedCell q j)).toReal := by
  have hdom := adaptedCell_isOpenBoundedConvexDomain q hq j
  have hne := hdom.isOpen.measure_ne_zero volume (adaptedCell_nonempty q j)
  exact ENNReal.toReal_pos hne hdom.volume_lt_top.ne

/-! #### From the pathwise shear congruence to the annealed block

The shear is a fixed congruence, so the entrywise integrals commute with it: both the annealed
identification and the entrywise integrability of the recentred block follow from the
carrier-field integrability `Annealed.hasIntegrableCoarseBlock_adapted`, using the skew-shear
congruence `coarseBlockMatrix_sub_skew_eq_blockCongr`. -/

/-- The skew shear congruence, with the quadraticity hypothesis in the form the adapted-cell
recovery theorem `isCoarseBlockMatrix_of_isOpenBoundedConvexDomain` produces. -/
private theorem coarseBlockMatrix_sub_skew_of_isCoarse {U : Set (Vec d)} {a : CoeffField d}
    {g : Mat d} (hg : matTranspose g = -g)
    (hA : IsCoarseBlockMatrix U a (coarseBlockMatrix U a)) :
    coarseBlockMatrix U (fun x => a x - g)
      = Multiscale.blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) (coarseBlockMatrix U a) := by
  have hnew : IsCoarseBlockMatrix U (fun x => a x - g)
      (Multiscale.blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) (coarseBlockMatrix U a)) := by
    refine ⟨isSymmetricBlockMat_blockCongr _ hA.1, ?_⟩
    intro Pv
    rw [Mu_sub_skew_shearLoad U a g hg Pv, blockVecDot_blockCongr,
      blockMatVecMul_shear_eq_shearLoad]
    exact hA.2 _
  exact (eq_coarseBlockMatrix_of_isCoarseBlockMatrix hnew).symm

private theorem ofFullBlockMat_fromBlocks_eq_mk (A B C D : Mat d) :
    ofFullBlockMat (Matrix.fromBlocks A B C D) = (⟨A, B, C, D⟩ : BlockMat d) := rfl

/-- The pathwise recentred block at an adapted cell is a fixed congruence of the carrier block,
by the shear congruence together with the adapted-cell coarse-block recovery. -/
private theorem coarseBlockMatrix_respCoeffMinus [NeZero d] (q : Mat d) (hq : IsUnit q)
    (u : ℤ) (F : BlockMat d) (hg : matTranspose (respg F) = -(respg F)) (a : CoeffSpace d) :
    coarseBlockMatrix (HighContrast.adaptedCell q u) (respCoeffMinus F a)
      = Multiscale.blockCongr (respG F) (coarseBlock (HighContrast.adaptedCell q u) a) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq u 0 a
  rw [Annealed.adaptedCellTranslate_zero] at hEll
  have hdom := adaptedCell_isOpenBoundedConvexDomain q hq u
  have hvol := volume_adaptedCell_toReal_pos q hq u
  have hA : IsCoarseBlockMatrix (HighContrast.adaptedCell q u) f
      (coarseBlockMatrix (HighContrast.adaptedCell q u) f) :=
    isCoarseBlockMatrix_of_isOpenBoundedConvexDomain hdom hEll hvol
  have h1 : coarseBlock (HighContrast.adaptedCell q u) a
      = coarseBlockMatrix (HighContrast.adaptedCell q u) f :=
    HCPolySupport.coarseBlockMatrix_congr_of_ae_eq (MeasureTheory.ae_restrict_of_ae hae)
  have hae1 : respCoeffMinus F a
      =ᵐ[MeasureTheory.volume.restrict (HighContrast.adaptedCell q u)] (fun x => f x - respg F) :=
    MeasureTheory.ae_restrict_of_ae (hae.mono fun x hx => by simp [respCoeffMinus, hx])
  rw [HCPolySupport.coarseBlockMatrix_congr_of_ae_eq hae1, h1,
    coarseBlockMatrix_sub_skew_of_isCoarse hg hA]
  rfl

/-- The adjoint twin. -/
private theorem coarseBlockMatrix_respCoeffPlus [NeZero d] (q : Mat d) (hq : IsUnit q)
    (u : ℤ) (F : BlockMat d) (hg : matTranspose (respg F) = -(respg F)) (a : CoeffSpace d) :
    coarseBlockMatrix (HighContrast.adaptedCell q u) (respCoeffPlus F a)
      = Multiscale.blockCongr (blockD d)
          (Multiscale.blockCongr (respG F) (coarseBlock (HighContrast.adaptedCell q u) a)) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq u 0 a
  rw [Annealed.adaptedCellTranslate_zero] at hEll
  have hdom := adaptedCell_isOpenBoundedConvexDomain q hq u
  have hvol := volume_adaptedCell_toReal_pos q hq u
  have hA : IsCoarseBlockMatrix (HighContrast.adaptedCell q u) f
      (coarseBlockMatrix (HighContrast.adaptedCell q u) f) :=
    isCoarseBlockMatrix_of_isOpenBoundedConvexDomain hdom hEll hvol
  have hgn : matTranspose (-(respg F)) = -(-(respg F)) := by
    have hT : matTranspose (-(respg F)) = - matTranspose (respg F) := by
      funext i j; simp [matTranspose, Matrix.neg_apply]
    rw [hT, hg]
  have hadjEq : coarseBlockMatrix (HighContrast.adaptedCell q u) (adjointCoeffField f)
      = blockMatFlipFlux (coarseBlockMatrix (HighContrast.adaptedCell q u) f) :=
    HCPolySupport.coarseBlockMatrix_adjointCoeffField_of_exists ⟨_, hA⟩
  have hadj : IsCoarseBlockMatrix (HighContrast.adaptedCell q u) (adjointCoeffField f)
      (coarseBlockMatrix (HighContrast.adaptedCell q u) (adjointCoeffField f)) := by
    rw [hadjEq]
    exact HCPolySupport.IsCoarseBlockMatrix.adjointCoeffField_symm hA
  have h1 : coarseBlock (HighContrast.adaptedCell q u) a
      = coarseBlockMatrix (HighContrast.adaptedCell q u) f :=
    HCPolySupport.coarseBlockMatrix_congr_of_ae_eq (MeasureTheory.ae_restrict_of_ae hae)
  have hae1 : respCoeffPlus F a
      =ᵐ[MeasureTheory.volume.restrict (HighContrast.adaptedCell q u)]
        (fun x => adjointCoeffField f x - -(respg F)) :=
    MeasureTheory.ae_restrict_of_ae (hae.mono fun x hx => by
      simp [respCoeffPlus, adjointCoeffField, hx, sub_neg_eq_add])
  rw [HCPolySupport.coarseBlockMatrix_congr_of_ae_eq hae1,
    coarseBlockMatrix_sub_skew_of_isCoarse hgn hadj, hadjEq, ← blockCongr_blockD,
    blockCongr_blockCongr, h1, blockCongr_blockCongr,
    blockD_mul_shear_neg (respg F)]
  rfl

/-! #### Passing a constant congruence through the entrywise annealing integrals -/

/-- Matrix whose entries are the integrals of the corresponding entries of `f` with respect to
`P`. -/
@[expose]
public noncomputable def entrywiseMatrixIntegral {ι : Type*} (P : Measure (CoeffSpace d))
    (f : CoeffSpace d → Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∫ a, f a i j ∂P

private theorem integrable_entries_mul_left_of_matrix {ι : Type*} [Fintype ι]
    {P : Measure (CoeffSpace d)} {f : CoeffSpace d → Matrix ι ι ℝ} (c : Matrix ι ι ℝ)
    (hf : ∀ i j, Integrable (fun a => f a i j) P) :
    ∀ i j, Integrable (fun a => (c * f a) i j) P := by
  classical
  intro i j
  simp only [Matrix.mul_apply]
  exact integrable_finsetSum _ fun k _ => (hf k j).const_mul _

private theorem matIntegral_mul_right_const {ι : Type*} [Fintype ι]
    {P : Measure (CoeffSpace d)} {f : CoeffSpace d → Matrix ι ι ℝ} (c : Matrix ι ι ℝ)
    (hf : ∀ i j, Integrable (fun a => f a i j) P) :
    entrywiseMatrixIntegral P (fun a => f a * c) = entrywiseMatrixIntegral P f * c := by
  classical
  ext i j
  simp only [entrywiseMatrixIntegral, Matrix.of_apply, Matrix.mul_apply]
  rw [MeasureTheory.integral_finsetSum _ fun k _ => (hf i k).mul_const (c k j)]
  exact Finset.sum_congr rfl fun k _ => MeasureTheory.integral_mul_const _ _

private theorem matIntegral_mul_left_const {ι : Type*} [Fintype ι]
    {P : Measure (CoeffSpace d)} {f : CoeffSpace d → Matrix ι ι ℝ} (c : Matrix ι ι ℝ)
    (hf : ∀ i j, Integrable (fun a => f a i j) P) :
    entrywiseMatrixIntegral P (fun a => c * f a) = c * entrywiseMatrixIntegral P f := by
  classical
  ext i j
  simp only [entrywiseMatrixIntegral, Matrix.of_apply, Matrix.mul_apply]
  rw [MeasureTheory.integral_finsetSum _ fun k _ => (hf k j).const_mul (c i k)]
  exact Finset.sum_congr rfl fun k _ => MeasureTheory.integral_const_mul _ _

/-- The annealed block of a constant congruence of the pathwise block is the congruence of the
annealed block. -/
private theorem annealedBlockOf_congr (P : Measure (CoeffSpace d)) (V : Set (Vec d))
    (G : BlockMat d) (b : CoeffSpace d → CoeffField d)
    (hint : HasIntegrableCoarseBlock P V)
    (hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix V (b a) = Multiscale.blockCongr G (coarseBlock V a)) :
    annealedBlockOf P V b = Multiscale.blockCongr G (annealedBlock P V) := by
  have hint' : ∀ α β, Integrable (fun a => toFullBlockMat (coarseBlock V a) α β) P := by
    intro α β
    have h := hint α β
    simpa only [blockMatEntry_eq_toFullBlockMat] using h
  have hfull : (fun a => toFullBlockMat (coarseBlockMatrix V (b a)))
      = fun a => (toFullBlockMat G)ᵀ * toFullBlockMat (coarseBlock V a) * toFullBlockMat G := by
    funext a
    rw [hb a]
    simp only [Multiscale.blockCongr, toFullBlockMat_ofFullBlockMat]
  have hL : annealedBlockOf P V b
      = ofFullBlockMat (entrywiseMatrixIntegral P
          (fun a => toFullBlockMat (coarseBlockMatrix V (b a)))) := by
    refine blockMat_ext ?_ ?_ ?_ ?_ <;> rfl
  have hR : annealedBlock P V
      = ofFullBlockMat (entrywiseMatrixIntegral P (fun a => toFullBlockMat (coarseBlock V a))) := by
    refine blockMat_ext ?_ ?_ ?_ ?_ <;> rfl
  rw [hL, hR, hfull,
    matIntegral_mul_right_const _ (integrable_entries_mul_left_of_matrix _ hint'),
    matIntegral_mul_left_const _ hint']
  simp only [Multiscale.blockCongr, toFullBlockMat_ofFullBlockMat]

/-- Entrywise `P`-integrability of the recentred coarse block transports from the carrier
field for free, because the shear is a fixed congruence and so each entry of the recentred block
is a fixed finite linear combination of entries of the carrier block. -/
private theorem integrable_entry_of_congr (P : Measure (CoeffSpace d)) (V : Set (Vec d))
    (G : BlockMat d) (b : CoeffSpace d → CoeffField d)
    (hint : HasIntegrableCoarseBlock P V)
    (hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix V (b a) = Multiscale.blockCongr G (coarseBlock V a)) :
    ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlockMatrix V (b a)) α β) P := by
  intro α β
  have hint' : ∀ γ δ : BlockCoord d,
      Integrable (fun a => toFullBlockMat (coarseBlock V a) γ δ) P := by
    intro γ δ
    have h := hint γ δ
    simpa only [blockMatEntry_eq_toFullBlockMat] using h
  have heq : (fun a => blockMatEntry (coarseBlockMatrix V (b a)) α β)
      = fun a => ∑ δ : BlockCoord d,
          (∑ γ : BlockCoord d,
            toFullBlockMat G γ α * toFullBlockMat (coarseBlock V a) γ δ)
          * toFullBlockMat G δ β := by
    funext a
    rw [blockMatEntry_eq_toFullBlockMat, hb a]
    simp only [Multiscale.blockCongr, toFullBlockMat_ofFullBlockMat, Matrix.mul_apply,
      Matrix.transpose_apply]
  rw [heq]
  exact integrable_finsetSum _ fun δ _ =>
    (integrable_finsetSum _ fun γ _ => (hint' γ δ).const_mul _).mul_const _

/-! #### The pathwise inputs at an adapted cell -/

/-- Pathwise nonnegativity of the recentred response on an adapted cell
(`e.response.energy.and.defect`). -/
theorem respJ_respCoeffMinus_nonneg (q : Mat d) (hq : IsUnit q) (u : ℤ)
    (F : BlockMat d) (hg : matTranspose (respg F) = -(respg F)) (a : CoeffSpace d) (p r : Vec d) :
    0 ≤ respJ q u p r (respCoeffMinus F a) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq u 0 a
  rw [Annealed.adaptedCellTranslate_zero] at hEll
  have hEll' := isEllipticFieldOn_sub_skew hEll (respg F) hg
  have hdom := adaptedCell_isOpenBoundedConvexDomain q hq u
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q u)) :=
    hdom.isFiniteMeasure_restrict_volume
  have hvol : (MeasureTheory.volume (HighContrast.adaptedCell q u)).toReal ≠ 0 :=
    ne_of_gt (volume_adaptedCell_toReal_pos q hq u)
  have hcongr : respJ q u p r (respCoeffMinus F a)
      = ResponseJ (HighContrast.adaptedCell q u) p r (fun x => f x - respg F) := by
    refine HCPolySupport.HighContrast.CG.responseJ_congr_of_ae_eq ?_ p r
    exact MeasureTheory.ae_restrict_of_ae (hae.mono fun x hx => by simp [respCoeffMinus, hx])
  rw [hcongr]
  exact (HCPolySupport.HighContrast.CG.responseJ_piece_bounds (ι := Unit) (s := (Set.univ : Set
    Unit))
    (W := HighContrast.adaptedCell q u) (U := fun _ => HighContrast.adaptedCell q u)
    (fun _ _ => hdom.isOpen) (fun _ _ => subset_rfl) hEll' p r (Set.mem_univ ()) hvol).1

/-- The adjoint twin. -/
theorem respJ_respCoeffPlus_nonneg (q : Mat d) (hq : IsUnit q) (u : ℤ)
    (F : BlockMat d) (hg : matTranspose (respg F) = -(respg F)) (a : CoeffSpace d) (p r : Vec d) :
    0 ≤ respJ q u p r (respCoeffPlus F a) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq u 0 a
  rw [Annealed.adaptedCellTranslate_zero] at hEll
  have hEll' := isEllipticFieldOn_transpose_add_skew hEll (respg F) hg
  have hdom := adaptedCell_isOpenBoundedConvexDomain q hq u
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q u)) :=
    hdom.isFiniteMeasure_restrict_volume
  have hvol : (MeasureTheory.volume (HighContrast.adaptedCell q u)).toReal ≠ 0 :=
    ne_of_gt (volume_adaptedCell_toReal_pos q hq u)
  have hcongr : respJ q u p r (respCoeffPlus F a)
      = ResponseJ (HighContrast.adaptedCell q u) p r (fun x => matTranspose (f x) + respg F) := by
    refine HCPolySupport.HighContrast.CG.responseJ_congr_of_ae_eq ?_ p r
    exact MeasureTheory.ae_restrict_of_ae (hae.mono fun x hx => by simp [respCoeffPlus, hx])
  rw [hcongr]
  exact (HCPolySupport.HighContrast.CG.responseJ_piece_bounds (ι := Unit) (s := (Set.univ : Set
    Unit))
    (W := HighContrast.adaptedCell q u) (U := fun _ => HighContrast.adaptedCell q u)
    (fun _ _ => hdom.isOpen) (fun _ _ => subset_rfl) hEll' p r (Set.mem_univ ()) hvol).1

/-- **AK.HC (2.15) at an adapted cell for the recentred sample** `a - g`
(`p.response.transfer`). -/
theorem respJ_eq_respCoeffMinus [NeZero d] (q : Mat d) (hq : IsUnit q) (u : ℤ)
    (F : BlockMat d) (hg : matTranspose (respg F) = -(respg F)) (a : CoeffSpace d) (p r : Vec d) :
    respJ q u p r (respCoeffMinus F a)
      = (1 / 2 : ℝ) * blockVecDot (-p, r)
          (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell q u) (respCoeffMinus F a))
            (-p, r))
        - vecDot p r := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq u 0 a
  rw [Annealed.adaptedCellTranslate_zero] at hEll
  have hEll' := isEllipticFieldOn_sub_skew hEll (respg F) hg
  have hae' : (respCoeffMinus F a)
      =ᵐ[MeasureTheory.volume.restrict (HighContrast.adaptedCell q u)] (fun x => f x - respg F) :=
    MeasureTheory.ae_restrict_of_ae (hae.mono fun x hx => by simp [respCoeffMinus, hx])
  have hdom := adaptedCell_isOpenBoundedConvexDomain q hq u
  have hvol := volume_adaptedCell_toReal_pos q hq u
  rw [respJ, HCPolySupport.HighContrast.CG.responseJ_congr_of_ae_eq hae' p r,
    HCPolySupport.coarseBlockMatrix_congr_of_ae_eq hae']
  exact HCPolySupport.HighContrast.CG.responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain
    hdom hEll'
    hvol p r

/-- The adjoint twin. -/
theorem respJ_eq_respCoeffPlus [NeZero d] (q : Mat d) (hq : IsUnit q) (u : ℤ)
    (F : BlockMat d) (hg : matTranspose (respg F) = -(respg F)) (a : CoeffSpace d) (p r : Vec d) :
    respJ q u p r (respCoeffPlus F a)
      = (1 / 2 : ℝ) * blockVecDot (-p, r)
          (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell q u) (respCoeffPlus F a))
            (-p, r))
        - vecDot p r := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq u 0 a
  rw [Annealed.adaptedCellTranslate_zero] at hEll
  have hEll' := isEllipticFieldOn_transpose_add_skew hEll (respg F) hg
  have hae' : (respCoeffPlus F a)
      =ᵐ[MeasureTheory.volume.restrict (HighContrast.adaptedCell q u)]
        (fun x => matTranspose (f x) + respg F) :=
    MeasureTheory.ae_restrict_of_ae (hae.mono fun x hx => by simp [respCoeffPlus, hx])
  have hdom := adaptedCell_isOpenBoundedConvexDomain q hq u
  have hvol := volume_adaptedCell_toReal_pos q hq u
  rw [respJ, HCPolySupport.HighContrast.CG.responseJ_congr_of_ae_eq hae' p r,
    HCPolySupport.coarseBlockMatrix_congr_of_ae_eq hae']
  exact HCPolySupport.HighContrast.CG.responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain
    hdom hEll'
    hvol p r

/-! #### The annealed identifications -/

/-- Carrier-field integrability at the selected cells, straight from the raw output. -/
theorem hasIntegrableCoarseBlock_respCell_of_raw (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
    (Src : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P)
    (hell : CoarseEllipticityDagger P γ E Ψ Kg Src) (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (u : ℤ) :
    HasIntegrableCoarseBlock P (respCell jStar F u) := by
  have h := Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ Kg Src hstat hell jStar hj
    (explicitCanonicalMetric F) hm u 0
  rwa [Annealed.adaptedCellTranslate_zero] at h

/-- The annealed block identification for the recentred coefficient:
`E[A(U_u; a - g)] = G^t E[A(U_u; a)] G`. -/
theorem annealedBlockOf_respCoeffMinus [NeZero d] (P : Measure (CoeffSpace d))
    (jStar : ℕ) (F : BlockMat d) (u : ℤ) (hq : IsUnit (respGrid jStar F))
    (hg : matTranspose (respg F) = -(respg F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F u)) :
    annealedBlockOf P (respCell jStar F u) (respCoeffMinus F) = respEhatMinus P jStar F u := by
  rw [annealedBlockOf_congr P (respCell jStar F u) (respG F) (respCoeffMinus F) hint
    (fun a => coarseBlockMatrix_respCoeffMinus (respGrid jStar F) hq u F hg a)]
  rfl

/-- The adjoint twin. -/
theorem annealedBlockOf_respCoeffPlus [NeZero d] (P : Measure (CoeffSpace d))
    (jStar : ℕ) (F : BlockMat d) (u : ℤ) (hq : IsUnit (respGrid jStar F))
    (hg : matTranspose (respg F) = -(respg F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F u)) :
    annealedBlockOf P (respCell jStar F u) (respCoeffPlus F) = respEhatPlus P jStar F u := by
  have hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix (respCell jStar F u) (respCoeffPlus F a)
        = Multiscale.blockCongr
            (ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d)))
            (coarseBlock (respCell jStar F u) a) := by
    intro a
    have h := coarseBlockMatrix_respCoeffPlus (respGrid jStar F) hq u F hg a
    rw [blockCongr_blockCongr] at h
    exact h
  rw [annealedBlockOf_congr P (respCell jStar F u) _ (respCoeffPlus F) hint hb,
    ← blockCongr_blockCongr]
  rfl

/-- Entrywise integrability of the recentred coarse block. -/
theorem integrable_respCoeffMinus [NeZero d] (P : Measure (CoeffSpace d))
    (jStar : ℕ) (F : BlockMat d) (u : ℤ) (hq : IsUnit (respGrid jStar F))
    (hg : matTranspose (respg F) = -(respg F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F u)) :
    ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (respCell jStar F u) (respCoeffMinus F a)) α β) P :=
  integrable_entry_of_congr P (respCell jStar F u) (respG F) (respCoeffMinus F) hint
    (fun a => coarseBlockMatrix_respCoeffMinus (respGrid jStar F) hq u F hg a)

/-- The adjoint twin. -/
theorem integrable_respCoeffPlus [NeZero d] (P : Measure (CoeffSpace d))
    (jStar : ℕ) (F : BlockMat d) (u : ℤ) (hq : IsUnit (respGrid jStar F))
    (hg : matTranspose (respg F) = -(respg F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F u)) :
    ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (respCell jStar F u) (respCoeffPlus F a)) α β) P :=
  integrable_entry_of_congr P (respCell jStar F u)
    (ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d))) (respCoeffPlus F) hint
    (fun a => by
      have h := coarseBlockMatrix_respCoeffPlus (respGrid jStar F) hq u F hg a
      rw [blockCongr_blockCongr] at h
      exact h)

/-- The defect at the plus load, conditional on the bridge inputs at the scale `s`. -/
theorem respTauPlus_eq (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (jStar : ℕ) (F : BlockMat d) (s t : ℤ) (e : Vec d)
    (hpath_s : ∀ a : CoeffSpace d,
      respJ (respGrid jStar F) s (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
          (respCoeffPlus F a)
        = (1 / 2 : ℝ) * blockVecDot (respxPlus P jStar F t e)
            (blockMatVecMul (coarseBlockMatrix (respCell jStar F s) (respCoeffPlus F a))
              (respxPlus P jStar F t e))
          - vecDot (respP (respMean P jStar F t) e) (respqPlus P jStar F t e))
    (hint_s : ∀ α β : BlockCoord d, Integrable (fun a =>
      blockMatEntry (coarseBlockMatrix (respCell jStar F s) (respCoeffPlus F a)) α β) P)
    (hann_s : annealedBlockOf P (respCell jStar F s) (respCoeffPlus F)
        = respEhatPlus P jStar F s)
    (hEJ : respEJPlus P jStar F t e = (1 / 2 : ℝ) * respLsqPlus P jStar F t e - 1)
    (hpq : vecDot (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) = 1) :
    respTauPlus P jStar F s t e
      = (1 / 2 : ℝ) * blockVecDot (respxPlus P jStar F t e)
          (blockMatVecMul (respEhatPlus P jStar F s) (respxPlus P jStar F t e))
        - (1 / 2 : ℝ) * respLsqPlus P jStar F t e := by
  have hs := integral_respJ P (respGrid jStar F) s (respP (respMean P jStar F t) e)
    (respqPlus P jStar F t e) (respCoeffPlus F) (respxPlus P jStar F t e)
    (respEhatPlus P jStar F s) hpath_s hint_s hann_s
  rw [respTauPlus, hs, hEJ, hpq]
  ring

/-- The plus defect is nonnegative once `Ehat_t^+ <= Ehat_s^+`. -/
theorem zero_le_respTauPlus (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (s t : ℤ) (e : Vec d)
    (hLoew : BlockMatLoewnerLE (respEhatPlus P jStar F t) (respEhatPlus P jStar F s))
    (hτ : respTauPlus P jStar F s t e
      = (1 / 2 : ℝ) * blockVecDot (respxPlus P jStar F t e)
          (blockMatVecMul (respEhatPlus P jStar F s) (respxPlus P jStar F t e))
        - (1 / 2 : ℝ) * respLsqPlus P jStar F t e) :
    0 ≤ respTauPlus P jStar F s t e := by
  have h := hLoew (respxPlus P jStar F t e)
  rw [hτ, respLsqPlus]
  linarith only [h]

/-! #### The side condition `hM`

`Analysis.swapConj_lowerRight` exposes `(schurSigma E)⁻¹` as the lower-right block of the swap
conjugate, so `posDef_lowerRight` applied there gives `schurSigma E` positive definite. -/

private theorem matTranspose_respSym (A : BlockMat d) :
    matTranspose (respSym A) = respSym A := by
  ext i j
  simp only [respSym, matTranspose, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.add_apply, smul_eq_mul]
  ring

private theorem schurSigma_posDef {A : BlockMat d} (hs : IsSymmetricBlockMat A)
    (hp : Book.Ch02.BlockPosDef A) : (schurSigma A).PosDef := by
  have hfull : (toFullBlockMat A).PosDef := posDef_toFullBlockMat hs hp
  have hsw := Analysis.swapConj_posDef hfull
  have hswS : IsSymmetricBlockMat (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat A)⁻¹ * toFullBlockMat (blockSwap d))) := by
    refine isSymmetricBlockMat_of_isSymm ?_
    have hherm := hsw.isHermitian
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      toFullBlockMat_ofFullBlockMat] at hherm
    exact hherm
  have h := posDef_lowerRight hswS (blockPosDef_of_full hsw)
  rw [Analysis.swapConj_lowerRight hs hp] at h
  exact Matrix.posDef_inv_iff.1 h

end HCPolySupport.HighContrast.Multiscale
end
