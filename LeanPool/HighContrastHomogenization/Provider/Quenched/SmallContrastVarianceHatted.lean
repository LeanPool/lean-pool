/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastVarianceCore
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastVarianceFrames
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenterSchur
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewNormalization
public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowCenteredBound

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastVarianceHatted

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The variance split at the recentered frame

The abstract variance split instantiated at the recentered coarse blocks
and means: every input transports through the shear congruence, the two
frame inputs are the recentered sharp bounds, and the conclusion returns
to the plain frame by the congruence invariance of the two-sided size.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem quad_split_two' {M : Mat d} (hM : M.PosSemidef)
    (a b : Vec d) :
    (a + b) ⬝ᵥ M *ᵥ (a + b) ≤
      2 * (a ⬝ᵥ M *ᵥ a) + 2 * (b ⬝ᵥ M *ᵥ b) := by
  have hswap : b ⬝ᵥ M *ᵥ a = a ⬝ᵥ M *ᵥ b := by
    rw [dotProduct_comm]
    exact mulVec_dotProduct_symm hM.isHermitian.eq a b
  have hminus : 0 ≤ (a - b) ⬝ᵥ M *ᵥ (a - b) := by
    have := hM.dotProduct_mulVec_nonneg (a - b)
    simpa using this
  have hexp₁ : (a + b) ⬝ᵥ M *ᵥ (a + b) =
      a ⬝ᵥ M *ᵥ a + 2 * (a ⬝ᵥ M *ᵥ b) + b ⬝ᵥ M *ᵥ b := by
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    rw [hswap]
    ring
  have hexp₂ : (a - b) ⬝ᵥ M *ᵥ (a - b) =
      a ⬝ᵥ M *ᵥ a - 2 * (a ⬝ᵥ M *ᵥ b) + b ⬝ᵥ M *ᵥ b := by
    simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
    rw [hswap]
    ring
  rw [hexp₂] at hminus
  rw [hexp₁]
  linarith only [hminus]

private theorem inv_smul_posDef' {A : FullBlockMat d} (hA : A.PosDef)
    {c : ℝ} (hc : 0 < c) : (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hA),
    inv_mul_cancel₀ (ne_of_gt hc), one_smul]

private theorem conj_mono'' {X Y : FullBlockMat d}
    (h : X ≤ Y) (M : FullBlockMat d) : Mᴴ * X * M ≤ Mᴴ * Y * M := by
  have hpsd : (Y - X).PosSemidef := Matrix.le_iff.mp h
  have hconj := hpsd.conjTranspose_mul_mul_same M
  refine Matrix.le_iff.mpr ?_
  have hrw : Mᴴ * (Y - X) * M = Mᴴ * Y * M - Mᴴ * X * M := by
    noncomm_ring
  rwa [hrw] at hconj

private theorem shifted_skew_quadratic_le_terminal_primal [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q) {j p : ℤ}
    (hlj : l ≤ j) (hjp : j ≤ p)
    (hintj : HasFiniteAdaptedMean P q j) (hintp : HasFiniteAdaptedMean P q p)
    {Sj SStarj Kj Sp SStarp Kp h0 : Mat d}
    (hStarj : SStarj.PosDef) (hSp : Sp.PosDef) (hStarp : SStarp.PosDef)
    (hformj : toFullBlockMat (adaptedMean P q j) = schurBlock Sj SStarj Kj)
    (hformp : toFullBlockMat (adaptedMean P q p) = schurBlock Sp SStarp Kp)
    {epsj : ℝ} (hposj : 0 ≤ epsj) (hepsj1 : epsj ≤ 1)
    (hdropSmall : 4 * (d : ℝ) *
      (adaptedHattedContrast P q j - adaptedHattedContrast P q p) ≤ 1)
    (hh0def : h0 = Response.responseSkew Kj)
    (hstarpinvle : SStarp⁻¹ ≤ SStarj⁻¹) (hstarcross : SStarj ≤ SStarp)
    (horderp : SStarp ≤ Sp)
    (hskewMj : Response.responseSymmetric Kj * SStarj⁻¹ *
      Response.responseSymmetric Kj ≤ (epsj ^ 2 / 4) • SStarj) :
    ∀ x : Vec d,
      ((Kp - h0) *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ ((Kp - h0) *ᵥ x) ≤
        x ⬝ᵥ Sp *ᵥ x := by
  classical
  have hKhat : ∀ x : Vec d,
      ((Kp - h0) *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ ((Kp - h0) *ᵥ x) ≤
        x ⬝ᵥ Sp *ᵥ x := by
    intro x
    -- the good-quadratics skew difference
    have hgq := adaptedMean_normalized_schur_good_quads_le_hattedContrast_drop
      hstat hq hlj hjp hintj hintp
    have hgq2 := le_trans (le_max_right _ _) hgq
    obtain ⟨hLRp, _hstp, hskp, hsgp⟩ := schurData_of_form hStarp hformp
    obtain ⟨_hLRj, _hstj, hskj, _hsgj⟩ := schurData_of_form hStarj hformj
    rw [hLRp, hskj, hskp, hsgp] at hgq2
    have hΔq := quad_le_of_norm_normalized_le hSp hStarp hgq2 x
    -- decompose the shifted skew
    have hsplitK : (Kp - h0) *ᵥ x =
        -((Kj - Kp) *ᵥ x) + Response.responseSymmetric Kj *ᵥ x := by
      have hKp : Kp - h0 = -(Kj - Kp) + (Kj - h0) := by abel
      have hKj0 : Kj - h0 = Response.responseSymmetric Kj := by
        rw [hh0def]
        exact Response.sub_responseSkew Kj
      rw [hKp, hKj0, Matrix.add_mulVec, Matrix.neg_mulVec]
    -- the two pieces
    have hquadsplit : ((Kp - h0) *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ
        ((Kp - h0) *ᵥ x) ≤
        2 * (((Kj - Kp) *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ ((Kj - Kp) *ᵥ x)) +
          2 * ((Response.responseSymmetric Kj *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ
            (Response.responseSymmetric Kj *ᵥ x)) := by
      rw [hsplitK]
      have h := quad_split_two' hStarp.inv.posSemidef
        (-((Kj - Kp) *ᵥ x)) (Response.responseSymmetric Kj *ᵥ x)
      have hneg : (-((Kj - Kp) *ᵥ x)) ⬝ᵥ SStarp⁻¹ *ᵥ
          (-((Kj - Kp) *ᵥ x)) =
          ((Kj - Kp) *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ ((Kj - Kp) *ᵥ x) := by
        rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
      rwa [hneg] at h
    -- the drop piece
    have hdropnn : 0 ≤
        adaptedHattedContrast P q j - adaptedHattedContrast P q p :=
      sub_nonneg.mpr (adaptedHattedContrast_le hstat hq hlj hjp hintj
        hintp)
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hxSp0 : 0 ≤ x ⬝ᵥ Sp *ᵥ x := by
      have := hSp.posSemidef.dotProduct_mulVec_nonneg x
      simpa using this
    have hΔsmall : ((Kj - Kp) *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ
        ((Kj - Kp) *ᵥ x) ≤ (1 / 16) * (x ⬝ᵥ Sp *ᵥ x) := by
      refine hΔq.trans ?_
      have hdd : ((d : ℝ) *
          (adaptedHattedContrast P q j - adaptedHattedContrast P q p)) ^
            2 ≤ 1 / 16 := by
        nlinarith only [hdropSmall, hdropnn, hd0,
          mul_nonneg hd0 hdropnn]
      exact mul_le_mul_of_nonneg_right hdd hxSp0
    -- the symmetric piece
    have hκpiece : (Response.responseSymmetric Kj *ᵥ x) ⬝ᵥ SStarp⁻¹ *ᵥ
        (Response.responseSymmetric Kj *ᵥ x) ≤
        (1 / 4) * (x ⬝ᵥ Sp *ᵥ x) := by
      have h1 := Initialization.dotProduct_mulVec_le_of_le hstarpinvle
        (Response.responseSymmetric Kj *ᵥ x)
      have hks : (Response.responseSymmetric Kj)ᴴ = Response.responseSymmetric Kj :=
        Response.responseSymmetric_isHermitian Kj
      have hkq : x ⬝ᵥ (Response.responseSymmetric Kj * SStarj⁻¹ *
          Response.responseSymmetric Kj) *ᵥ x =
          (Response.responseSymmetric Kj *ᵥ x) ⬝ᵥ SStarj⁻¹ *ᵥ
            (Response.responseSymmetric Kj *ᵥ x) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          ← mulVec_dotProduct_symm hks]
      have h2 := Initialization.dotProduct_mulVec_le_of_le hskewMj x
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hkq] at h2
      have h3 := Initialization.dotProduct_mulVec_le_of_le hstarcross x
      have h4 := Initialization.dotProduct_mulVec_le_of_le horderp x
      have hX0 : 0 ≤ x ⬝ᵥ SStarj *ᵥ x := by
        have := hStarj.posSemidef.dotProduct_mulVec_nonneg x
        simpa using this
      have heps2 : epsj ^ 2 / 4 ≤ 1 / 4 := by
        nlinarith only [hposj, hepsj1]
      have h5 : epsj ^ 2 / 4 * (x ⬝ᵥ SStarj *ᵥ x) ≤
          1 / 4 * (x ⬝ᵥ SStarj *ᵥ x) :=
        mul_le_mul_of_nonneg_right heps2 hX0
      linarith only [h1, h2, h3, h4, h5, hX0]
    linarith only [hquadsplit, hΔsmall, hκpiece, hxSp0]
  exact hKhat

private theorem recentered_coarse_block_dominates_sharp
    {q : Mat d} (hqpd : q.PosDef) (p : ℤ) (a : CoeffSpace d)
    (h0 : Mat d) (hh0 : IsSkewMat h0) :
    fullBlockSharp (toFullBlockMat
      (Response.skewBlockCongr h0 (coarseBlock (adaptedCell q p) a))) ≤
      toFullBlockMat
        (Response.skewBlockCongr h0 (coarseBlock (adaptedCell q p) a)) := by
  classical
  have hparentSharp : fullBlockSharp (toFullBlockMat
      (Response.skewBlockCongr h0 (coarseBlock (adaptedCell q p) a))) ≤
      toFullBlockMat
        (Response.skewBlockCongr h0 (coarseBlock (adaptedCell q p) a)) := by
    have hdom : IsOpenBoundedConvexDomain
        ((Response.adaptedDomain hqpd p : Domain d) : Set (Vec d)) :=
      (Response.adaptedDomain hqpd p).isDomain
    have hcell : coarseBlock
        ((Response.adaptedDomain hqpd p : Domain d) : Set (Vec d))
        (a.subSkew h0 hh0) =
        Response.skewBlockCongr h0
          (coarseBlock
            ((Response.adaptedDomain hqpd p : Domain d) : Set (Vec d)) a) :=
      Response.coarseBlock_subSkew (Response.adaptedDomain hqpd p) a h0 hh0
    have hsharp := Sharp.blockMatLoewnerLE_blockSharp_coarseBlock_of_nonempty
      hdom (Response.adaptedDomain hqpd p).nonempty (a.subSkew h0 hh0)
    rw [hcell] at hsharp
    have hsymm : IsSymmetricBlockMat
        (Response.skewBlockCongr h0
          (coarseBlock
            ((Response.adaptedDomain hqpd p : Domain d) : Set (Vec d)) a)) :=
      Response.isSymmetricBlockMat_skewBlockCongr (g := h0)
        (isSymmetricBlockMat_coarseBlock _ a)
    have hsymmSharp : IsSymmetricBlockMat
        (blockSharp (Response.skewBlockCongr h0
          (coarseBlock
            ((Response.adaptedDomain hqpd p : Domain d) : Set (Vec d)) a))) := by
      refine isSymmetricBlockMat_of_posSemidef ?_
      rw [toFullBlockMat_blockSharp]
      refine (posDef_fullBlockSharp ?_).posSemidef
      exact posDef_toFullBlockMat hsymm
        (Response.blockPosDef_skewBlockCongr (g := h0)
          (Sharp.blockPosDef_coarseBlock_of_volume_pos hdom
            (ENNReal.toReal_pos
              (hdom.isOpen.measure_pos volume
                (Response.adaptedDomain hqpd p).nonempty).ne'
              hdom.volume_lt_top.ne) a))
    have h := le_of_blockMatLoewnerLE hsymmSharp hsymm hsharp
    rw [toFullBlockMat_blockSharp] at h
    simpa only [Response.adaptedDomain_carrier] using h
  exact hparentSharp

private theorem recentered_adapted_mean_dominates_sharp
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hqpd : q.PosDef) (j : ℤ)
    (hintj : HasFiniteAdaptedMean P q j)
    (hintj' : HasIntegrableCoarseBlock P
      ((Response.adaptedDomain hqpd j : Domain d) : Set (Vec d)))
    (h0 : Mat d) (hh0 : IsSkewMat h0) :
    fullBlockSharp (toFullBlockMat
      (Response.skewBlockCongr h0 (adaptedMean P q j))) ≤
      toFullBlockMat (Response.skewBlockCongr h0 (adaptedMean P q j)) := by
  classical
  have hsharpJle : fullBlockSharp (toFullBlockMat
      (Response.skewBlockCongr h0 (adaptedMean P q j))) ≤
      toFullBlockMat (Response.skewBlockCongr h0 (adaptedMean P q j)) := by
    have hb := blockSharp_skewBlockCongr_annealedBlock_le
      (Response.adaptedDomain hqpd j) hintj' h0 hh0
    have hsymm : IsSymmetricBlockMat
        (Response.skewBlockCongr h0
          (annealedBlock P
            ((Response.adaptedDomain hqpd j : Domain d) : Set (Vec d)))) :=
      Response.isSymmetricBlockMat_skewBlockCongr (g := h0)
        (Recurrence.isSymmetricBlockMat_annealedBlock P _)
    have hsymmSharp : IsSymmetricBlockMat
        (blockSharp (Response.skewBlockCongr h0
          (annealedBlock P
            ((Response.adaptedDomain hqpd j : Domain d) : Set (Vec d))))) := by
      refine isSymmetricBlockMat_of_posSemidef ?_
      rw [toFullBlockMat_blockSharp]
      refine (posDef_fullBlockSharp ?_).posSemidef
      refine posDef_toFullBlockMat hsymm ?_
      refine Response.blockPosDef_skewBlockCongr (g := h0) ?_
      have h := Recurrence.blockPosDef_adaptedMean hqpd j hintj
      simpa only [adaptedMean, Response.adaptedDomain_carrier] using h
    have h := le_of_blockMatLoewnerLE hsymmSharp hsymm hb
    rw [toFullBlockMat_blockSharp] at h
    simpa only [adaptedMean, Response.adaptedDomain_carrier] using h
  exact hsharpJle

private theorem recentered_coarse_parent_le_average [NeZero d]
    {q : Mat d} (hqpd : q.PosDef) {j p : ℤ} (hjp : j ≤ p)
    {Z : Finset (Fin d → ℤ)}
    (hZ : (↑Z : Set (Fin d → ℤ)) =
      {w : Fin d → ℤ | adaptedCellCenter q j w ∈ adaptedCell q p})
    (a : CoeffSpace d) (h0 : Mat d) {Sh : FullBlockMat d}
    (hShdef : Sh = fullBlockShear h0) {A : (Fin d → ℤ) → FullBlockMat d}
    (hAfull : ∀ w, A w = Shᴴ *
      toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) * Sh) :
    toFullBlockMat
      (Response.skewBlockCongr h0 (coarseBlock (adaptedCell q p) a)) ≤
      (Z.card : ℝ)⁻¹ • ∑ w ∈ Z, A w := by
  classical
  have hparentLe : toFullBlockMat
      (Response.skewBlockCongr h0 (coarseBlock (adaptedCell q p) a)) ≤
      (Z.card : ℝ)⁻¹ • ∑ w ∈ Z, A w := by
    have hplain := Recurrence.toFullBlockMat_coarseBlock_adaptedCell_le_average
      hqpd hjp hZ a
    have hconj := conj_mono'' hplain Sh
    have hlhs : Shᴴ *
        toFullBlockMat (coarseBlock (adaptedCell q p) a) * Sh =
        toFullBlockMat
          (Response.skewBlockCongr h0 (coarseBlock (adaptedCell q p) a)) := by
      rw [Response.toFullBlockMat_skewBlockCongr, hShdef]
    have hrhs : Shᴴ * ((Z.card : ℝ)⁻¹ •
        ∑ w ∈ Z,
          toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)) * Sh =
        (Z.card : ℝ)⁻¹ • ∑ w ∈ Z, A w := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun w _hw => (hAfull w).symm
    rw [hlhs, hrhs] at hconj
    exact hconj
  exact hparentLe

private theorem recentered_parent_fluctuation_norm_eq_block_size
    {P : Measure (CoeffSpace d)} {q : Mat d} (p : ℤ)
    (a : CoeffSpace d) (h0 : Mat d)
    (hGpsym : IsSymmetricBlockMat (Response.skewBlockCongr h0 (adaptedMean P q p)))
    (hGpblock : Book.Ch02.BlockPosDef (Response.skewBlockCongr h0 (adaptedMean P q p))) :
    ‖matSqrt (toFullBlockMat
        (Response.skewBlockCongr h0 (adaptedMean P q p)))⁻¹ *
      (toFullBlockMat
        (Response.skewBlockCongr h0 (coarseBlock (adaptedCell q p) a)) -
        toFullBlockMat (Response.skewBlockCongr h0 (adaptedMean P q p))) *
      matSqrt (toFullBlockMat
        (Response.skewBlockCongr h0 (adaptedMean P q p)))⁻¹‖ =
      blockSize
        (blockSub (coarseBlock (adaptedCell q p) a) (adaptedMean P q p))
        (adaptedMean P q p) := by
  classical
  have hLHSeq : ‖matSqrt (toFullBlockMat
        (Response.skewBlockCongr h0 (adaptedMean P q p)))⁻¹ *
      (toFullBlockMat
        (Response.skewBlockCongr h0 (coarseBlock (adaptedCell q p) a)) -
        toFullBlockMat (Response.skewBlockCongr h0 (adaptedMean P q p))) *
      matSqrt (toFullBlockMat
        (Response.skewBlockCongr h0 (adaptedMean P q p)))⁻¹‖ =
      blockSize
        (blockSub (coarseBlock (adaptedCell q p) a) (adaptedMean P q p))
        (adaptedMean P q p) := by
    rw [← Response.blockSize_skewBlockCongr h0
      (blockSub (coarseBlock (adaptedCell q p) a) (adaptedMean P q p))
      (adaptedMean P q p)]
    rw [PortableHistory.blockSize_eq_norm
      (Response.isSymmetricBlockMat_skewBlockCongr (g := h0)
        (isSymmetricBlockMat_blockSub
          (isSymmetricBlockMat_coarseBlock _ a)
          (Recurrence.isSymmetricBlockMat_adaptedMean P q p)))
      hGpsym hGpblock]
    congr 1
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat,
      Response.blockSub_skewBlockCongr, Transport.toFullBlockMat_blockSub]
  exact hLHSeq

private theorem recentered_average_fluctuation_norm_eq_block_size
    {P : Measure (CoeffSpace d)} {q : Mat d} (hqpd : q.PosDef) (j p : ℤ)
    (a : CoeffSpace d) (h0 : Mat d) (Z : Finset (Fin d → ℤ))
    {A : (Fin d → ℤ) → FullBlockMat d}
    (hGpsym : IsSymmetricBlockMat (Response.skewBlockCongr h0 (adaptedMean P q p)))
    (hGpblock : Book.Ch02.BlockPosDef (Response.skewBlockCongr h0 (adaptedMean P q p)))
    (havgfull : (Z.card : ℝ)⁻¹ • ∑ w ∈ Z, A w =
      toFullBlockMat (Response.skewBlockCongr h0
        (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
          ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a))))) :
    ‖matSqrt (toFullBlockMat
        (Response.skewBlockCongr h0 (adaptedMean P q p)))⁻¹ *
      ((Z.card : ℝ)⁻¹ • ∑ w ∈ Z, A w -
        toFullBlockMat (Response.skewBlockCongr h0 (adaptedMean P q j))) *
      matSqrt (toFullBlockMat
        (Response.skewBlockCongr h0 (adaptedMean P q p)))⁻¹‖ =
      blockSize
        (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
          ∑ w ∈ Z,
            toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
          (adaptedMean P q j))
        (adaptedMean P q p) := by
  classical
  have hAvgeq : ‖matSqrt (toFullBlockMat
        (Response.skewBlockCongr h0 (adaptedMean P q p)))⁻¹ *
      ((Z.card : ℝ)⁻¹ • ∑ w ∈ Z, A w -
        toFullBlockMat (Response.skewBlockCongr h0 (adaptedMean P q j))) *
      matSqrt (toFullBlockMat
        (Response.skewBlockCongr h0 (adaptedMean P q p)))⁻¹‖ =
      blockSize
        (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
          ∑ w ∈ Z,
            toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
          (adaptedMean P q j))
        (adaptedMean P q p) := by
    rw [← Response.blockSize_skewBlockCongr h0
      (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
        ∑ w ∈ Z,
          toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
        (adaptedMean P q j))
      (adaptedMean P q p)]
    have havgSym : IsSymmetricBlockMat
        (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
          ∑ w ∈ Z,
            toFullBlockMat (coarseBlock (adaptedCellAt q j w) a))) := by
      refine isSymmetricBlockMat_of_posSemidef ?_
      rw [toFullBlockMat_ofFullBlockMat]
      refine Matrix.PosSemidef.smul ?_ (by positivity : (0 : ℝ) ≤ _)
      refine Matrix.posSemidef_sum Z fun w hw => ?_
      exact (posDef_toFullBlockMat
        (Recurrence.isSymmetricBlockMat_coarseBlock_adaptedCellAt q j w a)
        (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hqpd j w a)).posSemidef
    rw [PortableHistory.blockSize_eq_norm
      (Response.isSymmetricBlockMat_skewBlockCongr (g := h0)
        (isSymmetricBlockMat_blockSub havgSym
          (Recurrence.isSymmetricBlockMat_adaptedMean P q j)))
      hGpsym hGpblock]
    congr 1
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat,
      Response.blockSub_skewBlockCongr, Transport.toFullBlockMat_blockSub, havgfull]
  exact hAvgeq

private theorem terminal_star_inverse_quadratic_comparison
    {P : Measure (CoeffSpace d)} {q : Mat d} {j p : ℤ}
    {Sj SStarj Kj Sp SStarp Kp : Mat d} (hStarp : SStarp.PosDef)
    (hformj : toFullBlockMat (adaptedMean P q j) = schurBlock Sj SStarj Kj)
    (hformp : toFullBlockMat (adaptedMean P q p) = schurBlock Sp SStarp Kp)
    (hdropSmall : 4 * (d : ℝ) *
      (adaptedHattedContrast P q j - adaptedHattedContrast P q p) ≤ 1)
    (hdilplain : toFullBlockMat (adaptedMean P q j) ≤
      (1 + 4 * (d : ℝ) *
        (adaptedHattedContrast P q j - adaptedHattedContrast P q p)) •
          toFullBlockMat (adaptedMean P q p)) :
    ∀ y : Vec d,
      y ⬝ᵥ SStarj⁻¹ *ᵥ y ≤ 2 * (y ⬝ᵥ SStarp⁻¹ *ᵥ y) := by
  classical
  have hdilquad : ∀ y : Vec d,
      y ⬝ᵥ SStarj⁻¹ *ᵥ y ≤ 2 * (y ⬝ᵥ SStarp⁻¹ *ᵥ y) := by
    intro y
    have h := Initialization.dotProduct_mulVec_le_of_le hdilplain (Sum.elim 0 y)
    rw [hformj] at h
    have hsmul : Sum.elim (0 : Vec d) y ⬝ᵥ
        ((1 + 4 * (d : ℝ) *
          (adaptedHattedContrast P q j - adaptedHattedContrast P q p)) •
          toFullBlockMat (adaptedMean P q p)) *ᵥ Sum.elim (0 : Vec d) y =
        (1 + 4 * (d : ℝ) *
          (adaptedHattedContrast P q j - adaptedHattedContrast P q p)) *
          (Sum.elim (0 : Vec d) y ⬝ᵥ
            toFullBlockMat (adaptedMean P q p) *ᵥ
              Sum.elim (0 : Vec d) y) := by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [hsmul, hformp, Response.quadratic_schurBlock,
      Response.quadratic_schurBlock] at h
    simp only [Matrix.mulVec_zero, dotProduct_zero, sub_zero,
      zero_add] at h
    have hq2 : 0 ≤ y ⬝ᵥ SStarp⁻¹ *ᵥ y := by
      have := hStarp.inv.posSemidef.dotProduct_mulVec_nonneg y
      simpa using this
    have hcoef : 1 + 4 * (d : ℝ) *
        (adaptedHattedContrast P q j - adaptedHattedContrast P q p) ≤
        2 := by
      linarith only [hdropSmall]
    nlinarith only [h, hq2, hcoef]
  exact hdilquad

private theorem sharp_inverse_le_four_inverse {A : FullBlockMat d} (hA : A.PosDef)
    (horder : A ≤ (4 : ℝ) • fullBlockSharp A) :
    (fullBlockSharp A)⁻¹ ≤ (4 : ℝ) • A⁻¹ := by
  have hsharppd : (fullBlockSharp A).PosDef := posDef_fullBlockSharp hA
  have hsmulpd : ((4 : ℝ) • fullBlockSharp A).PosDef :=
    hsharppd.smul (by norm_num)
  have hinv := inv_le_inv_of_le hA hsmulpd horder
  rw [inv_smul_posDef' hsharppd (by norm_num : (0 : ℝ) < 4)] at hinv
  have h := smul_le_smul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 4)
  rwa [smul_smul, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0),
    one_smul] at h

/-- **The pathwise variance replacement**, plain-frame conclusion. -/
theorem blockSize_variance_replacement_pathwise [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q) {j p : ℤ}
    (hlj : l ≤ j) (hjp : j ≤ p)
    (hintj : HasFiniteAdaptedMean P q j)
    (hintp : HasFiniteAdaptedMean P q p)
    {Sj SStarj Kj : Mat d} (hSj : Sj.PosDef) (hStarj : SStarj.PosDef)
    (hformj : toFullBlockMat (adaptedMean P q j) = schurBlock Sj SStarj Kj)
    {Sp SStarp Kp : Mat d} (hSp : Sp.PosDef) (hStarp : SStarp.PosDef)
    (hformp : toFullBlockMat (adaptedMean P q p) = schurBlock Sp SStarp Kp)
    {epsj epsp : ℝ}
    (hposj : 0 ≤ epsj) (hepsj1 : epsj ≤ 1)
    (htrj : (d : ℝ) * (schurHattedContrast Sj SStarj - 1) ≤ epsj)
    (hposp : 0 < epsp) (hepsp1 : epsp ≤ 1)
    (htrp : (d : ℝ) * (schurHattedContrast Sp SStarp - 1) ≤ epsp)
    (hposj' : 0 < epsj)
    (hdropSmall : 4 * (d : ℝ) *
      (adaptedHattedContrast P q j - adaptedHattedContrast P q p) ≤ 1)
    {Z : Finset (Fin d → ℤ)}
    (hZ : (↑Z : Set (Fin d → ℤ)) =
      {w : Fin d → ℤ | adaptedCellCenter q j w ∈ adaptedCell q p})
    (hZne : Z.Nonempty)
    (a : CoeffSpace d) :
    blockSize
        (blockSub (coarseBlock (adaptedCell q p) a) (adaptedMean P q p))
        (adaptedMean P q p) ≤
      (2 + 4 * (1 + 4 * (d : ℝ) *
          (adaptedHattedContrast P q j - adaptedHattedContrast P q p)) ^
            2) *
        blockSize
          (blockSub (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
            ∑ w ∈ Z,
              toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))
            (adaptedMean P q j))
          (adaptedMean P q p) +
      4 * (1 + 4 * (d : ℝ) *
          (adaptedHattedContrast P q j - adaptedHattedContrast P q p)) ^
            2 * (36 * epsj) +
      4 * (d : ℝ) *
        (adaptedHattedContrast P q j - adaptedHattedContrast P q p) := by
  classical
  have hqpd : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  set h0 : Mat d := Response.responseSkew Kj with hh0def
  have hh0 : IsSkewMat h0 := Response.is_skew_mat_response_skew Kj
  set Sh : FullBlockMat d := fullBlockShear h0 with hShdef
  -- the smallness packs
  have hintj' : HasIntegrableCoarseBlock P
      ((Response.adaptedDomain hqpd j : Domain d) : Set (Vec d)) := by
    simpa only [Response.adaptedDomain_carrier] using! hintj
  have hEj' : toFullBlockMat
      (annealedBlock P
        ((Response.adaptedDomain hqpd j : Domain d) : Set (Vec d))) =
      schurBlock Sj SStarj Kj := by
    simpa only [adaptedMean, Response.adaptedDomain_carrier] using hformj
  obtain ⟨horderj, hgapMj, hskewMj, _htrGj, _htrSj⟩ :=
    centering_smallness_supply (Response.adaptedDomain hqpd j) hintj' hSj
      hStarj hEj' hposj' htrj
  have hintp' : HasIntegrableCoarseBlock P
      ((Response.adaptedDomain hqpd p : Domain d) : Set (Vec d)) := by
    simpa only [Response.adaptedDomain_carrier] using! hintp
  have hEp' : toFullBlockMat
      (annealedBlock P
        ((Response.adaptedDomain hqpd p : Domain d) : Set (Vec d))) =
      schurBlock Sp SStarp Kp := by
    simpa only [adaptedMean, Response.adaptedDomain_carrier] using hformp
  obtain ⟨horderp, hgapMp, hskewMp, _htrGp, _htrSp⟩ :=
    centering_smallness_supply (Response.adaptedDomain hqpd p) hintp' hSp
      hStarp hEp' hposp htrp
  -- the hatted means and their Schur forms
  have hE2j : toFullBlockMat (Response.skewBlockCongr h0 (adaptedMean P q j)) =
      schurBlock Sj SStarj (Response.responseSymmetric Kj) := by
    have h := toFullBlockMat_skewBlockCongr_of_schurBlock h0 hformj
    rw [hh0def] at h ⊢
    rwa [Response.sub_responseSkew Kj] at h
  have hE2p : toFullBlockMat (Response.skewBlockCongr h0 (adaptedMean P q p)) =
      schurBlock Sp SStarp (Kp - h0) :=
    toFullBlockMat_skewBlockCongr_of_schurBlock h0 hformp
  -- posdefs of the hatted means
  have hGjblock : Book.Ch02.BlockPosDef
      (Response.skewBlockCongr h0 (adaptedMean P q j)) :=
    Response.blockPosDef_skewBlockCongr (g := h0)
      (Recurrence.blockPosDef_adaptedMean hqpd j hintj)
  have hGjsym : IsSymmetricBlockMat
      (Response.skewBlockCongr h0 (adaptedMean P q j)) :=
    Response.isSymmetricBlockMat_skewBlockCongr (g := h0)
      (Recurrence.isSymmetricBlockMat_adaptedMean P q j)
  have hGpblock : Book.Ch02.BlockPosDef
      (Response.skewBlockCongr h0 (adaptedMean P q p)) :=
    Response.blockPosDef_skewBlockCongr (g := h0)
      (Recurrence.blockPosDef_adaptedMean hqpd p hintp)
  have hGpsym : IsSymmetricBlockMat
      (Response.skewBlockCongr h0 (adaptedMean P q p)) :=
    Response.isSymmetricBlockMat_skewBlockCongr (g := h0)
      (Recurrence.isSymmetricBlockMat_adaptedMean P q p)
  have hGj : (toFullBlockMat
      (Response.skewBlockCongr h0 (adaptedMean P q j))).PosDef :=
    posDef_toFullBlockMat hGjsym hGjblock
  have hGp : (toFullBlockMat
      (Response.skewBlockCongr h0 (adaptedMean P q p))).PosDef :=
    posDef_toFullBlockMat hGpsym hGpblock
  -- the hatted parent and children
  have hApblock : Book.Ch02.BlockPosDef
      (Response.skewBlockCongr h0 (coarseBlock (adaptedCell q p) a)) :=
    Response.blockPosDef_skewBlockCongr (g := h0)
      (Recurrence.blockPosDef_coarseBlock_adaptedCell hqpd p a)
  have hApsym : IsSymmetricBlockMat
      (Response.skewBlockCongr h0 (coarseBlock (adaptedCell q p) a)) :=
    Response.isSymmetricBlockMat_skewBlockCongr (g := h0)
      (isSymmetricBlockMat_coarseBlock _ a)
  have hAp : (toFullBlockMat
      (Response.skewBlockCongr h0 (coarseBlock (adaptedCell q p) a))).PosDef :=
    posDef_toFullBlockMat hApsym hApblock
  set A : (Fin d → ℤ) → FullBlockMat d := fun w =>
    toFullBlockMat (Response.skewBlockCongr h0
      (coarseBlock (adaptedCellAt q j w) a)) with hAdef
  have hA : ∀ w ∈ Z, (A w).PosDef := by
    intro w _hw
    exact posDef_toFullBlockMat
      (Response.isSymmetricBlockMat_skewBlockCongr (g := h0)
        (Recurrence.isSymmetricBlockMat_coarseBlock_adaptedCellAt q j w a))
      (Response.blockPosDef_skewBlockCongr (g := h0)
        (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hqpd j w a))
  -- transported average domination
  have hAfull : ∀ w, A w = Shᴴ *
      toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) * Sh := by
    intro w
    change toFullBlockMat (Response.skewBlockCongr h0
      (coarseBlock (adaptedCellAt q j w) a)) = _
    rw [Response.toFullBlockMat_skewBlockCongr, hShdef]
  have hparentLe := recentered_coarse_parent_le_average hqpd hjp hZ a h0 hShdef
    hAfull
  -- the hatted parent dominates its sharp
  have hparentSharp := recentered_coarse_block_dominates_sharp hqpd p a h0 hh0
  -- the hatted lower-scale mean dominates its sharp
  have hsharpJle := recentered_adapted_mean_dominates_sharp hqpd j hintj hintj' h0 hh0
  -- transported order and dilation
  have hordermean := Recurrence.toFullBlockMat_adaptedMean_le hstat hq hlj hjp
    hintj hintp
  have horder : toFullBlockMat
      (Response.skewBlockCongr h0 (adaptedMean P q p)) ≤
      toFullBlockMat (Response.skewBlockCongr h0 (adaptedMean P q j)) := by
    have hconj := conj_mono'' hordermean Sh
    rw [Response.toFullBlockMat_skewBlockCongr,
      Response.toFullBlockMat_skewBlockCongr]
    exact hconj
  have hdrop1 : (d : ℝ) *
      (adaptedHattedContrast P q j - adaptedHattedContrast P q p) ≤ 1 := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hdropnn : 0 ≤
        adaptedHattedContrast P q j - adaptedHattedContrast P q p :=
      sub_nonneg.mpr (adaptedHattedContrast_le hstat hq hlj hjp hintj
        hintp)
    nlinarith only [hdropSmall, hd0, hdropnn]
  have hdilplain := adaptedMean_le_hattedContrast_dilation hstat hq hlj
    hjp hintj hintp hdrop1
  have hdil : toFullBlockMat
      (Response.skewBlockCongr h0 (adaptedMean P q j)) ≤
      (1 + 4 * (d : ℝ) *
        (adaptedHattedContrast P q j - adaptedHattedContrast P q p)) •
        toFullBlockMat (Response.skewBlockCongr h0 (adaptedMean P q p)) := by
    have hconj := conj_mono'' hdilplain Sh
    rw [Response.toFullBlockMat_skewBlockCongr,
      Response.toFullBlockMat_skewBlockCongr]
    refine hconj.trans (le_of_eq ?_)
    rw [Matrix.mul_smul, Matrix.smul_mul]
  -- the two frame inputs
  have hO1 := hatted_sharp_inverse_bound hSp hStarp hposp.le hepsp1
    hgapMp hskewMp h0 hh0
  have hsharpPinv := sharp_inverse_le_four_inverse hGp (by
    rw [hE2p]
    exact hO1)
  -- the cross-scale facts for the gap input
  have hstarpinvle : SStarp⁻¹ ≤ SStarj⁻¹ := by
    refine Initialization.le_of_dotProduct_mulVec_le hStarp.inv.isHermitian
      hStarj.inv.isHermitian fun y => ?_
    have h := Initialization.dotProduct_mulVec_le_of_le hordermean (Sum.elim 0 y)
    rw [hformj, hformp, Response.quadratic_schurBlock,
      Response.quadratic_schurBlock] at h
    simpa [Matrix.mulVec_zero, dotProduct_zero, zero_dotProduct] using h
  have hstarcross : SStarj ≤ SStarp := by
    have h := inv_le_inv_of_le hStarp.inv hStarj.inv hstarpinvle
    rwa [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hStarp),
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hStarj)]
      at h
  have hdilquad := terminal_star_inverse_quadratic_comparison hStarp hformj hformp
    hdropSmall hdilplain
  have hKhat := shifted_skew_quadratic_le_terminal_primal hstat hq hlj hjp hintj hintp
    hStarj hSp hStarp hformj hformp
    hposj hepsj1 hdropSmall hh0def hstarpinvle hstarcross horderp hskewMj
  -- the gap input
  have hO2 := hatted_sharp_gap_bound hSj hStarj hposj hepsj1 horderj
    hgapMj (Response.responseSymmetric_isHermitian Kj) hskewMj hSp hStarp
    horderp hstarcross hdilquad hKhat
  have hgapJ : toFullBlockMat
      (Response.skewBlockCongr h0 (adaptedMean P q j)) -
      fullBlockSharp (toFullBlockMat
        (Response.skewBlockCongr h0 (adaptedMean P q j))) ≤
      (36 * epsj) • toFullBlockMat
        (Response.skewBlockCongr h0 (adaptedMean P q p)) := by
    rw [hE2j, hE2p]
    exact hO2
  -- nonnegativity of the constants
  have hdropnn : 0 ≤
      adaptedHattedContrast P q j - adaptedHattedContrast P q p :=
    sub_nonneg.mpr (adaptedHattedContrast_le hstat hq hlj hjp hintj
      hintp)
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hcD0 : (0 : ℝ) ≤ 4 * (d : ℝ) *
      (adaptedHattedContrast P q j - adaptedHattedContrast P q p) := by
    positivity
  -- the abstract core at the hatted objects
  have hcore := norm_normalized_parent_fluctuation_le Z hZne A hA hAp hGj
    hGp hparentLe hparentSharp hsharpJle horder
    (by norm_num : (0 : ℝ) ≤ 4)
    (by positivity : (0 : ℝ) ≤ 36 * epsj) hcD0 hsharpPinv hgapJ hdil
  -- return to the plain frame
  have havgfull : (Z.card : ℝ)⁻¹ • ∑ w ∈ Z, A w =
      toFullBlockMat (Response.skewBlockCongr h0
        (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
          ∑ w ∈ Z,
            toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)))) := by
    rw [Response.toFullBlockMat_skewBlockCongr, toFullBlockMat_ofFullBlockMat,
      Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _hw => ?_
    rw [hAfull w, hShdef]
  have hLHSeq := recentered_parent_fluctuation_norm_eq_block_size p a h0 hGpsym hGpblock
  have hAvgeq := recentered_average_fluctuation_norm_eq_block_size hqpd j p a h0 Z
    hGpsym hGpblock havgfull
  rw [← hLHSeq, ← hAvgeq]
  exact hcore

end

end HCPolySupport.HighContrast.Quenched
