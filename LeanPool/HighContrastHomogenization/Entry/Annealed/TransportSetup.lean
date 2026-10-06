/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.BridgeEccentricity
public import LeanPool.HighContrastHomogenization.Entry.Annealed.BridgeSourceTail
public import LeanPool.HighContrastHomogenization.Entry.Annealed.BridgeComparisons
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AveragingTransport
public import LeanPool.HighContrastHomogenization.Entry.Annealed.ParentChildRecurrence
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedCellFoundations
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.SelectionExponentBounds
public import LeanPool.HighContrastHomogenization.Entry.Analysis.PositiveGapMaximal
public import LeanPool.HighContrastHomogenization.Entry.TwoGridWhitney
public import LeanPool.HighContrastHomogenization.Entry.Annealed.ShortBridge
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Jensen
public import LeanPool.HighContrastHomogenization.Entry.MatrixAveraging

/-!
# High-contrast homogenization: Entry.Annealed.TransportSetup

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-! This module assembles the two-grid transport estimates behind `p.two.grid.transport`.
For the rounded grids it derives grid-ratio and eccentricity control from the dimension, the
operator-norm identity `‖bridgeMap A B‖ ^ 2 = blockOpNorm (normalizedBlock A B)` for positive
definite normalizers, the covariance of `normalizedBlock` under scaling, and the pointwise and
Schatten comparisons that exchange one normalizer for another at the cost of the grid proximity.
It then regroups a Whitney partition of an adapted cell into a capped row, a finite boundary
range and the fine cells, and shows that the resulting series orders the normalized coarse block
by the target mean, has finite moments, a positive full-matrix sum, finite rows and an exact row
reindexing; a fixed enlargement of the old coordinates contains the entire new-grid target, with
aligned parents at every higher generation. -/
open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter adaptedMean aspectRatio
  aspectRatio_nonneg blockLogDet blockPosDef_annealedBlock blockScale blockTrace
  blockVecDot_blockMatVecMul_eq_sum coarseBlock gridRatio isSymmetricBlockMat_coarseBlockMatrix
  matSqrt normalizedBlock toFullBlockMat_eq_blockMatEntry)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate aspectRatio_nonneg
  centeredCube standardCell standardCellCenter)
namespace HCPolySupport.HighContrast.Annealed
open MeasureTheory Geometry Multiscale Analysis
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix
noncomputable section

/-- Dimension alone fixes the grid ratio; projective proximity controls eccentricity. -/
theorem exists_transport_grid_constant (d : ℕ) (hd : 2 ≤ d) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar →
      ∀ m mPlus : Mat d, m.PosDef → mPlus.PosDef → projectiveDistance m mPlus ≤ 1 →
        gridRatio (explicitRoundedGrid jStar m) (explicitRoundedGrid jStar mPlus) ≤ K₀ ∧
          Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) ≤ Real.exp 1 * Real.sqrt (‖m‖ * ‖m⁻¹‖) ∧
          1 ≤ Real.sqrt (‖m‖ * ‖m⁻¹‖) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨K₀, hK₀, hbound⟩ := exists_gridRatio_bound d hd
  exact ⟨K₀, hK₀, fun jStar hj m mPlus hm hmPlus hpr =>
    ⟨hbound jStar hj m mPlus hm hmPlus hpr,
      eccentricity_le_of_projectiveDistance_le hm hmPlus hpr, Source.one_le_source_eccentricity hm⟩⟩
/-- The C-star identity for arbitrary positive definite normalizers on either grid. -/
theorem transportMatrix_sq_opNorm_eq_general {d : ℕ} {A B : BlockMat d}
    (hA : (toFullBlockMat A).PosDef) (hB : (toFullBlockMat B).PosDef) :
    ‖bridgeMap A B‖ ^ 2 = blockOpNorm (normalizedBlock A B) := by
  have he := normalizedBlock_transport_congr hA hB A
  rw [normalizedBlock_self_of_posDef A hA, toFullBlockMat_blockIdentity, mul_one] at he; rw
    [blockOpNorm, he]
  have hn := CStarRing.norm_star_mul_self (x := bridgeMap A B)
  simpa only [show (star (bridgeMap A B) : FullBlockMat d) = (bridgeMap A B)ᵀ from rfl,
    pow_two] using hn.symm
theorem transport_normalized_scale {d : ℕ} (c : ℝ) {F : BlockMat d}
    (hF : (toFullBlockMat F).PosDef) :
    normalizedBlock (blockScale c F) F = blockScale c (Book.Ch02.blockIdentity d) := by
  rw [normalizedBlock, toFullBlockMat_blockScale, Matrix.mul_smul, Matrix.smul_mul,
    matSqrt_inv_conj hF]
  rw [← ofFullBlockMat_toFullBlockMat (blockScale c (Book.Ch02.blockIdentity d)),
    toFullBlockMat_blockScale, toFullBlockMat_blockIdentity]
theorem transport_normalized_order {d : ℕ} {A B F : BlockMat d} (hA : (toFullBlockMat
  A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    (hF : (toFullBlockMat F).PosDef) (hAB : BlockMatLoewnerLE A B) :
    BlockMatLoewnerLE (normalizedBlock A F) (normalizedBlock B F) := by
  have hS := matSqrt_inv_posDef_full hF
  have h := Analysis.blockMatLoewnerLE_congr_le ((Analysis.toFullBlockMat_isHermitian_iff _).1
    hA) ((Analysis.toFullBlockMat_isHermitian_iff _).1 hB) hAB (matSqrt (toFullBlockMat F)⁻¹)
  simpa only [normalizedBlock, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    hS.isHermitian.eq] using h
private theorem transport_normalized_upper {d : ℕ} {F G : BlockMat d} (hF : (toFullBlockMat
  F).PosDef) (hG : (toFullBlockMat G).PosDef)
    {c : ℝ} (hc : 0 < c) (hFG : BlockMatLoewnerLE F (blockScale c G)) :
    BlockMatLoewnerLE (normalizedBlock F G) (blockScale c (Book.Ch02.blockIdentity d)) ∧
      blockOpNorm (normalizedBlock F G) ≤ c ∧
      blockLogDet F - blockLogDet G ≤ 2 * (d : ℝ) * Real.log c := by
  have hscale : (toFullBlockMat (blockScale c G)).PosDef := by
    rw [toFullBlockMat_blockScale]; exact hG.smul hc
  have ho := transport_normalized_order hF.isHermitian hscale.isHermitian hG hFG
  rw [transport_normalized_scale c hG] at ho
  have hN := normalizedBlock_posDef F G hF hG
  have hI : (toFullBlockMat (blockScale c (Book.Ch02.blockIdentity d))).IsHermitian := by
    rw [toFullBlockMat_blockScale, toFullBlockMat_blockIdentity]; exact (Matrix.PosDef.one.smul
      hc).isHermitian
  have hupper : toFullBlockMat (normalizedBlock F G) ≤ c • (1 : FullBlockMat d) := by
    simpa only [toFullBlockMat_blockScale, toFullBlockMat_blockIdentity] using (fullBlock_le_iff
      hN.isHermitian hI).2 ho
  have heig (i) : hN.isHermitian.eigenvalues i ≤ c := by
    apply (le_algebraMap_iff_spectrum_le (a := toFullBlockMat (normalizedBlock F G))
      (r := c) (ha := hN.isHermitian)).mp
      (by simpa only [Algebra.algebraMap_eq_smul_one] using hupper)
    rw [hN.isHermitian.spectrum_real_eq_range_eigenvalues]; exact Set.mem_range_self i
  refine ⟨ho, ?_, ?_⟩
  · have hunitary (U : unitary (FullBlockMat d)) (A : FullBlockMat d) :
        ‖(Unitary.conjStarAlgAut ℝ _ U) A‖ = ‖A‖ := by
      rw [Unitary.conjStarAlgAut_apply]
      rw [CStarRing.norm_mul_mem_unitary
        (A := (U : FullBlockMat d) * A) (hU := Unitary.star_mem U.prop)]
      exact CStarRing.norm_mem_unitary_mul A U.prop
    change ‖toFullBlockMat (normalizedBlock F G)‖ ≤ c
    conv_lhs => rw [hN.isHermitian.spectral_theorem]
    rw [hunitary]; simp only [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hc.le).2
    intro i
    simpa only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq,
      Real.norm_of_nonneg (hN.eigenvalues_pos i).le] using heig i
  ·
    have hdet : (toFullBlockMat (normalizedBlock F G)).det ≤ c ^ (2 * d) := by
      rw [hN.isHermitian.det_eq_prod_eigenvalues]; simp only [RCLike.ofReal_real_eq_id, id_eq]
      have hp := Finset.prod_le_prod₀ (fun i (_ : i ∈ Finset.univ) => (hN.eigenvalues_pos i).le)
        (fun i (_ : i ∈ Finset.univ) => heig i)
      simpa only [Finset.prod_const, Finset.card_univ, BlockCoord,
        Fintype.card_sum, Fintype.card_fin, two_mul] using hp
    have hl := Real.log_le_log hN.det_pos hdet
    rw [det_normalizedBlock_eq_exp F G hF hG, Real.log_exp, Real.log_pow] at hl
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hl
private theorem transport_reverse_lower {d : ℕ} {F H : BlockMat d} {δ : ℝ}
    (hδ : δ < 1) (hlow : BlockMatLoewnerLE (blockScale (1 - δ) F) H) :
    BlockMatLoewnerLE F (blockScale (1 - δ)⁻¹ H) := by
  have hh := bridge_blockScale_mono (inv_nonneg.mpr (sub_pos.mpr hδ).le) hlow
  have he : blockScale (1 - δ)⁻¹ (blockScale (1 - δ) F) = F := by
    simp only [blockScale, smul_smul, inv_mul_cancel₀ (sub_pos.mpr hδ).ne', one_smul]
  rwa [he] at hh
/-- `p.two.grid.transport`. The printed product is spectrally equivalent to the *inverse* of
`normalizedBlock H F`; its bounds are reciprocal, `1/(1+δ)` and `1/(1-δ)`. -/
theorem transport_normalizer_comparison {d : ℕ} {F H : BlockMat d} (hF : (toFullBlockMat
  F).PosDef) (hH : (toFullBlockMat H).PosDef)
    {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 4))
    (hlow : BlockMatLoewnerLE (blockScale (1 - δ) F) H)
    (hup : BlockMatLoewnerLE H (blockScale (1 + δ) F)) :
    BlockMatLoewnerLE (blockScale (1 - δ) (Book.Ch02.blockIdentity d)) (normalizedBlock H F) ∧
      BlockMatLoewnerLE (normalizedBlock H F) (blockScale (1 + δ) (Book.Ch02.blockIdentity d)) ∧
      ‖bridgeMap H F‖ ^ 2 ≤ 1 + δ ∧ ‖bridgeMap F H‖ ^ 2 ≤ (1 - δ)⁻¹ := by
  have hδ1 : δ < 1 := lt_of_le_of_lt hδ.2 (by norm_num)
  have hl : (toFullBlockMat (blockScale (1 - δ) F)).PosDef := by
    rw [toFullBlockMat_blockScale]; exact hF.smul (sub_pos.mpr hδ1)
  have ho := transport_normalized_order hl.isHermitian hH.isHermitian hF hlow
  rw [transport_normalized_scale _ hF] at ho
  have hu := transport_normalized_upper hH hF (by linarith only [hδ.1] : 0 < 1 + δ) hup
  have hv := transport_normalized_upper hF hH (inv_pos.mpr (sub_pos.mpr hδ1))
    (transport_reverse_lower hδ1 hlow)
  exact ⟨ho, hu.1, by rw [transportMatrix_sq_opNorm_eq_general hH hF]; exact hu.2.1,
    by rw [transportMatrix_sq_opNorm_eq_general hF hH]; exact hv.2.1⟩
private theorem transport_pointwise {d : ℕ} {A B X : BlockMat d} (hA : (toFullBlockMat
  A).PosDef) (hB : (toFullBlockMat B).PosDef)
    (hX : (toFullBlockMat X).IsHermitian) {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N (normalizedBlock X B) ≤
      ‖bridgeMap A B‖ ^ 2 * absSchattenNorm N (normalizedBlock X A) := by
  have hS := matSqrt_inv_posDef_full hA
  have hXA : (toFullBlockMat (normalizedBlock X A)).IsHermitian := by
    simpa only [normalizedBlock, toFullBlockMat_ofFullBlockMat, hS.isHermitian.eq] using
      Matrix.isHermitian_conjTranspose_mul_mul (matSqrt (toFullBlockMat A)⁻¹) hX
  have hh := Analysis.absSchattenNorm_congr_le (normalizedBlock X A) (bridgeMap A B) hXA hN
  rwa [← normalizedBlock_transport_congr hA hB X, ofFullBlockMat_toFullBlockMat] at hh
/-- The pointwise normalization change needed inside the joint maximum, in both directions. -/
theorem transport_schatten_normalizer_comparison {d : ℕ} {F H X : BlockMat d} (hF :
  (toFullBlockMat F).PosDef) (hH : (toFullBlockMat H).PosDef)
    (hX : (toFullBlockMat X).IsHermitian) {N : ℝ} (hN : 1 ≤ N)
    {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 4))
    (hlow : BlockMatLoewnerLE (blockScale (1 - δ) F) H)
    (hup : BlockMatLoewnerLE H (blockScale (1 + δ) F)) :
    absSchattenNorm N (normalizedBlock X F) ≤ (1 - δ)⁻¹ * absSchattenNorm N (normalizedBlock X H) ∧
      absSchattenNorm N (normalizedBlock X H) ≤ (1 - δ)⁻¹ * absSchattenNorm N (normalizedBlock X
        F) := by
  have hδ1 : δ < 1 := lt_of_le_of_lt hδ.2 (by norm_num)
  have hc : 1 + δ ≤ (1 - δ)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (sub_pos.mpr hδ1)]; nlinarith only [sq_nonneg δ]
  have hnorm := transport_normalizer_comparison hF hH hδ hlow hup
  have hsym (A : BlockMat d) (hA : (toFullBlockMat A).PosDef) :
      (toFullBlockMat (normalizedBlock X A)).IsHermitian := by
    have hS := matSqrt_inv_posDef_full hA
    simpa only [normalizedBlock, toFullBlockMat_ofFullBlockMat, hS.isHermitian.eq] using
      Matrix.isHermitian_conjTranspose_mul_mul (matSqrt (toFullBlockMat A)⁻¹) hX
  exact ⟨(transport_pointwise hH hF hX hN).trans (mul_le_mul_of_nonneg_right
      (hnorm.2.2.1.trans hc) (Analysis.absSchattenNorm_nonneg (hsym H hH) hN)),
    (transport_pointwise hF hH hX hN).trans (mul_le_mul_of_nonneg_right
      hnorm.2.2.2 (Analysis.absSchattenNorm_nonneg (hsym F hF) hN))⟩
/-- `p.two.grid.transport`. Old cells contribute the old eccentricity; normalization
on the new grid contributes the new one. The source envelope retains its full
fixed-Q bound, needed by transport beyond the bridge's first-moment estimate.
The Whitney row constant is `Cw = Cwhitney * K₀` at the consumer. -/
theorem transport_fine_source_tail (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∃ X : CoeffSpace d → ℝ, (∀ a, 0 ≤ X a) ∧
            MemLp X (ENNReal.ofReal (bigQ d γ : ℝ)) P ∧
            eLpNorm X (ENNReal.ofReal (bigQ d γ : ℝ)) P ≤ ENNReal.ofReal 2 ∧
            Integrable X P ∧ (∫ a, X a ∂P ≤ 2) ∧
            ∀ m mPlus : Mat d, m.PosDef → mPlus.PosDef →
            ∀ s : ℤ, (jStar : ℤ) ≤ s →
              adaptedCell (explicitRoundedGrid jStar mPlus) s ⊆ centeredCube d (2 * (jStar : ℤ)) →
            ∀ W : Set (Vec d), W ⊆ centeredCube d (2 * (jStar : ℤ)) →
            ∀ (ι : Type) [Countable ι] (r : ι → ℤ) (y : ι → Vec d) (w : ι → ℝ),
              (∀ i, r i < (jStar : ℤ)) → (∀ i, 0 ≤ w i) → Summable w →
              (∀ i, adaptedCellTranslate (explicitRoundedGrid jStar m) (r i) (y i) ⊆ W) →
              ∀ j : ℤ, (jStar : ℤ) ≤ j → ∀ Cw : ℝ, 0 ≤ Cw →
                (∀ t : ℤ, (∑' i : {i // r i = t}, w i) ≤ Cw * (3 : ℝ) ^ ((t : ℝ) - j)) →
                let M := fun a => ofFullBlockMat (∑' i, w i • toFullBlockMat
                  (coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar m) (r i) (y i)) a))
                SchattenMemLp P (bigQ d γ : ℝ) M ∧
                  (∀ᵐ a ∂P, Summable (fun i => w i • toFullBlockMat (coarseBlock
                    (adaptedCellTranslate (explicitRoundedGrid jStar m) (r i) (y i)) a)) ∧
                    BlockMatLoewnerLE (M a)
                      (blockScale (C * Cw * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖) *
                        Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) * X a *
                        (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - jStar)))
                        (adaptedMean P (explicitRoundedGrid jStar mPlus) s))) ∧
                  BlockMatLoewnerLE
                    (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (M a) α β ∂P))
                    (blockScale (C * Cw * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖) *
                      Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) * 2 *
                      (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - jStar)))
                      (adaptedMean P (explicitRoundedGrid jStar mPlus) s)) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, Ca, hCs, hCa, hsource⟩ := Source.source_multiplier_and_adapted_bound d hd γ hγ
  obtain ⟨CbSrc, Cb, hCbSrc, hCb, hbridge⟩ := bridge_fine_source_tail d hd γ hγ
  obtain ⟨CnSrc, Cn, hCnSrc, hCn, hnormalize⟩ := bridge_normalize_source_tail d hd γ hγ
  let den := 1 - (3 : ℝ) ^ (-(1 - γ))
  have hden : 0 < den := sub_pos.mpr (bridge_fine_ratio_mem_Ico hγ.2).2
  let Ct := Ca / den + Cb
  have hCt : 0 < Ct := add_pos (div_pos hCa hden) hCb
  refine ⟨max Cs (max CbSrc CnSrc), Ct * Cn, hCs.trans_le (le_max_left _ _), mul_pos hCt hCn, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hjStar hsrc
  have hlog : 0 ≤ Real.logb 3 (2 * K) := (Real.logb_pos (by norm_num)
    (by linarith only [hdag.one_lt_growthWitness] : (1 : ℝ) < 2 * K)).le
  have hsrcs := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left Cs (max CbSrc CnSrc))
    hlog)).trans hsrc
  have hsrcb := (Int.ceil_mono (mul_le_mul_of_nonneg_right
    ((le_max_left CbSrc CnSrc).trans (le_max_right Cs _)) hlog)).trans hsrc
  have hsrcn := (Int.ceil_mono (mul_le_mul_of_nonneg_right
    ((le_max_right CbSrc CnSrc).trans (le_max_right Cs _)) hlog)).trans hsrc
  obtain ⟨ell, X, _hell, _hXm, hform, _hgood, hX, _hXi, _hmoment, hnorm, hbound⟩ := hsource P E
    Ψ K S hstat hdag jStar hjStar hsrcs
  obtain ⟨_Xb, _hXb0, _hXb, _hXbi, _hEXb, hfine⟩ := hbridge P E Ψ K S hstat hdag jStar hjStar hsrcb
  have hX0 (a) : 0 ≤ X a := by rw [hform]; positivity
  have hQ : 1 ≤ (bigQ d γ : ℝ) := by exact_mod_cast (bigQ_two_le d γ hγ).trans' (by norm_num)
  have hEX := source_envelope_integral_le_two d hd γ hγ P X hX0 hX hnorm
  refine ⟨X, hX0, hX, hnorm, hX.integrable (ENNReal.one_le_ofReal.mpr hQ), hEX, ?_⟩
  intro m mPlus hm hmPlus s hs hswindow W hW ι hι r y w hr hw0 hw hcell j hj Cw hCw hrow M
  have haux := hfine m hm W hW ι r y w hr hw0 hw hcell j Cw hCw hrow
  have hsum := bridge_fine_weighted_sum w r hw0 hw jStar j hr Cw hCw hrow γ hγ.2
  have hPi := aspectRatio_nonneg E
  have hmean := blockPosDef_annealedBlock
    (by simpa only [adaptedCellTranslate, zero_add, Set.image_id'] using
      hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag jStar hjStar mPlus hmPlus s 0)
    (fun a => by simpa only [adaptedCellTranslate, zero_add, Set.image_id'] using
      blockPosDef_coarseBlock_adapted (explicitRoundedGrid jStar mPlus) (isUnit_roundedGrid
        hjStar hmPlus) s 0 a)
  have hdecay : (3 : ℝ) ^ (-((j : ℝ) - jStar)) ≤
      (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - jStar)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hgap : 0 ≤ (j : ℝ) - jStar := by exact_mod_cast sub_nonneg.mpr hj
    nlinarith only [mul_nonneg hγ.1 hgap]
  have hfactor (b x : ℝ) (hb : 0 ≤ b) (hbc : b ≤ Ct) (hx : 0 ≤ x) :
      (b * Real.sqrt (‖m‖ * ‖m⁻¹‖) * x * Cw * (3 : ℝ) ^ (-((j : ℝ) - jStar))) *
          Cn * aspectRatio E * Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) ≤
        (Ct * Cn) * Cw * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖) *
          Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) * x *
          (3 : ℝ) ^ (-(1 - γ) * ((j : ℝ) - jStar)) := by
    calc
      _ = b * Cn * Cw * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖) *
          Real.sqrt (‖mPlus‖ * ‖mPlus⁻¹‖) * x * (3 : ℝ) ^ (-((j : ℝ) - jStar)) := by ring
      _ ≤ _ := by gcongr
  refine ⟨haux.1, ?_, ?_⟩
  · filter_upwards [hbound, haux.2.1] with a ha hauxa
    have hXa := hX0 a
    have ho (i) := ha.2 m hm (r i) (y i) ((hcell i).trans hW)
    have hsumm : Summable (fun i => w i * (Ca * Real.sqrt (‖m‖ * ‖m⁻¹‖) * X a *
        (3 : ℝ) ^ (γ * ((jStar : ℝ) - r i)))) := by
      simpa only [mul_left_comm] using! hsum.1.mul_left (Ca * Real.sqrt (‖m‖ * ‖m⁻¹‖) * X a)
    have htail := bridge_block_tsum_bound
      (fun i => coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar m) (r i) (y i)) a) E w
      (fun i => Ca * Real.sqrt (‖m‖ * ‖m⁻¹‖) * X a * (3 : ℝ) ^ (γ * ((jStar : ℝ) - r i)))
      hw0 (fun i => isSymmetricBlockMat_coarseBlockMatrix _ (⇑a.1))
      (fun i => blockPosDef_coarseBlock_adapted _ (isUnit_roundedGrid hjStar hm) _ _ a)
      (fun i => by simpa only [max_eq_left (by exact_mod_cast sub_nonneg.mpr (hr i).le :
        0 ≤ (jStar : ℝ) - r i)] using ho i) hsumm
    have hD : BlockMatLoewnerLE (M a) (blockScale
        (Ca / den * Real.sqrt (‖m‖ * ‖m⁻¹‖) * X a * Cw * (3 : ℝ) ^ (-((j : ℝ) - jStar))) E) := by
      apply htail.2.trans (Source.blockScale_le_blockScale_of_pos hdag.refBlock_posDef _)
      simp_rw [mul_left_comm (w _) (Ca * Real.sqrt (‖m‖ * ‖m⁻¹‖) * X a), tsum_mul_left]
      calc
        _ ≤ (Ca * Real.sqrt (‖m‖ * ‖m⁻¹‖) * X a) *
            (Cw / den * (3 : ℝ) ^ (-((j : ℝ) - jStar))) :=
          mul_le_mul_of_nonneg_left hsum.2 (by positivity)
        _ = _ := by ring
    have hn := hnormalize P E Ψ K S hstat hdag jStar hjStar hsrcn mPlus hmPlus s hs hswindow
      (M a) _ (by positivity) hD
    exact ⟨hauxa.1, hn.trans (Source.blockScale_le_blockScale_of_pos hmean
      (hfactor (Ca / den) (X a) (div_pos hCa hden).le (le_add_of_nonneg_right hCb.le) (hX0 a)))⟩
  · have hD : BlockMatLoewnerLE
        (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (M a) α β ∂P))
        (blockScale (Cb * Real.sqrt (‖m‖ * ‖m⁻¹‖) * 2 * Cw *
          (3 : ℝ) ^ (-((j : ℝ) - jStar))) E) := by
      convert haux.2.2 using 1
      congr 1; ring
    have hn := hnormalize P E Ψ K S hstat hdag jStar hjStar hsrcn mPlus hmPlus s hs hswindow
      _ _ (by positivity) hD
    exact hn.trans (Source.blockScale_le_blockScale_of_pos hmean
      (hfactor Cb 2 hCb.le (le_add_of_nonneg_left (div_pos hCa hden).le) (by norm_num)))
/-- The diagonal profile uses O8 to cancel the actual terminal mean, then O5. -/
theorem transport_profile_self (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ)
      (K : ℝ) (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger
      P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (mPlus : Mat d) (hmPlus : mPlus.PosDef) (t : ℤ) :
    profile P γ (explicitRoundedGrid jStar mPlus) jStar t t =
      fluctuationHistory P γ (explicitRoundedGrid jStar mPlus) jStar t +
        meanHistory P γ (explicitRoundedGrid jStar mPlus) (jStar : ℤ) t := by
  exact profile_self_of_posDef P γ (explicitRoundedGrid jStar mPlus) jStar t (adaptedMean_posDef
    d hd P γ E Ψ K S hstat hdag jStar hj mPlus hmPlus t)
/-- The target-count loss leaves the printed positive geometric decay. -/
theorem transport_mean_weight_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (3 : ℝ) ^ (-((bigQ d γ : ℝ) * rhoMax d γ - (d : ℝ)) * t) =
        (3 : ℝ) ^ (-((bigQ d γ : ℝ) * γ + (1 - γ) / 4) * t) ∧
      (3 : ℝ) ^ (-((bigQ d γ : ℝ) * rhoMax d γ - (d : ℝ)) * t) ≤
        (3 : ℝ) ^ (-((1 - γ) / 4) * t) := by
  have hQ := bigQ_real_pos d γ hγ
  have he : (bigQ d γ : ℝ) * rhoMax d γ - (d : ℝ) = (bigQ d γ : ℝ) * γ + (1 - γ) / 4 := by
    calc
      _ = (bigQ d γ : ℝ) * (rhoMax d γ - (d : ℝ) / (bigQ d γ : ℝ)) := by field_simp
      _ = (bigQ d γ : ℝ) * (γ + (1 - γ) / (4 * (bigQ d γ : ℝ))) := by rw [rhoMax_sub_d_div_bigQ
        d hd γ hγ]
      _ = _ := by field_simp
  rw [he]
  refine ⟨rfl, Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith only [mul_nonneg hQ.le hγ.1]) ht
/-- Actual target blocks have finite moments, positive order, and the stationary normalized mean. -/
theorem transport_target_ordered_mean (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ)
      (K : ℝ) (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger
      P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (mPlus : Mat d) (hmPlus : mPlus.PosDef)
    (j t : ℤ) (hj : (jStar : ℤ) ≤ j) (hjt : j ≤ t) (w : Fin d → ℤ) (N : ℝ) (hN : 1 ≤ N) :
    let q := explicitRoundedGrid jStar mPlus
    let F := fun a => normalizedBlock (coarseBlock (adaptedCellAtCenter q j w) a) (adaptedMean P
      q t)
    SchattenMemLp P N F ∧ (∀ a, BlockMatLoewnerLE (ofFullBlockMat 0) (F a)) ∧
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P) = relMean P q j t ∧
      BlockMatLoewnerLE (Book.Ch02.blockIdentity d) (relMean P q j t) := by
  let : NeZero d := ⟨by omega⟩
  intro q F
  have hRaw := Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag
    jStar hjStar mPlus hmPlus j (adaptedCellCenter q j w) N hN
  have hMean := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar mPlus hmPlus t
  refine ⟨Source.memLqSchatten_normalizedBlock hRaw hN _, ?_, ?_,
    (adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag jStar hjStar mPlus hmPlus j t hj
      hjt).1⟩
  · intro a
    have hp := posDef_toFullBlockMat (isSymmetricBlockMat_coarseBlockMatrix _ (⇑a.1))
      (blockPosDef_coarseBlock_adapted q (isUnit_roundedGrid hjStar hmPlus) j (adaptedCellCenter
      q j w) a)
    have hn := normalizedBlock_posDef _ _ hp hMean
    apply (fullBlock_le_iff (by rw [toFullBlockMat_ofFullBlockMat]; exact
      Matrix.isHermitian_zero) hn.isHermitian).1
    simpa only [toFullBlockMat_ofFullBlockMat] using hn.posSemidef.nonneg
  · have he := integral_normalizedBlock_coarseBlock (hRaw.integrable_entry hN) (adaptedMean P q t)
    exact he.trans (congrArg (fun A => normalizedBlock A (adaptedMean P q t))
      (annealedBlock_adaptedCellAtCenter P hstat jStar hjStar mPlus hmPlus j hj w))
private theorem transport_source_weight_majorant {γ J cap r : ℝ} (hγ : 0 ≤ γ) (hr : r ≤ cap) :
    (3 : ℝ) ^ (γ * max (J - r) 0) ≤
      (3 : ℝ) ^ (γ * max (J - cap) 0) * (3 : ℝ) ^ (γ * (cap - r)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ hγ
  apply max_le
  · have hh := le_max_left (J - cap) 0
    linarith only [hh]
  · exact add_nonneg (le_max_right _ _) (sub_nonneg.mpr hr)
/-- A Whitney-type countable sum has genuine finite moments. The auxiliary
bounded-window envelope supplies finiteness only, with no uniform norm claim. -/
theorem transport_whitney_sum_mem (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ)
      (K : ℝ) (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger
      P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef) (W : Set (Vec d)) (hW :
      Bornology.IsBounded W)
    {ι : Type*} [Countable ι] (r : ι → ℤ) (y : ι → Vec d) (w : ι → ℝ)
    (cap j : ℤ) (hr : ∀ i, r i ≤ cap) (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w) (hcell : ∀ i,
      adaptedCellTranslate (explicitRoundedGrid jStar m) (r i) (y i) ⊆ W) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hrow : ∀ t : ℤ, (∑' i : {i // r i = t}, w i) ≤ Cw * (3 : ℝ) ^ ((t : ℝ) - j))
    (N : ℝ) (hN : 1 ≤ N) :
    SchattenMemLp P N (fun a => ofFullBlockMat (∑' i, w i • toFullBlockMat
      (coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar m) (r i) (y i)) a))) ∧
      (∀ᵐ a ∂P, Summable (fun i => w i • toFullBlockMat
        (coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar m) (r i) (y i)) a))) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨J, X, _hXm, hX0, hXN, hbound⟩ := Source.bounded_source_envelope P γ E Ψ K S hstat hdag
    W hW
  let A := fun i a => coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar m) (r i) (y i)) a
  let F := fun i a => w i • toFullBlockMat (A i a)
  let b := fun i => (3 : ℝ) ^ (γ * max ((J : ℝ) - r i) 0)
  let c := 12 * (d : ℝ) ^ ((3 : ℝ) / 2) / (1 - (3 : ℝ) ^ (-(1 - γ)))
  have hc : 0 ≤ c := by
    have hden : 0 < 1 - (3 : ℝ) ^ (-(1 - γ)) := sub_pos.mpr (bridge_fine_ratio_mem_Ico
      hdag.g_mem.2).2
    dsimp only [c]
    positivity
  have hb0 (i) : 0 ≤ b i := by dsimp only [b]; positivity
  have ht := (bridge_fine_weighted_sum w r hw0 hw (cap + 1) j
    (fun i => by have := hr i; omega) Cw hCw hrow γ hdag.g_mem.2).1
  have hwb : Summable (fun i => w i * b i) := by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (hw0 i) (hb0 i))
      (f := fun i => (3 : ℝ) ^ (γ * max ((J : ℝ) - (cap + 1 : ℤ)) 0) *
        (w i * (3 : ℝ) ^ (γ * (((cap + 1 : ℤ) : ℝ) - r i)))) _ (ht.mul_left _)
    intro i
    have hh := mul_le_mul_of_nonneg_left (transport_source_weight_majorant (J := (J : ℝ))
      (cap := ((cap + 1 : ℤ) : ℝ)) (r := (r i : ℝ)) hdag.g_mem.1
      (by exact_mod_cast (show r i ≤ cap + 1 by have := hr i; omega))) (hw0 i)
    simpa only [mul_left_comm] using hh
  have hAs (i) (a) : IsSymmetricBlockMat (A i a) := isSymmetricBlockMat_coarseBlockMatrix _ (⇑a.1)
  have hAp (i) (a) : Book.Ch02.BlockPosDef (A i a) := blockPosDef_coarseBlock_adapted _
    (isUnit_roundedGrid hjStar hm) _ _ a
  have ho : ∀ᵐ a ∂P, ∀ i, BlockMatLoewnerLE (A i a) (blockScale (c * X a * b i) E) := by
    filter_upwards [hbound] with a ha
    exact fun i => ha _ (inverseNormLE_roundedGrid hjStar hm) _ _ (hcell i)
  let D := fun i => (w i * b i) * (c * blockTrace E)
  have hTr : 0 ≤ blockTrace E := (Source.fullBlock_posSemidef_of_pos hdag.refBlock_isSymm
    hdag.refBlock_posDef).trace_nonneg
  have hD0 (i) : 0 ≤ D i := mul_nonneg (mul_nonneg (hw0 i) (hb0 i)) (mul_nonneg hc hTr)
  have hD : Summable D := hwb.mul_right _
  have hFm (i) : HasMeasurableBlock P (fun a => ofFullBlockMat (F i a)) := by
    intro α β
    have hmeas := ((measurable_coarseBlock_entry_adapted (explicitRoundedGrid jStar m)
      (isUnit_roundedGrid hjStar hm) (r i) (y i) α β).mono (coeffSigma_le_global _)
        le_rfl).aestronglyMeasurable (μ := P)
    simpa only [F, A, blockMatEntry_ofFullBlockMat, Matrix.smul_apply, smul_eq_mul,
      toFullBlockMat_eq_blockMatEntry] using hmeas.const_mul (w i)
  have hFs : ∀ᵐ a ∂P, ∀ i, IsSymmetricBlockMat (ofFullBlockMat (F i a)) := by
    apply ae_of_all
    intro a i α β
    simp only [F, blockMatEntry_ofFullBlockMat, Matrix.smul_apply, smul_eq_mul,
      toFullBlockMat_eq_blockMatEntry, hAs i a α β]
  have hFn : ∀ᵐ a ∂P, ∀ i, ‖F i a‖ ≤ D i * X a := by
    filter_upwards [ho] with a ha
    intro i
    dsimp only [F]; rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 i)]
    calc
      _ ≤ w i * (c * X a * b i * blockTrace E) := mul_le_mul_of_nonneg_left
        (Source.blockOpNorm_le_scale_trace (hAs i a) (hAp i a) (ha i)) (hw0 i)
      _ = _ := by dsimp only [D]; ring
  refine ⟨(Source.lqSchatten_tsum_convergence P N hN F hFm hFs D hD0 hD X hX0 (hXN N hN) hFn).1, ?_⟩
  filter_upwards [ho] with a ha
  have hs : Summable (fun i => w i * (c * X a * b i)) := by
    simpa only [mul_left_comm] using hwb.mul_left (c * X a)
  exact (bridge_block_tsum_bound (fun i => A i a) E w (fun i => c * X a * b i)
    hw0 (fun i => hAs i a) (fun i => hAp i a) ha hs).1
/-- Response defects on open cells give the normalized countable partition order.
The convergent series is supplied by `transport_whitney_sum_mem`. -/
theorem transport_partition_order {d : ℕ} [NeZero d] {ι : Type*} {I : Set ι} (hI : I.Countable)
  (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d)
    (qi : ι → Mat d) (hqi : ∀ i ∈ I, IsUnit (qi i)) (r : ι → ℤ) (z : ι → Vec d)
    (a : CoeffSpace d) (R : BlockMat d) (hR : (toFullBlockMat R).PosDef) :
    let W := adaptedCellTranslate q j y
    let U := fun i => adaptedCellTranslate (qi i) (r i) (z i)
    (∀ i ∈ I, U i ⊆ W) → I.PairwiseDisjoint U → volume (W \ ⋃ i ∈ I, U i) = 0 →
    Summable (fun i : I => ((volume (U i)).toReal / (volume W).toReal) • toFullBlockMat
      (coarseBlock (U i) a)) →
    BlockMatLoewnerLE (normalizedBlock (coarseBlock W a) R)
      (normalizedBlock (ofFullBlockMat (∑' i : I,
        ((volume (U i)).toReal / (volume W).toReal) • toFullBlockMat (coarseBlock (U i) a))) R)
          := by
  intro W U hsub hdis hnull hseries
  have hWfin : volume W ≠ ⊤ := Transport.volume_adaptedCellTranslate_ne_top q j y
  let : IsFiniteMeasure (volumeMeasureOn W) := ⟨by simpa [volumeMeasureOn] using hWfin.lt_top⟩
  have hWvol : (volume W).toReal ≠ 0 := by
    dsimp only [W]; rw [volume_adaptedCellTranslate_toReal]
    have hdet : q.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det q).mp hq).ne_zero
    positivity
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ := exists_elliptic_representative_adapted q hq j y a
  have ho : BlockMatLoewnerLE (coarseBlock W a) (ofFullBlockMat (∑' i : I,
      ((volume (U i)).toReal / (volume W).toReal) • toFullBlockMat (coarseBlock (U i) a))) := by
    apply Source.block_tsum_of_response_partition hI (isOpen_adaptedCellTranslate hq j y) hWvol
      (fun i hi => isOpen_adaptedCellTranslate (hqi i hi) (r i) (z i)) hsub hdis hnull hEll
      (coarseBlock W a) (fun i => coarseBlock (U i) a) _ _ hseries
    · intro p t
      rw [← responseJ_congr_of_ae_eq (ae_restrict_of_ae hae)]; exact
        responseJ_eq_coarseBlock_adapted q hq j y a p t
    · intro i hi p t
      rw [← responseJ_congr_of_ae_eq (ae_restrict_of_ae hae)]; exact
        responseJ_eq_coarseBlock_adapted (qi i) (hqi i hi) (r i) (z i) a p t
  have hsym := Source.isSymmetricBlockMat_tsum _ hseries (fun i α β => by
    simp only [blockMatEntry_ofFullBlockMat, Matrix.smul_apply, smul_eq_mul,
      toFullBlockMat_eq_blockMatEntry]
    congr 1
    exact isSymmetricBlockMat_coarseBlockMatrix (U i) (⇑a.1) α β)
  have hS := matSqrt_inv_posDef_full hR
  have hc := blockMatLoewnerLE_congr_le (isSymmetricBlockMat_coarseBlockMatrix W (⇑a.1)) hsym ho
    (matSqrt (toFullBlockMat R)⁻¹)
  simpa only [normalizedBlock, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    hS.isHermitian.eq] using! hc
private theorem transport_all_rows {ι : Type*} (w : ι → ℝ) (r : ι → ℤ) (cap j : ℤ) (hw0 : ∀ i, 0
  ≤ w i) (hw : Summable w) (hr : ∀ i, r i ≤ cap) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ t < cap, (∑' i : {i // r i = t}, w i) ≤ C * (3 : ℝ) ^ ((t : ℝ) - j)) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ t : ℤ, (∑' i : {i // r i = t}, w i) ≤ Cw * (3 : ℝ) ^ ((t : ℝ) - j) := by
  let T := ∑' i, w i
  have hT : 0 ≤ T := tsum_nonneg hw0
  refine ⟨C + T * (3 : ℝ) ^ ((j : ℝ) - cap), by positivity, ?_⟩
  intro t
  by_cases ht : t < cap
  · exact (hrow t ht).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
    (by positivity))
  by_cases he : t = cap
  · subst t
    have hp : (3 : ℝ) ^ ((j : ℝ) - cap) * (3 : ℝ) ^ ((cap : ℝ) - j) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), sub_add_sub_cancel, sub_self, Real.rpow_zero]
    calc
      _ ≤ T := Summable.tsum_subtype_le w (fun i => r i = cap) hw0 hw
      _ = (T * (3 : ℝ) ^ ((j : ℝ) - cap)) * (3 : ℝ) ^ ((cap : ℝ) - j) := by rw [mul_assoc, hp,
        mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (by positivity)
  · have hzero : (∑' i : {i // r i = t}, w i) = 0 := (tsum_congr fun i => False.elim (by
      have hri := hr i
      rw [i.2] at hri
      omega)).trans tsum_zero
    rw [hzero]
    positivity
/-- Instantiate Whitney conclusion (i) on the actual target. The finite row,
partition and boundary mass clauses discharge all countable-sum guards.
The geometric constant is selected from K₀ before the law. -/
theorem exists_transport_whitney_ordered_data (d : ℕ) (hd : 2 ≤ d)
    (K₀ : ℝ) (hK₀ : 1 ≤ K₀) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar → ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
        ∀ m mPlus : Mat d, m.PosDef → mPlus.PosDef →
          gridRatio (explicitRoundedGrid jStar m) (explicitRoundedGrid jStar mPlus) ≤ K₀ →
        ∀ j t : ℤ, (jStar : ℤ) ≤ j → j ≤ t → ∀ ell : ℕ, 1 ≤ ell →
        ∀ y ∈ adaptedLatticeAtScale (explicitRoundedGrid jStar mPlus) j, ∀ N : ℝ, 1 ≤ N →
          let q := explicitRoundedGrid jStar m
          let qPlus := explicitRoundedGrid jStar mPlus
          let W := adaptedCellTranslate qPlus j y
          let I := {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn W q (j - (ell : ℤ)) p.1 p.2}
          let F := fun a => normalizedBlock (coarseBlock W a) (adaptedMean P qPlus t)
          let G := fun a => normalizedBlock (ofFullBlockMat (∑' p : I,
            ((volume (adaptedCellAtCenter q p.1.1 p.1.2)).toReal / (volume W).toReal) •
              toFullBlockMat (coarseBlock (adaptedCellAtCenter q p.1.1 p.1.2) a))) (adaptedMean
                P qPlus t)
          SchattenMemLp P N F ∧ SchattenMemLp P N G ∧
            (∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (F a) ∧ BlockMatLoewnerLE (F a) (G a)) ∧
            ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P) = relMean P
              qPlus j t ∧
            BlockMatLoewnerLE (Book.Ch02.blockIdentity d) (relMean P qPlus j t) ∧
            (∀ᵐ a ∂P, Summable (fun p : I =>
              ((volume (adaptedCellAtCenter q p.1.1 p.1.2)).toReal / (volume W).toReal) •
                toFullBlockMat (coarseBlock (adaptedCellAtCenter q p.1.1 p.1.2) a))) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, hCs, hWhitney⟩ := Entry.two_grid_whitney d hd
  obtain ⟨C, hC, hpart⟩ := hWhitney K₀ hK₀
  apply Exists.intro (Cs γ)
  apply And.intro
  · exact hCs γ hγ
  intro P hP E Ψ K S hstat hdag jStar hjStar hsrc m mPlus hm hmPlus hratio j t hj hjt ell hell y
    hy N hN
  rcases hy with ⟨v, rfl⟩
  intro q qPlus W I F G
  have hq := isUnit_roundedGrid hjStar hm
  have hqPlus := isUnit_roundedGrid hjStar hmPlus
  obtain ⟨hfin, hsub, hdis, hnull, _hvol, _hcap, _hcount, _hmass, hrow⟩ := (hpart γ hγ K
    hdag.one_lt_growthWitness jStar hjStar hsrc m mPlus hm hmPlus hratio j ell hell).1
      (adaptedCellCenter qPlus j v) ⟨v, rfl⟩
  let r := fun p : I => p.1.1
  let z := fun p : I => adaptedCellCenter q p.1.1 p.1.2
  let w := fun p : I => (volume (adaptedCellAtCenter q p.1.1 p.1.2)).toReal / (volume W).toReal
  have hsubI (p : ℤ × (Fin d → ℤ)) (hp : p ∈ I) : adaptedCellAtCenter q p.1 p.2 ⊆ W := hsub p.1
    p.2 hp
  have hw0 (p) : 0 ≤ w p := by dsimp only [w]; positivity
  have hWfin : volume W ≠ ⊤ := Transport.volume_adaptedCellTranslate_ne_top qPlus j
    (adaptedCellCenter qPlus j v)
  let : IsFiniteMeasure (volumeMeasureOn W) := ⟨by simpa [volumeMeasureOn] using hWfin.lt_top⟩
  have hw : Summable w := summable_volumeRatio (U := fun p : ℤ × (Fin d → ℤ) =>
    adaptedCellAtCenter q p.1 p.2) (W := W) (s := I)
    (fun p _ => (isOpen_adaptedCellTranslate hq p.1 (adaptedCellCenter q p.1
      p.2)).measurableSet) hsubI hdis
  have hr (p : I) : r p ≤ j - (ell : ℤ) := p.2.1.1
  have hrowI (s : ℤ) (hs : s < j - (ell : ℤ)) :
      (∑' p : {p : I // r p = s}, w p) ≤ C * (3 : ℝ) ^ ((s : ℝ) - j) := by
    exact (bridge_maximal_row_mass W q hq (j - (ell : ℤ)) s (hfin s hs.le) (volume
      W).toReal).2.le.trans (hrow s hs)
  obtain ⟨Cw, hCw, hrowAll⟩ := transport_all_rows w r (j - (ell : ℤ)) j hw0 hw hr C hC.le hrowI
  have hW : Bornology.IsBounded W := by
    dsimp only [W]; rw [adaptedCellTranslate_eq_cg_affine]; exact
      (isOpenBoundedConvexDomain_affine_openCube qPlus hqPlus j _).isBoundedDomain.isBounded
  have hraw := transport_whitney_sum_mem d hd P γ E Ψ K S hstat hdag jStar hjStar m hm W hW
    r z w (j - (ell : ℤ)) j hr hw0 hw (fun p => hsubI p p.2) Cw hCw hrowAll N hN
  have hG := Source.memLqSchatten_normalizedBlock hraw.1 hN (adaptedMean P qPlus t)
  have hR := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar mPlus hmPlus t
  have hFG : ∀ᵐ a ∂P, BlockMatLoewnerLE (F a) (G a) := by
    filter_upwards [hraw.2] with a ha
    exact transport_partition_order (Set.to_countable I) qPlus hqPlus j (adaptedCellCenter qPlus
      j v)
      (fun _ => q) (fun _ _ => hq) Prod.fst (fun p => adaptedCellCenter q p.1 p.2)
      a (adaptedMean P qPlus t) hR hsubI hdis hnull ha
  have hF := transport_target_ordered_mean d hd P γ E Ψ K S hstat hdag jStar hjStar mPlus hmPlus
    j t hj hjt v N hN
  exact ⟨hF.1, hG, hFG.mono fun a ha => ⟨hF.2.1 a, ha⟩, hF.2.2.1, hF.2.2.2, hraw.2⟩
/-- Regroup a convergent Whitney series into the cap row, the finite boundary
range, and all fine cells. This also supplies the exact empty-boundary case. -/
theorem transport_series_three_parts {d : ℕ} {ι : Type*} (F : ι → FullBlockMat d)
    (hF : Summable F) (r : ι → ℤ) (J cap : ℤ) (hJ : J ≤ cap) (hr : ∀ i, r i ≤ cap) :
    (∑' i, F i) = (∑' i : {i // r i = cap}, F i) +
      (∑ t ∈ Finset.Icc J (cap - 1), ∑' i : {i // r i = t}, F i) +
      (∑' i : {i // r i < J}, F i) := by
  classical
  let lo : Set ι := {i | r i < J}
  let hi : Set ι := loᶜ
  let row := fun t : ℤ => ∑' i : {i : hi // r i = t}, F i.1
  have hgroup := (hF.subtype hi).hasSum.tsum_fiberwise (fun i : hi => r i)
  have hgroupEq : (∑' t, row t) = ∑' i : hi, F i := hgroup.tsum_eq
  have hzero (t : ℤ) (ht : t ∉ Finset.Icc J cap) : row t = 0 := by
    apply (tsum_congr fun i => ?_).trans tsum_zero
    exfalso
    have hil : J ≤ r i.1 := not_lt.mp i.1.2
    have hir := hr i.1
    rw [i.2] at hil hir; exact ht (Finset.mem_Icc.mpr ⟨hil, hir⟩)
  have heq (t : ℤ) (ht : t ∈ Finset.Icc J cap) : row t = ∑' i : {i // r i = t}, F i := by
    let e : {i : hi // r i = t} ≃ {i : ι // r i = t} :=
      { toFun := fun i => ⟨i.1.1, i.2⟩
        invFun := fun i => ⟨⟨i.1, by
          change ¬r i.1 < J
          rw [i.2]; exact not_lt.mpr (Finset.mem_Icc.mp ht).1⟩, i.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.tsum_eq (fun i : {i : ι // r i = t} => F i)
  have hall : (∑' i, F i) = (∑ t ∈ Finset.Icc J cap, ∑' i : {i // r i = t}, F i) +
      (∑' i : {i // r i < J}, F i) := by
    calc
      _ = (∑' i : hi, F i) + (∑' i : lo, F i) := by
        rw [add_comm]; exact (hF.tsum_subtype_add_tsum_subtype_compl lo).symm
      _ = _ := by
        congr 1; rw [← hgroupEq, tsum_eq_sum hzero]; exact Finset.sum_congr rfl heq
  have hcap : cap ∈ Finset.Icc J cap := Finset.mem_Icc.mpr ⟨hJ, le_rfl⟩
  have herase : (Finset.Icc J cap).erase cap = Finset.Icc J (cap - 1) := by
    ext t; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  rw [hall, ← Finset.sum_erase_add _ _ hcap, herase]
  abel
/-- Positivity survives the actual infinite full-matrix sum. -/
theorem transport_positive_matrix_series {d : ℕ} {ι : Type*} (F : ι → FullBlockMat d)
    (hsum : Summable F) (hF : ∀ i, (F i).PosSemidef) : (∑' i, F i).PosSemidef := by
  have hs := Source.isSymmetricBlockMat_tsum F hsum (fun i =>
    (toFullBlockMat_isHermitian_iff _).mp (by simpa only [toFullBlockMat_ofFullBlockMat] using
      (hF i).isHermitian))
  have hsym : (∑' i, F i).IsHermitian := by
    simpa only [toFullBlockMat_ofFullBlockMat] using (toFullBlockMat_isHermitian_iff _).mpr hs
  have hz (v : BlockVec d) : blockVecDot v (blockMatVecMul (ofFullBlockMat (0 : FullBlockMat d))
    v) = 0 := by
    simp only [blockVecDot_blockMatVecMul_eq_sum, blockMatEntry_ofFullBlockMat,
      Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero]
  apply Matrix.nonneg_iff_posSemidef.mp
  have hiff := (fullBlock_le_iff (A := ofFullBlockMat 0) (B := ofFullBlockMat (∑' i, F i))
    (by simpa only [toFullBlockMat_ofFullBlockMat] using (Matrix.isHermitian_zero : (0 :
      FullBlockMat d).IsHermitian))
    (by simpa only [toFullBlockMat_ofFullBlockMat] using hsym))
  simp only [toFullBlockMat_ofFullBlockMat] at hiff
  apply hiff.2
  intro v; rw [hz]
  have hi (i) : 0 ≤ blockVecDot v (blockMatVecMul (ofFullBlockMat (F i)) v) := by
    have hiffi := (fullBlock_le_iff (A := ofFullBlockMat 0) (B := ofFullBlockMat (F i))
      (by simpa only [toFullBlockMat_ofFullBlockMat] using (Matrix.isHermitian_zero : (0 :
        FullBlockMat d).IsHermitian))
      (by simpa only [toFullBlockMat_ofFullBlockMat] using (hF i).isHermitian))
    simp only [toFullBlockMat_ofFullBlockMat] at hiffi
    have ho := hiffi.1 (hF i).nonneg
    have hh := ho v
    rw [hz] at hh; linarith only [hh]
  have hh : 0 ≤ ∑' i, (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (F i)) v) :=
    tsum_nonneg (fun i => mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (hi i))
  rw [← Source.quadratic_tsum_fullBlock F hsum v] at hh; linarith only [hh]
/-- Reindex one actual pair-indexed Whitney row by its finite center set.
No averaging or cardinality estimate is used in this identity. -/
theorem transport_maximal_row_reindex {d : ℕ} (W : Set (Vec d)) (q : Mat d) (hq : IsUnit q)
    (cap t : ℤ) (hfin : (maximalAdaptedCellCenters W q cap t).Finite) (F : Vec d → FullBlockMat d) :
    let I := {p : ℤ × (Fin d → ℤ) // IsMaximalAdaptedCellIn W q cap p.1 p.2}
    (∑' i : {i : I // i.1.1 = t}, F (adaptedCellCenter q i.1.1.1 i.1.1.2)) = ∑ z ∈
      hfin.toFinset, F z := by
  intro I
  classical
  let Z := maximalAdaptedCellCenters W q cap t
  let f : {i : I // i.1.1 = t} → Z := fun i => ⟨adaptedCellCenter q t i.1.1.2, by
    refine ⟨i.1.1.2, ?_, rfl⟩
    have hp := i.1.2
    rwa [i.2] at hp⟩
  have hinj : Function.Injective f := by
    intro i k hik
    have hw : i.1.1.2 = k.1.1.2 := (adaptedCellCenter_injective q t hq) (congrArg Subtype.val hik)
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (i.2.trans k.2.symm) hw
  have hsurj : Function.Surjective f := by
    intro z
    rcases z.2 with ⟨w, hw, he⟩
    refine ⟨⟨⟨(t, w), hw⟩, rfl⟩, ?_⟩
    exact Subtype.ext he
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  let : Fintype Z := hfin.fintype
  calc
    _ = ∑' i : {i : I // i.1.1 = t}, F (e i) := tsum_congr fun i => by
      change F (adaptedCellCenter q i.1.1.1 i.1.1.2) = F (adaptedCellCenter q t i.1.1.2)
      rw [i.2]
    _ = ∑' z : Z, F z := e.tsum_eq (fun z : Z => F z)
    _ = ∑ z : Z, F z := tsum_fintype _
    _ = _ := (Finset.sum_subtype hfin.toFinset (fun _ => hfin.mem_toFinset) F).symm
/-- Normalize a positive source tail by the actual positive terminal mean. -/
theorem transport_normalized_psd_bound {d : ℕ} {M R : BlockMat d} (hM : (toFullBlockMat
  M).PosSemidef) (hR : (toFullBlockMat R).PosDef)
    {c : ℝ} (hc : 0 ≤ c) (hbound : BlockMatLoewnerLE M (blockScale c R)) :
    (toFullBlockMat (normalizedBlock M R)).PosSemidef ∧
      BlockMatLoewnerLE (normalizedBlock M R) (blockScale c (Book.Ch02.blockIdentity d)) := by
  have hS := matSqrt_inv_posDef_full hR
  have hn : (toFullBlockMat (normalizedBlock M R)).PosSemidef := by
    simpa only [normalizedBlock, toFullBlockMat_ofFullBlockMat, hS.isHermitian.eq] using
      hM.conjTranspose_mul_mul_same (matSqrt (toFullBlockMat R)⁻¹)
  have hsc : (toFullBlockMat (blockScale c R)).IsHermitian := by
    rw [toFullBlockMat_blockScale]; exact (hR.posSemidef.smul hc).isHermitian
  refine ⟨hn, ?_⟩
  have hb := transport_normalized_order hM.isHermitian hsc hR hbound
  rwa [transport_normalized_scale c hR] at hb
/-- A fixed enlargement in old coordinates contains the whole new-grid target.
Its size is chosen before either grid; no enlarged source window is assumed. -/
theorem exists_transport_parent_enlargement (d : ℕ) (hd : 2 ≤ d) (K₀ : ℝ) (hK₀ : 1 ≤ K₀) :
    ∃ h : ℕ, ∀ (q qPlus : Mat d), IsUnit q → gridRatio q qPlus ≤ K₀ →
      ∀ t : ℤ, adaptedCell qPlus t ⊆ adaptedCell q (t + h) := by
  obtain ⟨h, hh⟩ := exists_nat_gt ((d : ℝ) * K₀)
  have hhpow : (d : ℝ) * K₀ < (3 : ℝ) ^ h := hh.trans_le (by
    exact_mod_cast (show h < 2 ^ h from Nat.lt_two_pow_self).le.trans (pow_le_pow_left' (by
      decide : (2 : ℕ) ≤ 3) h))
  refine ⟨h, ?_⟩
  intro q qPlus hq hratio t x hx
  obtain ⟨v, hv, rfl⟩ := hx
  let A := q⁻¹ * qPlus
  have hA := norm_inv_mul_le_gridRatio_of_le hd hratio
  have hK0 : 0 ≤ K₀ := zero_le_one.trans hK₀
  have hrad : 0 < (3 : ℝ) ^ t / 2 := by positivity
  have hcoord (i : Fin d) : |(A *ᵥ v) i| ≤ (d : ℝ) * K₀ * ((3 : ℝ) ^ t / 2) := by
    calc
      _ ≤ ∑ j, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, K₀ * ((3 : ℝ) ^ t / 2) := by
        apply Finset.sum_le_sum
        intro j _; rw [abs_mul]; exact mul_le_mul ((abs_entry_le_opNorm A i j).trans hA)
          (abs_le.mpr ⟨by linarith only [(Recurrence.mem_centeredCube_iff.mp hv j).1],
            by linarith only [(Recurrence.mem_centeredCube_iff.mp hv j).2]⟩) (abs_nonneg _) hK0
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring
  have hvold : A *ᵥ v ∈ centeredCube d (t + (h : ℤ)) := by
    rw [Recurrence.mem_centeredCube_iff]
    intro i
    have hp := (hcoord i).trans_lt (mul_lt_mul_of_pos_right hhpow hrad)
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    have he : (3 : ℝ) ^ h * ((3 : ℝ) ^ t / 2) = (3 : ℝ) ^ t * (3 : ℝ) ^ h / 2 := by ring
    rw [he] at hp
    constructor <;> linarith only [(abs_lt.mp hp).1, (abs_lt.mp hp).2]
  refine ⟨A *ᵥ v, hvold, ?_⟩
  have hdet := (Matrix.isUnit_iff_isUnit_det q).mp hq
  simp only [A, matVecMul_eq_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv q hdet, Matrix.one_mul]
/-- Iterated aligned parents exist at every higher integer generation. -/
theorem transport_exists_standard_parent {d : ℕ} (r : ℤ) (h : ℕ) (w : Fin d → ℤ) :
    ∃ v : Fin d → ℤ, standardCell d r w ⊆ standardCell d (r + h) v := by
  induction h with
  | zero => exact ⟨w, by simpa only [Nat.cast_zero, add_zero] using Set.Subset.rfl⟩
  | succ h ih =>
    obtain ⟨v, hv⟩ := ih
    refine ⟨Transport.gridParent v, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc] using
      hv.trans (Transport.standardCell_subset_parent (r + h) v)
/-- Every old cell below k inside the target lies in one of the fixed, finite
scale-k parents of the enlarged old target. The index family has its exact count. -/
theorem transport_old_parent_family {d : ℕ} (q qPlus : Mat d) (hq : IsUnit q) (k t : ℤ) (hkt : k
  ≤ t) (h : ℕ)
    (hcover : adaptedCell qPlus t ⊆ adaptedCell q (t + h)) :
    let Z := {v : Fin d → ℤ | standardCellCenter k v ∈ centeredCube d (t + h)}
    Z.Finite ∧ Z.ncard = 3 ^ (d * ((t - k).toNat + h)) ∧
      ∀ (r : ℤ), r ≤ k → ∀ (w : Fin d → ℤ),
        adaptedCellCenter q r w ∈ adaptedCell qPlus t →
        ∃ v ∈ Z, adaptedCellAtCenter q r w ⊆ adaptedCellAtCenter q k v := by
  intro Z
  have hgap : k + (((t - k).toNat + h : ℕ) : ℤ) = t + h := by omega
  have hz := alignedCenterSet_finite_card d k ((t - k).toNat + h)
  rw [hgap] at hz
  refine ⟨hz.1, hz.2, ?_⟩
  intro r hr w hw
  obtain ⟨v, hv⟩ := transport_exists_standard_parent r (k - r).toNat w
  have hgaprk : r + ((k - r).toNat : ℤ) = k := by omega
  rw [hgaprk] at hv
  have hcenter : standardCellCenter r w ∈ centeredCube d (t + h) := by
    obtain ⟨x, hx, he⟩ := hcover hw
    have hc : matVecMul q (standardCellCenter r w) = adaptedCellCenter q r w := by
      change q *ᵥ ((3 : ℝ) ^ r • (fun i => (w i : ℝ))) =
        (3 : ℝ) ^ r • q *ᵥ (fun i => (w i : ℝ))
      exact Matrix.mulVec_smul _ _ _
    have heq := matVecMul_injective_of_isUnit q hq (he.trans hc.symm)
    exact heq ▸ hx
  have hpar : standardCell d k v ⊆ centeredCube d (t + h) := by
    rw [centeredCube_eq_standardCell] at hcenter ⊢; exact standardCell_subset_of_mem (by omega)
      (hv (Recurrence.standardCellCenter_mem_standardCell r w)) hcenter
  refine ⟨v, hpar (Recurrence.standardCellCenter_mem_standardCell k v), ?_⟩
  rw [adaptedCellAtCenter_eq_affine_standardCell, adaptedCellAtCenter_eq_affine_standardCell];
    exact Set.image_mono hv

end
end HCPolySupport.HighContrast.Annealed
