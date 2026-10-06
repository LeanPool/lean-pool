/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.AbstractCellPairingBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.StationaryAnnealedErrorScalars
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# High-contrast homogenization: Entry.Response.Rows.AnnealedBlockMeanCancellation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Mean Cancellation and Full Stationarity of the Annealed Block

Above the stationarity threshold `j_*`, the cell mean of a subcell's own doubled optimizer state
has the form `x + R 𝐀(V) x` with a common annealed block `𝐀`, so the weighted flat average,
over the coarse subcells of the terminal cell, of the annealed cell means of each subcell's own
optimizer state vanishes once the flat weights are normalized. Because the crossed pairing is
bilinear and both the finite flat average and the expectation are linear, pairing that flat
average against the dual variable `Y` is the expectation of the weighted flat average of the
pathwise crossed pairings. For a stationary law and a scale above `j_*`, this file also shows the
whole annealed coarse block of a recentred family — diagonal and off-diagonal alike — is the
same `2d`-by-`2d` matrix at every aligned cell of the generation, since every such cell is an
integer translate of the centred one and the recentring commutes with translation.  Both the
cancellation of the weighted flat average of the annealed cell means and the cell-independence of
the annealed coarse block are used in the cell half of the cutoff-mean row of
`p.response.transfer`.
-/

section
/-!
## The constant cell means cancel after expectation

In the cell half of the cutoff-mean row of `p.response.transfer`, the weighted flat average, over
the coarse subcells of the terminal cell, of the ANNEALED cell means of each subcell's own
optimizer state vanishes.  Above the scale `j_*` the subcells are integer translates of one
another and the law is stationary, so the annealed block of every subcell agrees; the pathwise cell
mean of the optimizer state is `x + R 𝐀 x` (`AK.HC (2.32)`), and its expectation is
`x + R 𝐀_bar x` with the common annealed block `𝐀_bar`.  The weights — the subcell means of the
  cutoff
fluctuation `φ - 1` — have normalized sum zero because the cutoff has mean one on the terminal cell.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock coarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Mean-zero weighting of a common expectation.**  If the weights `c` have normalized sum zero
and every cell functional `G w` has the same law-integral `m`, then the normalized weighted sum of
the integrals vanishes.  This packages the elementary finite-sum manipulation together with
`integral_avsum_mul_eq_zero`; it is the expectation form of the cancellation in
`p.response.transfer`. -/
private theorem normalized_integral_weighted_eq_zero {d : ℕ}
    (P : Measure (CoeffSpace d)) (n : ℕ) (c : (Fin d → ℤ) → ℝ)
    (G : (Fin d → ℤ) → CoeffSpace d → ℝ) (m : ℝ)
    (hc : (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w = 0)
    (hG : ∀ w ∈ triadicIndexBox d n, (∫ a, G w a ∂P) = m)
    (hint : ∀ w ∈ triadicIndexBox d n, Integrable (G w) P) :
    (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * (∫ a, G w a ∂P) = 0 := by
  have hlin : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * G w a ∂P)
      = (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * (∫ a, G w a ∂P) := by
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum _ (fun w hw => (hint w hw).const_mul (c w))]
    exact Finset.sum_congr rfl fun w _ => by rw [integral_const_mul]
  rw [← hlin]
  exact integral_avsum_mul_eq_zero P n c G m hc hG hint

/-- **The weighted cell means of the subcell optimizers cancel, negative sign.**  In the cell half
of the cutoff-mean row of `p.response.transfer`, let the cell mean of the doubled optimizer state of
each coarse subcell `U_w` of the terminal cell `U_t` be the block response of the recentred
coefficient `a_- = a - g` at the load `x^- = (-p, q^-)`, with a common annealed block `A` above
`j_*`.  Then the normalized sum, over the subcells, of the subcell mean of `φ - 1` times the
expectation of each coordinate of that optimizer mean is zero.  The expectation of `x^- + R 𝐀 x^-`
is `x^- + R A x^-` at every subcell by `integral_blockResponseMean`, because the subcell's annealed
block is `A`; the weights have normalized sum zero by `avsum_volumeAverage_sub_one_eq_zero`, the
cutoff having mean one. -/
theorem avsum_weighted_integral_cellAverage_subcellOptimizer_eq_zero {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (hq : IsUnit (respGrid jStar F)) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (ht : t = s + (H : ℤ))
    (Mv : (Fin d → ℤ) → CoeffSpace d → BlockVec d)
    (A : BlockMat d)
    (hMv : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      Mv w a = blockResponseMean (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F a)) (-respP (respMean P jStar F t) e, respqMinus P jStar F t e))
    (hann : ∀ w ∈ triadicIndexBox d H,
      annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F) = A)
    (hint : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d,
      Integrable (fun a => (Mv w a).1 i) P ∧ Integrable (fun a => (Mv w a).2 i) P)
    (hblkint : ∀ w ∈ triadicIndexBox d H,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hquad : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      HasQuadraticMu (adaptedCellAtCenter (respGrid jStar F) s w) (⇑a.1 : CoeffField d)) :
    (∀ i : Fin d, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)
          * ∫ a, (Mv w a).1 i ∂P = 0)
      ∧ (∀ i : Fin d, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)
          * ∫ a, (Mv w a).2 i ∂P = 0) := by
  have hts : t - (H : ℤ) = s := by omega
  have hφint : IntegrableOn φ (HighContrast.adaptedCell (respGrid jStar F) t) :=
    ((hφ.contDiff.continuous).integrable_of_hasCompactSupport hφ.hasCompactSupport).integrableOn
  have hVfin : volume (HighContrast.adaptedCell (respGrid jStar F) t) ≠ ⊤ := by
    rw [← adaptedCellTranslate_zero (respGrid jStar F) t]
    exact Transport.volume_adaptedCellTranslate_ne_top (respGrid jStar F) t 0
  have hintφ : IntegrableOn (fun x => φ x - 1) (HighContrast.adaptedCell (respGrid jStar F) t) :=
    hφint.sub (integrableOn_const hVfin)
  have hvol : (volume (HighContrast.adaptedCell (respGrid jStar F) t)).toReal ≠ 0 := by
    rw [Geometry.volume_adaptedCell_toReal]
    exact mul_ne_zero
      (abs_ne_zero.mpr (IsUnit.ne_zero
        ((Matrix.isUnit_iff_isUnit_det (respGrid jStar F)).mp hq)))
      (pow_ne_zero _ (ne_of_gt (zpow_pos (by norm_num : (0 : ℝ) < 3) t)))
  have hc : (((triadicIndexBox d H).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) = 0 := by
    have h := avsum_volumeAverage_sub_one_eq_zero (qq := respGrid jStar F) hq t H hφ hintφ hvol
      hφint
    simpa only [hts] using h
  have hA : ∀ w ∈ triadicIndexBox d H, ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)) α β) P := by
    intro w hw
    have hb : ∀ a : CoeffSpace d,
        coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)
          = blockCongr (respG F) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) s w) a) :=
      fun a => coarseBlockMatrix_sub_skew_eq_blockCongr (respg_isSkew F) (hquad w hw a)
    exact integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (respG F) (hblkint w hw) hb
  constructor
  · intro i
    refine normalized_integral_weighted_eq_zero P H
      (fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
      (fun w a => (Mv w a).1 i)
      ((blockResponseMean A (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).1 i)
      hc ?_ ?_
    · intro w hw
      have hpath : (∫ a, (Mv w a).1 i ∂P)
          = ∫ a, (blockResponseMean (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a))
              (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).1 i ∂P := by
        apply integral_congr_ae
        filter_upwards with a
        rw [hMv w hw a]
      rw [hpath]
      have hpair := integral_blockResponseMean P (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F) (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)
        (hA w hw)
      have h1 : (∫ a, (blockResponseMean (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a))
            (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).1 i ∂P)
          = (blockResponseMean (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s w)
              (respCoeffMinus F))
              (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).1 i :=
        congrFun (congrArg Prod.fst hpair) i
      rw [h1]
      exact congrArg (fun M : BlockMat d => (blockResponseMean M
        (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).1 i) (hann w hw)
    · intro w hw
      exact (hint w hw i).1
  · intro i
    refine normalized_integral_weighted_eq_zero P H
      (fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
      (fun w a => (Mv w a).2 i)
      ((blockResponseMean A (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).2 i)
      hc ?_ ?_
    · intro w hw
      have hpath : (∫ a, (Mv w a).2 i ∂P)
          = ∫ a, (blockResponseMean (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a))
              (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).2 i ∂P := by
        apply integral_congr_ae
        filter_upwards with a
        rw [hMv w hw a]
      rw [hpath]
      have hpair := integral_blockResponseMean P (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F) (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)
        (hA w hw)
      have h1 : (∫ a, (blockResponseMean (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a))
            (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).2 i ∂P)
          = (blockResponseMean (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s w)
              (respCoeffMinus F))
              (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).2 i :=
        congrFun (congrArg Prod.snd hpair) i
      rw [h1]
      exact congrArg (fun M : BlockMat d => (blockResponseMean M
        (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).2 i) (hann w hw)
    · intro w hw
      exact (hint w hw i).2

/-- **The weighted cell means of the subcell optimizers cancel, adjoint sign.**  The adjoint twin of
`avsum_weighted_integral_cellAverage_subcellOptimizer_eq_zero` for the recentred coefficient
`a_+ = aᵗ + g` at the load `x^+ = (-p, q^+)`: the normalized sum, over the coarse subcells of the
terminal cell, of the subcell mean of `φ - 1` times the expectation of each coordinate of the
optimizer mean vanishes, for the adjoint coarse block. -/
theorem avsum_weighted_integral_cellAverage_subcellOptimizerPlus_eq_zero {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (hq : IsUnit (respGrid jStar F)) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (ht : t = s + (H : ℤ))
    (Mv : (Fin d → ℤ) → CoeffSpace d → BlockVec d)
    (A : BlockMat d)
    (hMv : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      Mv w a = blockResponseMean (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F a)) (-respP (respMean P jStar F t) e, respqPlus P jStar F t e))
    (hann : ∀ w ∈ triadicIndexBox d H,
      annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F) = A)
    (hint : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d,
      Integrable (fun a => (Mv w a).1 i) P ∧ Integrable (fun a => (Mv w a).2 i) P)
    (hblkint : ∀ w ∈ triadicIndexBox d H,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hquad : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      HasQuadraticMu (adaptedCellAtCenter (respGrid jStar F) s w) (⇑a.1 : CoeffField d)) :
    (∀ i : Fin d, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)
          * ∫ a, (Mv w a).1 i ∂P = 0)
      ∧ (∀ i : Fin d, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)
          * ∫ a, (Mv w a).2 i ∂P = 0) := by
  have hts : t - (H : ℤ) = s := by omega
  have hφint : IntegrableOn φ (HighContrast.adaptedCell (respGrid jStar F) t) :=
    ((hφ.contDiff.continuous).integrable_of_hasCompactSupport hφ.hasCompactSupport).integrableOn
  have hVfin : volume (HighContrast.adaptedCell (respGrid jStar F) t) ≠ ⊤ := by
    rw [← adaptedCellTranslate_zero (respGrid jStar F) t]
    exact Transport.volume_adaptedCellTranslate_ne_top (respGrid jStar F) t 0
  have hintφ : IntegrableOn (fun x => φ x - 1) (HighContrast.adaptedCell (respGrid jStar F) t) :=
    hφint.sub (integrableOn_const hVfin)
  have hvol : (volume (HighContrast.adaptedCell (respGrid jStar F) t)).toReal ≠ 0 := by
    rw [Geometry.volume_adaptedCell_toReal]
    exact mul_ne_zero
      (abs_ne_zero.mpr (IsUnit.ne_zero
        ((Matrix.isUnit_iff_isUnit_det (respGrid jStar F)).mp hq)))
      (pow_ne_zero _ (ne_of_gt (zpow_pos (by norm_num : (0 : ℝ) < 3) t)))
  have hc : (((triadicIndexBox d H).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) = 0 := by
    have h := avsum_volumeAverage_sub_one_eq_zero (qq := respGrid jStar F) hq t H hφ hintφ hvol
      hφint
    simpa only [hts] using h
  have hgnskew : matTranspose (-(respg F)) = -(-(respg F)) := by
    ext i j
    have h := congrFun (congrFun (respg_isSkew F) i) j
    simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply] at h ⊢
    linarith only [h]
  have hA : ∀ w ∈ triadicIndexBox d H, ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)) α β) P := by
    intro w hw
    have hb : ∀ a : CoeffSpace d,
        coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)
          = blockCongr (ofFullBlockMat (toFullBlockMat (blockD d) *
              toFullBlockMat (⟨1, 0, -respg F, 1⟩ : BlockMat d)))
              (coarseBlock (adaptedCellAtCenter (respGrid jStar F) s w) a) := by
      intro a
      have h1 : respCoeffPlus F a
          = fun x => (adjointCoeffField (⇑a.1 : CoeffField d)) x - (-(respg F)) := by
        funext x
        simp only [respCoeffPlus, adjointCoeffField, sub_neg_eq_add]
      have h2 := coarseBlockMatrix_sub_skew_eq_blockCongr
        (U := adaptedCellAtCenter (respGrid jStar F) s w)
        (a := adjointCoeffField (⇑a.1 : CoeffField d)) hgnskew
        (hasQuadraticMu_adjointCoeffField (hquad w hw a))
      have h3 : coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
            (adjointCoeffField (⇑a.1 : CoeffField d))
          = blockCongr (blockD d) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) s w) a) := by
        rw [coarseBlockMatrix_adjointCoeffField_of_exists
          (exists_coarseBlockMatrix_of_hasQuadraticMu (hquad w hw a)), ← blockCongr_blockD]
        rfl
      rw [h1, h2, h3, blockCongr_blockCongr]
    exact integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr _ (hblkint w hw) hb
  constructor
  · intro i
    refine normalized_integral_weighted_eq_zero P H
      (fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
      (fun w a => (Mv w a).1 i)
      ((blockResponseMean A (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).1 i)
      hc ?_ ?_
    · intro w hw
      have hpath : (∫ a, (Mv w a).1 i ∂P)
          = ∫ a, (blockResponseMean (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a))
              (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).1 i ∂P := by
        apply integral_congr_ae
        filter_upwards with a
        rw [hMv w hw a]
      rw [hpath]
      have hpair := integral_blockResponseMean P (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F) (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)
        (hA w hw)
      have h1 : (∫ a, (blockResponseMean (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a))
            (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).1 i ∂P)
          = (blockResponseMean (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s w)
              (respCoeffPlus F))
              (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).1 i :=
        congrFun (congrArg Prod.fst hpair) i
      rw [h1]
      exact congrArg (fun M : BlockMat d => (blockResponseMean M
        (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).1 i) (hann w hw)
    · intro w hw
      exact (hint w hw i).1
  · intro i
    refine normalized_integral_weighted_eq_zero P H
      (fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
      (fun w a => (Mv w a).2 i)
      ((blockResponseMean A (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).2 i)
      hc ?_ ?_
    · intro w hw
      have hpath : (∫ a, (Mv w a).2 i ∂P)
          = ∫ a, (blockResponseMean (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a))
              (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).2 i ∂P := by
        apply integral_congr_ae
        filter_upwards with a
        rw [hMv w hw a]
      rw [hpath]
      have hpair := integral_blockResponseMean P (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F) (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)
        (hA w hw)
      have h1 : (∫ a, (blockResponseMean (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a))
            (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).2 i ∂P)
          = (blockResponseMean (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s w)
              (respCoeffPlus F))
              (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).2 i :=
        congrFun (congrArg Prod.snd hpair) i
      rw [h1]
      exact congrArg (fun M : BlockMat d => (blockResponseMean M
        (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).2 i) (hann w hw)
    · intro w hw
      exact (hint w hw i).2

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The crossed pairing of a weighted flat average of expectations

The cell part of the cutoff-mean defect of `p.response.transfer` is a weighted flat average,
over the coarse subcells of the terminal cell, of the annealed cell means of the doubled
optimizer state.  Because the crossed pairing is bilinear and both the finite flat average and
the expectation are linear, pairing the flat average against the dual variable `Y` — the gradient
slot against `Y.2` and the flux slot against `Y.1` — is the expectation of the weighted flat
average of the pathwise crossed pairings.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The crossed pairing of a weighted flat average of expectations.**  Let `Z` be a finite
index set, `c` a real weight, `M` a family of doubled vectors indexed by `Z` and the sample space,
and let `N` be the doubled vector whose two slots are the weighted flat averages of the
expectations of the corresponding slots of `M`.  Then the crossed pairing of `N` against `Y`
(gradient slot against `Y.2`, flux slot against `Y.1`) equals the expectation of the weighted
flat average of the pathwise crossed pairings.  This is the exchange of the finite average with
the expectation used in `p.response.transfer`. -/
theorem vecDot_avsum_integral_eq_integral_avsum_pairing {d : ℕ} {ι α : Type*}
    [MeasurableSpace α] (P : Measure α) (Z : Finset ι) (c : ι → ℝ) (Y : BlockVec d)
    (M : ι → α → BlockVec d) (N : BlockVec d)
    (hN1 : N.1 = fun i => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * ∫ a, (M w a).1 i ∂P)
    (hN2 : N.2 = fun i => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * ∫ a, (M w a).2 i ∂P)
    (hint1 : ∀ w ∈ Z, ∀ i : Fin d, Integrable (fun a => (M w a).1 i) P)
    (hint2 : ∀ w ∈ Z, ∀ i : Fin d, Integrable (fun a => (M w a).2 i) P) :
    vecDot N.1 Y.2 + vecDot Y.1 N.2
      = ∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
          c w * (vecDot (M w a).1 Y.2 + vecDot Y.1 (M w a).2) ∂P := by
  -- Integrability of the two pathwise pairings at each cell.
  have hpair1 : ∀ w ∈ Z, Integrable (fun a => vecDot (M w a).1 Y.2) P := by
    intro w hw
    simp only [vecDot]
    exact integrable_finsetSum Finset.univ fun i _ => (hint1 w hw i).mul_const (Y.2 i)
  have hpair2 : ∀ w ∈ Z, Integrable (fun a => vecDot Y.1 (M w a).2) P := by
    intro w hw
    simp only [vecDot]
    exact integrable_finsetSum Finset.univ fun i _ => (hint2 w hw i).const_mul (Y.1 i)
  have hsummand : ∀ w ∈ Z, Integrable (fun a =>
      c w * (vecDot (M w a).1 Y.2 + vecDot Y.1 (M w a).2)) P :=
    fun w hw => ((hpair1 w hw).add (hpair2 w hw)).const_mul (c w)
  -- The integral of each pathwise pairing is the pairing of the expected slot.
  have hint_dot1 : ∀ w ∈ Z, (∫ a, vecDot (M w a).1 Y.2 ∂P)
      = vecDot (fun i => ∫ a, (M w a).1 i ∂P) Y.2 := by
    intro w hw
    simp only [vecDot]
    rw [integral_finsetSum Finset.univ fun i _ => (hint1 w hw i).mul_const (Y.2 i)]
    exact Finset.sum_congr rfl fun i _ => by rw [integral_mul_const]
  have hint_dot2 : ∀ w ∈ Z, (∫ a, vecDot Y.1 (M w a).2 ∂P)
      = vecDot Y.1 (fun i => ∫ a, (M w a).2 i ∂P) := by
    intro w hw
    simp only [vecDot]
    rw [integral_finsetSum Finset.univ fun i _ => (hint2 w hw i).const_mul (Y.1 i)]
    exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]
  -- The pairing is linear over the weighted finite average.
  have hdot_wsum : ∀ (x : ι → Vec d) (y : Vec d),
      vecDot (fun i => ∑ w ∈ Z, c w * x w i) y = ∑ w ∈ Z, c w * vecDot (x w) y := by
    intro x y
    simp only [vecDot, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => by ring
  -- The left-hand side, with the defining averages substituted.
  have hL1 : vecDot N.1 Y.2
      = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * vecDot (fun i => ∫ a, (M w a).1 i ∂P) Y.2 := by
    rw [hN1]
    change vecDot (((Z.card : ℝ))⁻¹ •
        (fun i => ∑ w ∈ Z, c w * ∫ a, (M w a).1 i ∂P)) Y.2
      = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * vecDot (fun i => ∫ a, (M w a).1 i ∂P) Y.2
    rw [vecDot_smul_left, hdot_wsum]
  have hL2 : vecDot N.2 Y.1
      = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * vecDot Y.1 (fun i => ∫ a, (M w a).2 i ∂P) := by
    rw [hN2]
    change vecDot (((Z.card : ℝ))⁻¹ •
        (fun i => ∑ w ∈ Z, c w * ∫ a, (M w a).2 i ∂P)) Y.1
      = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * vecDot Y.1 (fun i => ∫ a, (M w a).2 i ∂P)
    rw [vecDot_smul_left, hdot_wsum]
    congr 1
    exact Finset.sum_congr rfl fun w _ => by rw [vecDot_comm]
  have hL : vecDot N.1 Y.2 + vecDot Y.1 N.2
      = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w *
          (vecDot (fun i => ∫ a, (M w a).1 i ∂P) Y.2
            + vecDot Y.1 (fun i => ∫ a, (M w a).2 i ∂P)) := by
    rw [vecDot_comm Y.1 N.2, hL1, hL2, ← mul_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by rw [← mul_add]
  -- The right-hand side, with the integral moved inside the weighted average.
  have hR : (∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
        c w * (vecDot (M w a).1 Y.2 + vecDot Y.1 (M w a).2) ∂P)
      = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w *
          (vecDot (fun i => ∫ a, (M w a).1 i ∂P) Y.2
            + vecDot Y.1 (fun i => ∫ a, (M w a).2 i ∂P)) := by
    rw [integral_const_mul, integral_finsetSum Z hsummand]
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [integral_const_mul, integral_add (hpair1 w hw) (hpair2 w hw),
      hint_dot1 w hw, hint_dot2 w hw]
  rw [hR]
  exact hL

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The whole annealed block of an aligned cell is cell-independent

For a stationary law `P` and a scale `j` above `j_*`, every aligned cell of the generation is an
integer translate of the centred adapted cell, the law is invariant under integer translations,
and the recentring of `p.response.transfer` subtracts (respectively adds) a constant matrix field,
which commutes with translation.  Consequently the whole annealed block of the recentred field
`a_- = a - g` or `a_+ = aᵀ + g` is the same `2d`-by-`2d` matrix at every cell of the generation.

`StationaryAnnealedErrorScalars` records this for the two diagonal sub-blocks only.  The mean
cancellation of
`p.response.transfer` — "the constant cell means cancel after expectation, because the scale-`s`
translations are integral" — needs the whole block, because the annealed cell mean of the
optimizer state is `x + R 𝐀 x` and the off-diagonal sub-blocks enter it.  This file supplies the
off-diagonal half and packages the four fields into a single block equality.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter measurable_translateCoeff
  translateCoeff)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory Geometry

noncomputable section

/-- A translated adapted cell is the translate of the centred adapted cell: both are the image of
`⋄_j^q` under `x ↦ y + x`. -/
private theorem adaptedCellTranslate_eq_translateSet {d : ℕ} (q : Mat d) (j : ℤ) (y : Vec d) :
    HighContrast.adaptedCellTranslate q j y = translateSet y (HighContrast.adaptedCell q j) := by
  ext x
  simp only [HighContrast.adaptedCellTranslate, translateSet, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw, hwxy⟩
    exact ⟨w, hw, by rw [← hwxy, add_comm]⟩
  · rintro ⟨w, hw, hwxy⟩
    exact ⟨w, hw, by rw [hwxy, add_comm]⟩

/-- The coarse block of the recentred field `a_- = a - g` on an integer translate of a cell is the
coarse block of the translated recentred field on the cell.  The recentring subtracts the constant
matrix field `g`, which is unaffected by translation, so the covariance is that of the coarse block
matrix itself. -/
private theorem coarseBlockMatrix_adaptedCellTranslate_respCoeffMinus {d : ℕ}
    (q : Mat d) (j : ℤ) (z : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (HighContrast.adaptedCellTranslate q j (Source.AKL.intTranslation z))
        (respCoeffMinus F a)
      = coarseBlockMatrix (HighContrast.adaptedCell q j) (respCoeffMinus F (translateCoeff z a))
        := by
  rw [adaptedCellTranslate_eq_translateSet,
    coarseBlockMatrix_translateSet_eq_translateCoeffField]
  apply coarseBlockMatrix_congr_of_ae_eq
  apply ae_restrict_of_ae
  filter_upwards [Source.AKL.translateField_ae z a.1] with x hxpt
  exact (congrArg (fun M : Mat d => M - respg F) hxpt).symm

/-- The coarse block of the recentred field `a_+ = aᵀ + g` on an integer translate of a cell is the
coarse block of the translated recentred field on the cell.  The recentring adds the constant matrix
field `g`, which is unaffected by translation, so the covariance is that of the coarse block matrix
itself. -/
private theorem coarseBlockMatrix_adaptedCellTranslate_respCoeffPlus {d : ℕ}
    (q : Mat d) (j : ℤ) (z : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (HighContrast.adaptedCellTranslate q j (Source.AKL.intTranslation z))
        (respCoeffPlus F a)
      = coarseBlockMatrix (HighContrast.adaptedCell q j) (respCoeffPlus F (translateCoeff z a))
        := by
  rw [adaptedCellTranslate_eq_translateSet,
    coarseBlockMatrix_translateSet_eq_translateCoeffField]
  apply coarseBlockMatrix_congr_of_ae_eq
  apply ae_restrict_of_ae
  filter_upwards [Source.AKL.translateField_ae z a.1] with x hxpt
  exact (congrArg (fun M : Mat d => matTranspose M + respg F) hxpt).symm

/-- Stationarity of a scalar functional of the coefficient field: precomposing with an integer
translation leaves the `P`-integral unchanged. -/
private theorem integral_comp_translateCoeff_eq_aux {d : ℕ} (P : Measure (CoeffSpace d))
    (hstat : IsStationaryLaw P) (z : Fin d → ℤ) (f : CoeffSpace d → ℝ)
    (hf : AEStronglyMeasurable f P) :
    (∫ a, f (translateCoeff z a) ∂P) = ∫ a, f a ∂P := by
  have h := integral_map (μ := P) (φ := translateCoeff z)
    (measurable_translateCoeff z).aemeasurable (f := f) (by rw [hstat z]; exact hf)
  rw [hstat z] at h
  exact h.symm

/-- Stationarity of a scalar functional of an aligned cell: an aligned cell is an integer
translate of the centred cell, and the law is invariant under integer translations, so the
`P`-integral of the functional is the same at every aligned cell of the scale. -/
private theorem integral_cellFunctional_adaptedCellAtCenter_eq_aux {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (G : Set (Vec d) → CoeffSpace d → ℝ)
    (hG : ∀ (z : Fin d → ℤ) (a : CoeffSpace d),
      G (HighContrast.adaptedCellTranslate (explicitRoundedGrid jStar m) j
        (Source.AKL.intTranslation z))
          a
        = G (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) (translateCoeff z a))
    (hmeas : AEStronglyMeasurable (G (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j))
      P) :
    (∫ a, G (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) a ∂P)
      = ∫ a, G (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) a ∂P := by
  obtain ⟨z, hz⟩ := Annealed.adaptedCellCenter_eq_intTranslation jStar m hj w
  have hcongr : (∫ a, G (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) a ∂P) =
      ∫ a, G (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) (translateCoeff z a) ∂P
        := by
    apply integral_congr_ae
    filter_upwards with a
    change G (HighContrast.adaptedCellTranslate (explicitRoundedGrid jStar m) j
          (adaptedCellCenter (explicitRoundedGrid jStar m) j w)) a
        = G (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) (translateCoeff z a)
    rw [hz]
    exact hG z a
  rw [hcongr]
  exact integral_comp_translateCoeff_eq_aux P hstat z _ hmeas

/-- Stationarity of one entry of an aligned-cell block: if the block function reads a translated
cell as the centred cell read at the translated coefficient field, then the `P`-integral of any
`blockMatEntry` of the block is the same at every aligned cell of generation `j ≥ j_*`. -/
private theorem integral_cellEntry_adaptedCellAtCenter_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (B : Set (Vec d) → CoeffSpace d → BlockMat d)
    (hB : ∀ (z : Fin d → ℤ) (a : CoeffSpace d),
      B (HighContrast.adaptedCellTranslate (explicitRoundedGrid jStar m) j
        (Source.AKL.intTranslation z)) a
        = B (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) (translateCoeff z a))
    (α β : BlockCoord d)
    (hmeas : AEStronglyMeasurable
      (fun a => blockMatEntry (B (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) a) α
        β) P) :
    (∫ a, blockMatEntry (B (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) a) α β ∂P)
      = ∫ a, blockMatEntry (B (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) a) α β
        ∂P :=
  integral_cellFunctional_adaptedCellAtCenter_eq_aux P hstat jStar m j hj w
    (fun V a => blockMatEntry (B V a) α β)
    (fun z a => congrArg (fun M : BlockMat d => blockMatEntry M α β) (hB z a))
    hmeas

/-- **The whole annealed block of the recentred field is the same on every aligned cell, minus
sign.**  For a stationary law `P` and the recentred coefficient `a_- = a - g` of
`p.response.transfer`, the `P`-entrywise annealed block of the pathwise coarse block on an aligned
cell of scale `j ≥ j_*` is the annealed block of the centred cell, independently of the cell index
`w`.  This is the full `BlockMat` form, off-diagonal sub-blocks included. -/
theorem annealedBlockOf_adaptedCellAtCenter_respCoeffMinus_eq_full {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (F : BlockMat d) (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (hmeas : ∀ (α β : BlockCoord d),
      AEStronglyMeasurable (fun a => blockMatEntry
        (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
          (respCoeffMinus F a)) α β) P) :
    annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) (respCoeffMinus F)
      = annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffMinus F) := by
  apply blockMat_ext
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffMinus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffMinus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inl i) (Sum.inl k) (hmeas (Sum.inl i) (Sum.inl k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffMinus F)).upperLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid
            jStar m) j w)
              (respCoeffMinus F a)) (Sum.inl i) (Sum.inl k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffMinus F)).upperLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid
            jStar m) j)
              (respCoeffMinus F a)) (Sum.inl i) (Sum.inl k) ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffMinus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffMinus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inl i) (Sum.inr k) (hmeas (Sum.inl i) (Sum.inr k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffMinus F)).upperRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid
            jStar m) j w)
              (respCoeffMinus F a)) (Sum.inl i) (Sum.inr k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffMinus F)).upperRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid
            jStar m) j)
              (respCoeffMinus F a)) (Sum.inl i) (Sum.inr k) ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffMinus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffMinus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inr i) (Sum.inl k) (hmeas (Sum.inr i) (Sum.inl k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffMinus F)).lowerLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid
            jStar m) j w)
              (respCoeffMinus F a)) (Sum.inr i) (Sum.inl k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffMinus F)).lowerLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid
            jStar m) j)
              (respCoeffMinus F a)) (Sum.inr i) (Sum.inl k) ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffMinus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffMinus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inr i) (Sum.inr k) (hmeas (Sum.inr i) (Sum.inr k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffMinus F)).lowerRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid
            jStar m) j w)
              (respCoeffMinus F a)) (Sum.inr i) (Sum.inr k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffMinus F)).lowerRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid
            jStar m) j)
              (respCoeffMinus F a)) (Sum.inr i) (Sum.inr k) ∂P := rfl
    rw [hred, hred']
    exact h

/-- **The whole annealed block of the recentred field is the same on every aligned cell, plus
sign.**  For a stationary law `P` and the recentred coefficient `a_+ = aᵀ + g` of
`p.response.transfer`, the `P`-entrywise annealed block of the pathwise coarse block on an aligned
cell of scale `j ≥ j_*` is the annealed block of the centred cell, independently of the cell index
`w`.  This is the full `BlockMat` form, off-diagonal sub-blocks included. -/
theorem annealedBlockOf_adaptedCellAtCenter_respCoeffPlus_eq_full {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (F : BlockMat d) (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (hmeas : ∀ (α β : BlockCoord d),
      AEStronglyMeasurable (fun a => blockMatEntry
        (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
          (respCoeffPlus F a)) α β) P) :
    annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) (respCoeffPlus F)
      = annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffPlus F) := by
  apply blockMat_ext
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffPlus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffPlus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inl i) (Sum.inl k) (hmeas (Sum.inl i) (Sum.inl k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffPlus F)).upperLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid
            jStar m) j w)
              (respCoeffPlus F a)) (Sum.inl i) (Sum.inl k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffPlus F)).upperLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid
            jStar m) j)
              (respCoeffPlus F a)) (Sum.inl i) (Sum.inl k) ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffPlus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffPlus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inl i) (Sum.inr k) (hmeas (Sum.inl i) (Sum.inr k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffPlus F)).upperRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid
            jStar m) j w)
              (respCoeffPlus F a)) (Sum.inl i) (Sum.inr k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffPlus F)).upperRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid
            jStar m) j)
              (respCoeffPlus F a)) (Sum.inl i) (Sum.inr k) ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffPlus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffPlus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inr i) (Sum.inl k) (hmeas (Sum.inr i) (Sum.inl k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffPlus F)).lowerLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid
            jStar m) j w)
              (respCoeffPlus F a)) (Sum.inr i) (Sum.inl k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffPlus F)).lowerLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid
            jStar m) j)
              (respCoeffPlus F a)) (Sum.inr i) (Sum.inl k) ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffPlus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffPlus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inr i) (Sum.inr k) (hmeas (Sum.inr i) (Sum.inr k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffPlus F)).lowerRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid
            jStar m) j w)
              (respCoeffPlus F a)) (Sum.inr i) (Sum.inr k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffPlus F)).lowerRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid
            jStar m) j)
              (respCoeffPlus F a)) (Sum.inr i) (Sum.inr k) ∂P := rfl
    rw [hred, hred']
    exact h

end

end HCPolySupport.HighContrast.Multiscale
end
