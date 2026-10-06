/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TerminalEnergyDeficitBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.BesovScaleSummationToolkit
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.SourceLoadHeadBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.StationaryAnnealedErrorScalars

/-!
# High-contrast homogenization: Entry.Response.Rows.AbstractCellPairingBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Abstract Cell-Pairing Row of the Cutoff-Mean Estimate

For a stationary law above the threshold `j_*`, the annealed coarse block of `a_-` or `a_+` is
the same matrix at every aligned cell of a generation, so the flat average, over the generation's
cells, of the square of each cell's own two-term annealed head collapses to the single head at
the origin cell. Because the scale-`s` translations of the adapted grid are integral, the cell
averages of the cutoff fluctuation over those cells share that common annealed value, and exact
partition averaging turns their weighted average into the average of the fluctuation over the
terminal cell, which vanishes since a cutoff has mean one. Combining the head collapse with the
annealed Cauchy-Schwarz inequality that moves the expectation outside the flat average of the
pathwise cell-pairing bound identifies the collapsed head with the depth-zero summand of `L_s`,
assembling the abstract cell-pairing row bounded by `√(L_s^∓) · √(2 tau^∓)`.
The module serves the manuscript's `p.response.transfer`: it bounds the cell half of the
cutoff-mean row by the source load `L_s` and the scale defect `tau`.
-/

section
/-!
## The flat average of the annealed heads collapses to the origin cell

In the cell half of the cutoff-mean row of `p.response.transfer` the terminal cell is
subdivided into the `3^{Hd}` cells of the coarse generation `s`, and each contributes the
square of the two-term head of its own annealed block.  Above `j_*` every aligned cell of a
given generation is an integer translate of the centred one and the law is translation
invariant, so all those annealed blocks coincide: the flat average over the triadic index
box collapses to the single head at the index `0`, the depth-zero summand of the source load
`respSourceLoad`.  This is the step that makes the scale-`s` subdivision cost nothing.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory Geometry

noncomputable section

/-- **The flat average of the annealed heads collapses, minus sign.**  For a stationary law
`P` and the recentred coefficient `a_- = a - g` of `p.response.transfer`, at a scale
`j ≥ j_*` the normalized sum over the `3^{nd}` triadic subcells `adaptedCellAtCenter (respGrid
jStar F) j w`
of the squared two-term head of the corresponding annealed block is the head of the single cell
at the index `0`.  Every subcell is an integer translate of the centred cell and the law is
translation invariant, so the summand is independent of `w`. -/
theorem avsum_sq_head_annealed_respCoeffMinus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (F : BlockMat d)
    (j : ℤ) (hj : (jStar : ℤ) ≤ j) (n : ℕ) (Y : BlockVec d)
    (hmeas : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) j)
        (respCoeffMinus F a)).upperLeft i k) P)
    (hmeas' : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) j)
        (respCoeffMinus F a)).lowerRight i k) P) :
    ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
        (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffMinus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffMinus F)).lowerRight Y.2))) ^ 2
      = (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j 0) (respCoeffMinus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j 0) (respCoeffMinus F)).lowerRight Y.2)))
                ^ 2 := by
  have h0mem : (0 : Fin d → ℤ) ∈ triadicIndexBox d n := by
    rw [triadicIndexBox, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_Icc.mpr
      ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  have hcard : ((triadicIndexBox d n).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr ⟨0, h0mem⟩))
  simp only [respGrid]
  have hsum : ∀ w ∈ triadicIndexBox d n,
      (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
              F)) j w)
            (respCoeffMinus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
              F)) j w)
            (respCoeffMinus F)).lowerRight Y.2))) ^ 2
      = (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
              F)) j 0)
            (respCoeffMinus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
              F)) j 0)
            (respCoeffMinus F)).lowerRight Y.2))) ^ 2 := by
    intro w _
    have hw := annealedBlockOf_adaptedCellAtCenter_respCoeffMinus_eq P hstat jStar
      (explicitCanonicalMetric F) F j hj w hmeas hmeas'
    have h0 := annealedBlockOf_adaptedCellAtCenter_respCoeffMinus_eq P hstat jStar
      (explicitCanonicalMetric F) F j hj 0 hmeas hmeas'
    simp only [hw.1, hw.2, h0.1, h0.2]
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hcard _

/-- **The flat average of the annealed heads collapses, plus sign.**  For a stationary law
`P` and the recentred coefficient `a_+ = aᵀ + g` of `p.response.transfer`, at a scale
`j ≥ j_*` the normalized sum over the `3^{nd}` triadic subcells `adaptedCellAtCenter (respGrid
jStar F) j w`
of the squared two-term head of the corresponding annealed block is the head of the single cell
at the index `0`.  Every subcell is an integer translate of the centred cell and the law is
translation invariant, so the summand is independent of `w`. -/
theorem avsum_sq_head_annealed_respCoeffPlus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (F : BlockMat d)
    (j : ℤ) (hj : (jStar : ℤ) ≤ j) (n : ℕ) (Y : BlockVec d)
    (hmeas : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) j)
        (respCoeffPlus F a)).upperLeft i k) P)
    (hmeas' : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) j)
        (respCoeffPlus F a)).lowerRight i k) P) :
    ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
        (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffPlus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffPlus F)).lowerRight Y.2))) ^ 2
      = (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j 0) (respCoeffPlus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
              (adaptedCellAtCenter (respGrid jStar F) j 0) (respCoeffPlus F)).lowerRight Y.2)))
                ^ 2 := by
  have h0mem : (0 : Fin d → ℤ) ∈ triadicIndexBox d n := by
    rw [triadicIndexBox, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_Icc.mpr
      ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  have hcard : ((triadicIndexBox d n).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr ⟨0, h0mem⟩))
  simp only [respGrid]
  have hsum : ∀ w ∈ triadicIndexBox d n,
      (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
              F)) j w)
            (respCoeffPlus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
              F)) j w)
            (respCoeffPlus F)).lowerRight Y.2))) ^ 2
      = (Real.sqrt (vecDot Y.1 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
              F)) j 0)
            (respCoeffPlus F)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (annealedBlockOf P
            (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
              F)) j 0)
            (respCoeffPlus F)).lowerRight Y.2))) ^ 2 := by
    intro w _
    have hw := annealedBlockOf_adaptedCellAtCenter_respCoeffPlus_eq P hstat jStar
      (explicitCanonicalMetric F) F j hj w hmeas hmeas'
    have h0 := annealedBlockOf_adaptedCellAtCenter_respCoeffPlus_eq P hstat jStar
      (explicitCanonicalMetric F) F j hj 0 hmeas hmeas'
    simp only [hw.1, hw.2, h0.1, h0.2]
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hcard _

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cell half of the cutoff-mean row on the carriers

The cell half of the two cutoff-mean rows of `e.response.cutoff.estimate` is the flat average,
over the `3^{Hd}` coarse cells of the terminal cell, of the cell mean of the cutoff times the
crossed dual pairing of that cell's optimizer-mean defect.  AK's direct full-dual pairing bounds
each cell's pairing pathwise by the cell's own two-term head times the square root of twice the
cell deficit; Cauchy--Schwarz with the expectation outside the flat average separates the two
factors, the expectation meets the pathwise coarse blocks linearly through
`integral_avsum_pathwise_head_le`, stationarity collapses the flat average of the annealed blocks
to the single cell at the origin through `avsum_sq_head_annealed_respCoeffMinus_eq`, and
`sq_head_le_respSourceLoad` identifies that collapsed head with the depth-zero summand of the
source load `L_s` of `p.response.transfer`.  The second factor is the annealed flat average of the
cell deficits, which is twice the scale defect `tau`.  This module assembles those landed pieces
into the two carrier-level estimates, one for each sign of the recentred coefficient.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- **The cell half of the cutoff-mean row, minus sign.**  On the carriers of
`p.response.transfer`, let `pairing` be the full-dual pairing of the optimizer-mean defect and let
`D` be the scalar cell deficit.  If each cell's pairing is controlled pathwise by the cell's own
two-term head
`√(P · b_s^{1/2} P) + √(Q · (S_{*,s})^{-1/2} Q)` of the pathwise coarse block of the recentred
coefficient `a_- = a - g` times `√(2 D)`, and the annealed flat average of `2 D` is `2 tau^-`,
then, provided the pathwise coarse blocks are nonnegative, integrable and measurable as
prescribed, the modulus of the sample expectation of the cutoff-weighted flat average of the
pairing is at most `√(L_s^-) * √(2 tau^-)`, where `L_s^-` is the source load of
`p.response.transfer` at the recentred coefficient `a_-` and the dual variable `Y^-`.  This is the
cell half of the cutoff-mean row, with the expectation outside the flat average and no inversion
of an annealed block and no Jensen step. -/
theorem abs_integral_avsum_weighted_pairing_le_respLsMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (hjs : (jStar : ℤ) ≤ s)
    (c : (Fin d → ℤ) → ℝ) (hc : ∀ w ∈ triadicIndexBox d H, |c w| ≤ 1)
    (pairing D : (Fin d → ℤ) → CoeffSpace d → ℝ)
    (hsum : Summable (respSourceLoadSummand P jStar F s (respCoeffMinus F)
      (respYMinus P jStar F t e)))
    (hD : ∀ w ∈ triadicIndexBox d H, ∀ a, 0 ≤ D w a)
    (hbd : ∀ w ∈ triadicIndexBox d H, ∀ a,
      |pairing w a|
        ≤ (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
              (respYMinus P jStar F t e).1))
            + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
              (respYMinus P jStar F t e).2)))
          * Real.sqrt (2 * D w a))
    (hDval : (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, 2 * D w a ∂P) = 2 * respTauMinus P jStar F s t e)
    (hUL : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d, 0 ≤
      vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
        (respYMinus P jStar F t e).1))
    (hLR : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d, 0 ≤
      vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
        (respYMinus P jStar F t e).2))
    (hentUL : ∀ w ∈ triadicIndexBox d H, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F a)).upperLeft i j) P)
    (hentLR : ∀ w ∈ triadicIndexBox d H, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F a)).lowerRight i j) P)
    (hqUL : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
        (respYMinus P jStar F t e).1)) P)
    (hqLR : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
        (respYMinus P jStar F t e).2)) P)
    (hcross : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
            (respYMinus P jStar F t e).1))
        * Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
            (respYMinus P jStar F t e).2))) P)
    (hsq : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
              (respYMinus P jStar F t e).1))
          + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
              (respYMinus P jStar F t e).2))) ^ 2) P)
    (hmeas : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s)
        (respCoeffMinus F a)).upperLeft i k) P)
    (hmeas' : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s)
        (respCoeffMinus F a)).lowerRight i k) P)
    (hFint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
                (respYMinus P jStar F t e).1))
            + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
                (respYMinus P jStar F t e).2))) ^ 2) P)
    (hDint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, 2 * D w a) P)
    (hMidint : Integrable (fun a =>
      Real.sqrt (((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
                  (respYMinus P jStar F t e).1))
              + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
                  (respYMinus P jStar F t e).2))) ^ 2)
        * Real.sqrt (((triadicIndexBox d H).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d H, 2 * D w a)) P)
    (hPint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, c w *
        (Real.sqrt ((Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                    (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
                    (respYMinus P jStar F t e).1))
                + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                    (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
                    (respYMinus P jStar F t e).2))) ^ 2) * Real.sqrt (2 * D w a))) P)
    (hPint' : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, c w * pairing w a) P) :
    |∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H, c w * pairing w a ∂P|
      ≤ Real.sqrt (respLsMinus P jStar F s t e)
        * Real.sqrt (2 * respTauMinus P jStar F s t e) := by
  have hG : ∀ w ∈ triadicIndexBox d H, ∀ a, 0 ≤
      (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
            (respYMinus P jStar F t e).1))
        + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
            (respYMinus P jStar F t e).2))) := by
    intro w hw a
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hGsq : (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
              (respYMinus P jStar F t e).1))
          + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
              (respYMinus P jStar F t e).2))) ^ 2 ∂P)
      ≤ respLsMinus P jStar F s t e := by
    calc
      (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d H,
            (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
                  (respYMinus P jStar F t e).1))
              + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
                  (respYMinus P jStar F t e).2))) ^ 2 ∂P)
          ≤ ((triadicIndexBox d H).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d H,
                (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (annealedBlockOf P
                      (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F)).upperLeft
                      (respYMinus P jStar F t e).1))
                  + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (annealedBlockOf P
                      (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F)).lowerRight
                      (respYMinus P jStar F t e).2))) ^ 2 :=
            integral_avsum_pathwise_head_le (P := P) (jStar := jStar) (F := F)
              (k := s) (n := H) (b := respCoeffMinus F) (Y := respYMinus P jStar F t e)
              hUL hLR hentUL hentLR hqUL hqLR hcross hsq
      _ = (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) s 0) (respCoeffMinus F)).upperLeft
                (respYMinus P jStar F t e).1))
            + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) s 0) (respCoeffMinus F)).lowerRight
                (respYMinus P jStar F t e).2))) ^ 2 :=
            avsum_sq_head_annealed_respCoeffMinus_eq (P := P) (hstat := hstat)
              (jStar := jStar) (F := F) (j := s) (hj := hjs) (n := H)
              (Y := respYMinus P jStar F t e) hmeas hmeas'
      _ ≤ respLsMinus P jStar F s t e := by
            simpa only [respLsMinus] using
              sq_head_le_respSourceLoad (P := P) (jStar := jStar) (F := F) (s := s)
                (b := respCoeffMinus F) (Y := respYMinus P jStar F t e) hsum
  exact abs_integral_flat_weighted_pairing_le (P := P) (Z := triadicIndexBox d H)
    (c := c) (hc := hc) (pairing := pairing)
    (G := fun w a =>
      (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
            (respYMinus P jStar F t e).1))
        + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
            (respYMinus P jStar F t e).2))))
    (D := D) (Lhead := respLsMinus P jStar F s t e)
    (tau := respTauMinus P jStar F s t e)
    hG hD hbd hGsq hDval hFint hDint hMidint hPint hPint'

/-- **The cell half of the cutoff-mean row, plus sign.**  This is the `Plus` twin of
`abs_integral_avsum_weighted_pairing_le_respLsMinus`: the same flat-average estimate with the
recentred coefficient `a_+ = aᵀ + g`, the dual variable `Y^+`, the annealed head collapse
`avsum_sq_head_annealed_respCoeffPlus_eq`, the scale defect `tau^+` and the source load `L_s^+` of
`p.response.transfer`. -/
theorem abs_integral_avsum_weighted_pairing_le_respLsPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (hjs : (jStar : ℤ) ≤ s)
    (c : (Fin d → ℤ) → ℝ) (hc : ∀ w ∈ triadicIndexBox d H, |c w| ≤ 1)
    (pairing D : (Fin d → ℤ) → CoeffSpace d → ℝ)
    (hsum : Summable (respSourceLoadSummand P jStar F s (respCoeffPlus F)
      (respYPlus P jStar F t e)))
    (hD : ∀ w ∈ triadicIndexBox d H, ∀ a, 0 ≤ D w a)
    (hbd : ∀ w ∈ triadicIndexBox d H, ∀ a,
      |pairing w a|
        ≤ (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
              (respYPlus P jStar F t e).1))
            + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
              (respYPlus P jStar F t e).2)))
          * Real.sqrt (2 * D w a))
    (hDval : (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, 2 * D w a ∂P) = 2 * respTauPlus P jStar F s t e)
    (hUL : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d, 0 ≤
      vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
        (respYPlus P jStar F t e).1))
    (hLR : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d, 0 ≤
      vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
        (respYPlus P jStar F t e).2))
    (hentUL : ∀ w ∈ triadicIndexBox d H, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F a)).upperLeft i j) P)
    (hentLR : ∀ w ∈ triadicIndexBox d H, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F a)).lowerRight i j) P)
    (hqUL : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
        (respYPlus P jStar F t e).1)) P)
    (hqLR : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
        (respYPlus P jStar F t e).2)) P)
    (hcross : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
            (respYPlus P jStar F t e).1))
        * Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
            (respYPlus P jStar F t e).2))) P)
    (hsq : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
              (respYPlus P jStar F t e).1))
          + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
              (respYPlus P jStar F t e).2))) ^ 2) P)
    (hmeas : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s)
        (respCoeffPlus F a)).upperLeft i k) P)
    (hmeas' : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s)
        (respCoeffPlus F a)).lowerRight i k) P)
    (hFint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
                (respYPlus P jStar F t e).1))
            + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
                (respYPlus P jStar F t e).2))) ^ 2) P)
    (hDint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, 2 * D w a) P)
    (hMidint : Integrable (fun a =>
      Real.sqrt (((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
                  (respYPlus P jStar F t e).1))
              + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
                  (respYPlus P jStar F t e).2))) ^ 2)
        * Real.sqrt (((triadicIndexBox d H).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d H, 2 * D w a)) P)
    (hPint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, c w *
        (Real.sqrt ((Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                    (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
                    (respYPlus P jStar F t e).1))
                + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                    (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
                    (respYPlus P jStar F t e).2))) ^ 2) * Real.sqrt (2 * D w a))) P)
    (hPint' : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, c w * pairing w a) P) :
    |∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H, c w * pairing w a ∂P|
      ≤ Real.sqrt (respLsPlus P jStar F s t e)
        * Real.sqrt (2 * respTauPlus P jStar F s t e) := by
  have hG : ∀ w ∈ triadicIndexBox d H, ∀ a, 0 ≤
      (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
            (respYPlus P jStar F t e).1))
        + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
            (respYPlus P jStar F t e).2))) := by
    intro w hw a
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hGsq : (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
              (respYPlus P jStar F t e).1))
          + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
              (respYPlus P jStar F t e).2))) ^ 2 ∂P)
      ≤ respLsPlus P jStar F s t e := by
    calc
      (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d H,
            (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
                  (respYPlus P jStar F t e).1))
              + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
                  (respYPlus P jStar F t e).2))) ^ 2 ∂P)
          ≤ ((triadicIndexBox d H).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d H,
                (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (annealedBlockOf P
                      (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F)).upperLeft
                      (respYPlus P jStar F t e).1))
                  + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (annealedBlockOf P
                      (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F)).lowerRight
                      (respYPlus P jStar F t e).2))) ^ 2 :=
            integral_avsum_pathwise_head_le (P := P) (jStar := jStar) (F := F)
              (k := s) (n := H) (b := respCoeffPlus F) (Y := respYPlus P jStar F t e)
              hUL hLR hentUL hentLR hqUL hqLR hcross hsq
      _ = (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) s 0) (respCoeffPlus F)).upperLeft
                (respYPlus P jStar F t e).1))
            + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) s 0) (respCoeffPlus F)).lowerRight
                (respYPlus P jStar F t e).2))) ^ 2 :=
            avsum_sq_head_annealed_respCoeffPlus_eq (P := P) (hstat := hstat)
              (jStar := jStar) (F := F) (j := s) (hj := hjs) (n := H)
              (Y := respYPlus P jStar F t e) hmeas hmeas'
      _ ≤ respLsPlus P jStar F s t e := by
            simpa only [respLsPlus] using
              sq_head_le_respSourceLoad (P := P) (jStar := jStar) (F := F) (s := s)
                (b := respCoeffPlus F) (Y := respYPlus P jStar F t e) hsum
  exact abs_integral_flat_weighted_pairing_le (P := P) (Z := triadicIndexBox d H)
    (c := c) (hc := hc) (pairing := pairing)
    (G := fun w a =>
      (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
            (respYPlus P jStar F t e).1))
        + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
            (respYPlus P jStar F t e).2))))
    (D := D) (Lhead := respLsPlus P jStar F s t e)
    (tau := respTauPlus P jStar F s t e)
    hG hD hbd hGsq hDval hFint hDint hMidint hPint hPint'

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Cancellation of constant cell means after expectation

In the centred cutoff decomposition of `p.response.transfer`, the constant cell means cancel after
expectation.  The scale-`s` translations of the grid are integral, so the cell averages of the
cutoff fluctuation share a common annealed value.  Exact partition averaging turns their average
over the generation-`(t - n)` triadic subdivision of the terminal cell into the average of `φ - 1`
over that cell, and that average vanishes because the cutoff class has volume average one.  The
same partition then shows that any weighting of a family of cell functionals with a common
annealed value and mean-zero normalized weights integrates to zero.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Cancellation of the cell means of the cutoff fluctuation.**  The normalized sum of the cell
averages of `φ - 1` over the `3 ^ (n * d)` depth-`n` triadic subcells of the adapted cell
`HighContrast.adaptedCell qq t` equals the average of `φ - 1` over that cell, which is zero because
`φ` has volume average one there.  This is the first cancellation in `p.response.transfer`. -/
theorem avsum_volumeAverage_sub_one_eq_zero {d : ℕ} [NeZero d] {qq : Mat d} (hq : IsUnit qq)
    (t : ℤ) (n : ℕ) {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ)
    (hint : IntegrableOn (fun x => φ x - 1) (HighContrast.adaptedCell qq t))
    (hvol : (volume (HighContrast.adaptedCell qq t)).toReal ≠ 0)
    (hφint : IntegrableOn φ (HighContrast.adaptedCell qq t)) :
    (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => φ x - 1)
      = 0 := by
  rw [avsum_volumeAverage_eq qq hq t n hint]
  exact volumeAverage_sub_one_eq_zero (HighContrast.adaptedCell qq t)
    (IsResponseCutoff.volumeAverage_eq_one hφ) hvol hφint

/-- **Mean-zero weighting of a common annealed value.**  If each cell functional `G w` has the same
annealed value `m` and the weights `c w` have normalized sum zero, then the annealed integral of
the weighted sum vanishes.  The common value is the one supplied by the integrality of the
scale-`s` translations; this is the second cancellation in `p.response.transfer`. -/
theorem integral_avsum_mul_eq_zero {d : ℕ} {α : Type*} [MeasurableSpace α] (P : Measure α)
    (n : ℕ) (c : (Fin d → ℤ) → ℝ) (G : (Fin d → ℤ) → α → ℝ) (m : ℝ)
    (hc : (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w = 0)
    (hG : ∀ w ∈ triadicIndexBox d n, (∫ a, G w a ∂P) = m)
    (hint : ∀ w ∈ triadicIndexBox d n, Integrable (G w) P) :
    (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * G w a ∂P) = 0 := by
  calc (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * G w a ∂P)
      = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∫ a, ∑ w ∈ triadicIndexBox d n, c w * G w a ∂P := by
        rw [integral_const_mul]
    _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, ∫ a, c w * G w a ∂P := by
        rw [integral_finsetSum (triadicIndexBox d n)
          (fun w hw => (hint w hw).const_mul (c w))]
    _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w * m := by
        have hsum : (∑ w ∈ triadicIndexBox d n, ∫ a, c w * G w a ∂P)
            = ∑ w ∈ triadicIndexBox d n, c w * m :=
          Finset.sum_congr rfl (fun w hw => by rw [integral_const_mul, hG w hw])
        rw [hsum]
    _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ((∑ w ∈ triadicIndexBox d n, c w) * m) := by
        rw [← Finset.sum_mul]
    _ = ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, c w) * m := by
        rw [← mul_assoc]
    _ = 0 := by
        rw [hc, zero_mul]

end

end HCPolySupport.HighContrast.Multiscale
end
