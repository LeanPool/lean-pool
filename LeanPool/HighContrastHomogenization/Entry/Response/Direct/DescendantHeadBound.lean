/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.DescendantIndexStationarity
public import LeanPool.HighContrastHomogenization.Entry.Response.Pairing.CoarseBlockFenchelPairing
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CarrierIntegrabilityConditions
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.OptimizerMeanRowCarriers
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.SourceLoadHeadBound
public import Mathlib.Basic.ENNReal.Holder
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# High-contrast homogenization: Entry.Response.Direct.DescendantHeadBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed head of one descendant generation, and its integrands

Cutting the terminal cell into the `3^{(H+n)d}` aligned cells of generation `s - n`, the pathwise
full-dual pairing on each of them produces a two-term head
`√(Y₁ · A(V;a_-)_{11} Y₁) + √(Y₂ · A(V;b)_{22} Y₂)`, and its annealed flat average over all these
cells is bounded, in nine analytic steps, by the corresponding entry of the annealed coarse block;
the same bound is then read off on the concrete data the response problem actually supplies. The
descendant sum of `p.response.transfer` uses this bound to read the generation-`n` layer of the
source load `𝓛_s` against the expectation of the flat average of the squared head, for both signs.
The pathwise expansion of the cutoff pairing that this rests on needs six scalar integrands to be
integrable on the terminal cell, each a product of the bounded cutoff with either a coordinate of
the doubled optimizer state, a coordinate pairing of that state with a fixed vector, or a constant,
and this file records that integrability.
-/

section
/-!
## The annealed head of the descendant layer of the source load

Step ζ of the cutoff-mean row of `p.response.transfer` at descendant depth `n`.  The terminal
cell is cut into the `3^{(H+n)d}` aligned cells of generation `s - n`; on each of them the
pathwise full-dual pairing produces the head `√(Y₁ · 𝐀(V; a_-).upperLeft Y₁) +
√(Y₂ · 𝐀(V; b).lowerRight Y₂)`, and its annealed flat average over all `3^{(H+n)d}` cells is at
most the depth-`n` layer of `respSourceLoad`, i.e. the flat average over the `3^{nd}` descendants
of ONE scale-`s` cell of the same head read on the ANNEALED block.

The estimate is the two-term expectation bound `integral_sq_sqrt_add_sqrt_le` applied cell by
cell, the identification of each pathwise quadratic form with the annealed one
(`integral_vecDot_coarseBlock_upperLeft`/`…_lowerRight`), the grouped-digit decomposition of the
index box `sum_triadicIndexBox_add`, and the stationarity identity
`annealedBlockOf_descendant_respCoeffMinus_eq`/`…_Plus_eq`, which makes the summand independent
of the outer index and collapses the outer sum.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The descendant layer bound, uniformly in the recentred coefficient family.**  For an
arbitrary family `b` of coefficient fields, if the pathwise head is integrable cell by cell and
the annealed block of a descendant cell depends only on the inner index, then the annealed flat
average of the squared pathwise head over the depth-`(H + n)` index box is at most the depth-`n`
layer of the source load read on the annealed block. -/
private theorem integral_avsum_sq_head_descendant_le_aux {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (b : CoeffSpace d → CoeffField d) (H n : ℕ) (s : ℤ) (Y : BlockVec d)
    (hUL : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (b a)).upperLeft Y.1)) P)
    (hLR : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (b a)).lowerRight Y.2)) P)
    (hULe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (b a)).upperLeft i k) P)
    (hLRe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (b a)).lowerRight i k) P)
    (hUL0 : ∀ W : Fin d → ℤ, ∀ a, 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (b a)).upperLeft Y.1))
    (hLR0 : ∀ W : Fin d → ℤ, ∀ a, 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (b a)).lowerRight Y.2))
    (hcross : ∀ W : Fin d → ℤ, Integrable (fun a =>
      Real.sqrt (vecDot Y.1 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
            (b a)).upperLeft Y.1))
        * Real.sqrt (vecDot Y.2 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
            (b a)).lowerRight Y.2))) P)
    (hsq : ∀ W : Fin d → ℤ, Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (b a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (b a)).lowerRight Y.2))) ^ 2) P)
    (hdesc : ∀ w z : Fin d → ℤ,
      (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
          (fun i => 3 ^ n * w i + z i)) b).upperLeft
        = (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
            b).upperLeft ∧
      (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
          (fun i => 3 ^ n * w i + z i)) b).lowerRight
        = (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
            b).lowerRight) :
    (∫ a, (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d (H + n),
        (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (b a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (b a)).lowerRight Y.2))) ^ 2 ∂P)
      ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  b).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  b).lowerRight Y.2))) ^ 2 := by
  have hterm : ∀ W : Fin d → ℤ,
      (∫ a, (Real.sqrt (vecDot Y.1 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (b a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (b a)).lowerRight Y.2))) ^ 2 ∂P)
        ≤ (Real.sqrt (vecDot Y.1 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                b).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                b).lowerRight Y.2))) ^ 2 := by
    intro W
    have hhead := integral_sq_sqrt_add_sqrt_le P (hUL W) (hLR W) (hUL0 W) (hLR0 W)
      (hcross W) (hsq W)
    have hfbar := integral_vecDot_coarseBlock_upperLeft P
      (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W) b Y.1 (hULe W)
    have hgbar := integral_vecDot_coarseBlock_lowerRight P
      (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W) b Y.2 (hLRe W)
    rw [hfbar, hgbar] at hhead
    exact hhead
  have hsum_bound :
      (∑ W ∈ triadicIndexBox d (H + n),
          ∫ a, (Real.sqrt (vecDot Y.1 (matVecMul
                (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                  (b a)).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                  (b a)).lowerRight Y.2))) ^ 2 ∂P)
        ≤ ∑ W ∈ triadicIndexBox d (H + n),
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                    b).upperLeft Y.1))
                + Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                    b).lowerRight Y.2))) ^ 2 :=
    Finset.sum_le_sum (fun W _ => hterm W)
  have hLHS :
      (∫ a, (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
          ∑ W ∈ triadicIndexBox d (H + n),
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                    (b a)).upperLeft Y.1))
                + Real.sqrt (vecDot Y.2 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                    (b a)).lowerRight Y.2))) ^ 2 ∂P)
        = (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
          ∑ W ∈ triadicIndexBox d (H + n),
            ∫ a, (Real.sqrt (vecDot Y.1 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                    (b a)).upperLeft Y.1))
                + Real.sqrt (vecDot Y.2 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                    (b a)).lowerRight Y.2))) ^ 2 ∂P := by
    rw [integral_const_mul,
      integral_finsetSum (triadicIndexBox d (H + n)) (fun W _ => hsq W)]
  have hcHn_inv_nonneg : 0 ≤ (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ := by
    have hpos : (0 : ℝ) < ((triadicIndexBox d (H + n)).card : ℝ) := by
      rw [card_triadicIndexBox (H + n)]
      positivity
    exact inv_nonneg.mpr (le_of_lt hpos)
  have hreindex :
      (∑ W ∈ triadicIndexBox d (H + n),
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                  b).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                  b).lowerRight Y.2))) ^ 2)
        = ∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
                      (fun i => 3 ^ n * w i + z i)) b).upperLeft Y.1))
                + Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
                      (fun i => 3 ^ n * w i + z i)) b).lowerRight Y.2))) ^ 2 :=
    sum_triadicIndexBox_add (d := d) H n
      (fun W => (Real.sqrt (vecDot Y.1 (matVecMul
            (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
            (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              b).lowerRight Y.2))) ^ 2)
  have hdesc_sum :
      (∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
                    (fun i => 3 ^ n * w i + z i)) b).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
                    (fun i => 3 ^ n * w i + z i)) b).lowerRight Y.2))) ^ 2)
        = ∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                    b).upperLeft Y.1))
                + Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                    b).lowerRight Y.2))) ^ 2 := by
    refine Finset.sum_congr rfl (fun w _ => ?_)
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [(hdesc w z).1, (hdesc w z).2]
  have hcollapse :
      (∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  b).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  b).lowerRight Y.2))) ^ 2)
        = ((triadicIndexBox d H).card : ℝ) *
            ∑ z ∈ triadicIndexBox d n,
              (Real.sqrt (vecDot Y.1 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                      b).upperLeft Y.1))
                  + Real.sqrt (vecDot Y.2 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                      b).lowerRight Y.2))) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (((triadicIndexBox d (H + n)).card : ℝ))
      = (((triadicIndexBox d H).card : ℝ)) * (((triadicIndexBox d n).card : ℝ)) := by
    rw [card_triadicIndexBox (H + n), card_triadicIndexBox H, card_triadicIndexBox n,
      pow_add, mul_pow]
  have hcH_pos : (0 : ℝ) < ((triadicIndexBox d H).card : ℝ) := by
    rw [card_triadicIndexBox H]
    positivity
  have hcH_ne : ((triadicIndexBox d H).card : ℝ) ≠ 0 := ne_of_gt hcH_pos
  calc
    (∫ a, (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
        ∑ W ∈ triadicIndexBox d (H + n),
          (Real.sqrt (vecDot Y.1 (matVecMul
                (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                  (b a)).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                  (b a)).lowerRight Y.2))) ^ 2 ∂P)
        = (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
            ∑ W ∈ triadicIndexBox d (H + n),
              ∫ a, (Real.sqrt (vecDot Y.1 (matVecMul
                    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                      (b a)).upperLeft Y.1))
                  + Real.sqrt (vecDot Y.2 (matVecMul
                    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                      (b a)).lowerRight Y.2))) ^ 2 ∂P := hLHS
    _ ≤ (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
            ∑ W ∈ triadicIndexBox d (H + n),
              (Real.sqrt (vecDot Y.1 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                      b).upperLeft Y.1))
                  + Real.sqrt (vecDot Y.2 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                      b).lowerRight Y.2))) ^ 2 :=
          mul_le_mul_of_nonneg_left hsum_bound hcHn_inv_nonneg
    _ = (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
            (∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
              (Real.sqrt (vecDot Y.1 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
                        (fun i => 3 ^ n * w i + z i)) b).upperLeft Y.1))
                  + Real.sqrt (vecDot Y.2 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
                        (fun i => 3 ^ n * w i + z i)) b).lowerRight Y.2))) ^ 2) := by
          rw [hreindex]
    _ = (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
            (∑ w ∈ triadicIndexBox d H, ∑ z ∈ triadicIndexBox d n,
              (Real.sqrt (vecDot Y.1 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                      b).upperLeft Y.1))
                  + Real.sqrt (vecDot Y.2 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                      b).lowerRight Y.2))) ^ 2) := by
          rw [hdesc_sum]
    _ = (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ *
            (((triadicIndexBox d H).card : ℝ) *
              ∑ z ∈ triadicIndexBox d n,
                (Real.sqrt (vecDot Y.1 (matVecMul
                      (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                        b).upperLeft Y.1))
                    + Real.sqrt (vecDot Y.2 (matVecMul
                      (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                        b).lowerRight Y.2))) ^ 2) := by
          rw [hcollapse]
    _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ z ∈ triadicIndexBox d n,
              (Real.sqrt (vecDot Y.1 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                      b).upperLeft Y.1))
                  + Real.sqrt (vecDot Y.2 (matVecMul
                    (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                      b).lowerRight Y.2))) ^ 2 := by
          rw [hcard, mul_inv_rev, mul_assoc, inv_mul_cancel_left₀ hcH_ne]

/-- **The annealed flat average of the squared pairing head at descendant depth `n`.**  Step ζ of
the cutoff-mean row of `p.response.transfer` at depth `n`, minus sign: the annealed flat average
over the generation-`(s-n)` cells of the terminal cell of the squared pathwise head is at most the
depth-`n` layer of the source load. -/
theorem integral_avsum_sq_head_descendant_le_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (F : BlockMat d)
    (H n : ℕ) (s : ℤ) (hjs : (jStar : ℤ) ≤ s) (Y : BlockVec d)
    (hUL : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft Y.1)) P)
    (hLR : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight Y.2)) P)
    (hULe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft i k) P)
    (hLRe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight i k) P)
    (hmeas : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft i k) P)
    (hmeas' : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight i k) P)
    (hUL0 : ∀ W : Fin d → ℤ, ∀ a, 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft Y.1))
    (hLR0 : ∀ W : Fin d → ℤ, ∀ a, 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight Y.2))
    (hcross : ∀ W : Fin d → ℤ, Integrable (fun a =>
      Real.sqrt (vecDot Y.1 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
            (respCoeffMinus F a)).upperLeft Y.1))
        * Real.sqrt (vecDot Y.2 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
            (respCoeffMinus F a)).lowerRight Y.2))) P)
    (hsq : ∀ W : Fin d → ℤ, Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (respCoeffMinus F a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (respCoeffMinus F a)).lowerRight Y.2))) ^ 2) P) :
    (∫ a, (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d (H + n),
        (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffMinus F a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffMinus F a)).lowerRight Y.2))) ^ 2 ∂P)
      ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffMinus F)).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffMinus F)).lowerRight Y.2))) ^ 2 := by
  exact integral_avsum_sq_head_descendant_le_aux P jStar F (respCoeffMinus F) H n s Y
    hUL hLR hULe hLRe hUL0 hLR0 hcross hsq (fun w z =>
      annealedBlockOf_descendant_respCoeffMinus_eq P hstat jStar (explicitCanonicalMetric F) F s hjs
        n w z (hmeas z) (hmeas' z))

/-- **The annealed flat average of the squared pairing head at descendant depth `n`, plus
sign.**  The adjoint twin of `integral_avsum_sq_head_descendant_le_respCoeffMinus`, for the
recentred family `a_+ = a^t + g`. -/
theorem integral_avsum_sq_head_descendant_le_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (F : BlockMat d)
    (H n : ℕ) (s : ℤ) (hjs : (jStar : ℤ) ≤ s) (Y : BlockVec d)
    (hUL : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft Y.1)) P)
    (hLR : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight Y.2)) P)
    (hULe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft i k) P)
    (hLRe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight i k) P)
    (hmeas : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft i k) P)
    (hmeas' : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight i k) P)
    (hUL0 : ∀ W : Fin d → ℤ, ∀ a, 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft Y.1))
    (hLR0 : ∀ W : Fin d → ℤ, ∀ a, 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight Y.2))
    (hcross : ∀ W : Fin d → ℤ, Integrable (fun a =>
      Real.sqrt (vecDot Y.1 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
            (respCoeffPlus F a)).upperLeft Y.1))
        * Real.sqrt (vecDot Y.2 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
            (respCoeffPlus F a)).lowerRight Y.2))) P)
    (hsq : ∀ W : Fin d → ℤ, Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (respCoeffPlus F a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
              (respCoeffPlus F a)).lowerRight Y.2))) ^ 2) P) :
    (∫ a, (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d (H + n),
        (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffPlus F a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffPlus F a)).lowerRight Y.2))) ^ 2 ∂P)
      ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffPlus F)).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffPlus F)).lowerRight Y.2))) ^ 2 := by
  exact integral_avsum_sq_head_descendant_le_aux P jStar F (respCoeffPlus F) H n s Y
    hUL hLR hULe hLRe hUL0 hLR0 hcross hsq (fun w z =>
      annealedBlockOf_descendant_respCoeffPlus_eq P hstat jStar (explicitCanonicalMetric F) F s hjs
        n w z (hmeas z) (hmeas' z))

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The annealed head of one descendant generation at the carriers

The descendant sum of `p.response.transfer` reads the generation-`n` layer of the source load
`𝓛_s` against the expectation of the flat average, over the depth-`(H+n)` aligned cells of the
terminal cell, of the squared pathwise two-term head
`(⟨Y₁, 𝐛_V Y₁⟩^{1/2} + ⟨Y₂, σ_{*,V}^{-1} Y₂⟩^{1/2})²`.  `DescendantHeadBound` proves that bound
from nine analytic side conditions on the pathwise coarse blocks.  This module discharges all nine
at the carriers, from the coarse-block integrability of the sample on every aligned cell of the
response grid and the nonnegativity of the two diagonal forms, so that the head bound carries no
analytic side condition.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The annealed head of a descendant generation is at most the corresponding layer of the
source load, minus sign, at the carriers.**  The expectation of the flat average over the
depth-`(H+n)` aligned cells of the squared pathwise two-term head of `a_- = a - g` is at most the
flat average over the generation-`n` cells of the squared annealed two-term head, i.e. the
generation-`n` layer of `𝓛_s^-` of `p.response.transfer`. -/
theorem integral_avsum_sq_head_descendant_le_respCoeffMinus_car {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hstat : IsStationaryLaw P) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
    (Src : CoeffSpace d → ℝ) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H n : ℕ) (s : ℤ) (hjs : (jStar : ℤ) ≤ s)
    (Y : BlockVec d) :
    (∫ a, (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d (H + n),
        (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffMinus F a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffMinus F a)).lowerRight Y.2))) ^ 2 ∂P)
      ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffMinus F)).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffMinus F)).lowerRight Y.2))) ^ 2 := by
  have hblk : ∀ W : Fin d → ℤ, HasIntegrableCoarseBlock P
      (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W) :=
    fun W => hasIntegrableCoarseBlock_adaptedCellAtCenter_respGrid hd P γ E Ψ Kg Src hstat hdag
      jStar
      hjStar F hm (s - (n : ℤ)) W
  have hULe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft i k) P :=
    fun W => integrable_coarseBlockMatrix_upperLeft_respCoeffMinus P jStar hjStar F hm
      (s - (n : ℤ)) W (hblk W)
  have hLRe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight i k) P :=
    fun W => integrable_coarseBlockMatrix_lowerRight_respCoeffMinus P jStar hjStar F hm
      (s - (n : ℤ)) W (hblk W)
  have hmeas : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft i k) P :=
    fun W i k => (hULe W i k).aestronglyMeasurable
  have hmeas' : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight i k) P :=
    fun W i k => (hLRe W i k).aestronglyMeasurable
  have hUL0 : ∀ (W : Fin d → ℤ) (a : CoeffSpace d), 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft Y.1) :=
    fun W a => (zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter jStar hjStar
      F hm
      (s - (n : ℤ)) a Y W).1
  have hLR0 : ∀ (W : Fin d → ℤ) (a : CoeffSpace d), 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight Y.2) :=
    fun W a => (zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter jStar hjStar
      F hm
      (s - (n : ℤ)) a Y W).2
  have hUL : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft Y.1)) P :=
    fun W => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft) Y.1 (hULe W)
  have hLR : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight Y.2)) P :=
    fun W => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight) Y.2 (hLRe W)
  exact integral_avsum_sq_head_descendant_le_respCoeffMinus P hstat jStar F H n s hjs Y
    hUL hLR hULe hLRe hmeas hmeas' hUL0 hLR0
    (fun W => integrable_sqrt_mul_sqrt_gen (hUL0 W) (hLR0 W) (hUL W) (hLR W))
    (fun W => integrable_sq_sqrt_add_sqrt_gen (hUL0 W) (hLR0 W) (hUL W) (hLR W))

/-- **The annealed head of a descendant generation is at most the corresponding layer of the
source load, plus sign, at the carriers.**  The expectation of the flat average over the
depth-`(H+n)` aligned cells of the squared pathwise two-term head of `a_- = a - g` is at most the
flat average over the generation-`n` cells of the squared annealed two-term head, i.e. the
generation-`n` layer of `𝓛_s^-` of `p.response.transfer`. -/
theorem integral_avsum_sq_head_descendant_le_respCoeffPlus_car {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hstat : IsStationaryLaw P) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
    (Src : CoeffSpace d → ℝ) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H n : ℕ) (s : ℤ) (hjs : (jStar : ℤ) ≤ s)
    (Y : BlockVec d) :
    (∫ a, (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d (H + n),
        (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffPlus F a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffPlus F a)).lowerRight Y.2))) ^ 2 ∂P)
      ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffPlus F)).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffPlus F)).lowerRight Y.2))) ^ 2 := by
  have hblk : ∀ W : Fin d → ℤ, HasIntegrableCoarseBlock P
      (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W) :=
    fun W => hasIntegrableCoarseBlock_adaptedCellAtCenter_respGrid hd P γ E Ψ Kg Src hstat hdag
      jStar
      hjStar F hm (s - (n : ℤ)) W
  have hULe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft i k) P :=
    fun W => integrable_coarseBlockMatrix_upperLeft_respCoeffPlus P jStar hjStar F hm
      (s - (n : ℤ)) W (hblk W)
  have hLRe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight i k) P :=
    fun W => integrable_coarseBlockMatrix_lowerRight_respCoeffPlus P jStar hjStar F hm
      (s - (n : ℤ)) W (hblk W)
  have hmeas : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft i k) P :=
    fun W i k => (hULe W i k).aestronglyMeasurable
  have hmeas' : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight i k) P :=
    fun W i k => (hLRe W i k).aestronglyMeasurable
  have hUL0 : ∀ (W : Fin d → ℤ) (a : CoeffSpace d), 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft Y.1) :=
    fun W a => (zero_le_vecDot_coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm
      (s - (n : ℤ)) a Y W).1
  have hLR0 : ∀ (W : Fin d → ℤ) (a : CoeffSpace d), 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight Y.2) :=
    fun W a => (zero_le_vecDot_coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm
      (s - (n : ℤ)) a Y W).2
  have hUL : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft Y.1)) P :=
    fun W => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft) Y.1 (hULe W)
  have hLR : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight Y.2)) P :=
    fun W => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight) Y.2 (hLRe W)
  exact integral_avsum_sq_head_descendant_le_respCoeffPlus P hstat jStar F H n s hjs Y
    hUL hLR hULe hLRe hmeas hmeas' hUL0 hLR0
    (fun W => integrable_sqrt_mul_sqrt_gen (hUL0 W) (hLR0 W) (hUL W) (hLR W))
    (fun W => integrable_sq_sqrt_add_sqrt_gen (hUL0 W) (hLR0 W) (hUL W) (hLR W))

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Integrability of the cutoff integrands of the pathwise expansion of `p.response.transfer`

The pathwise expansion of the cutoff pairing in the cutoff estimate of `p.response.transfer`
needs six scalar integrands to be integrable on the terminal cell.  All six are products of the
bounded cutoff `φ` with either a coordinate of the doubled optimizer state `X = (∇v, b ∇v)`, a
coordinate pairing of `X` with a constant vector, or the pairing `X₁·X₂`.  On a set of finite
volume, with both slots of `X` square integrable and `0 ≤ φ ≤ 2`, the bounded-measurable-factor
lemma gives the first three, and the `L² × L² → L¹` Hölder pairing gives the last.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A measurable function bounded by `Mφ` in absolute value, multiplied by an integrable
function, is integrable on any set.  The pointwise bound `|φ x| ≤ Mφ` supplies the
almost-everywhere norm bound required by `Integrable.bdd_mul`. -/
theorem integrableOn_cutoff_mul_coord {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    (hUfin : volume U ≠ ⊤) {φ : Vec d → ℝ} (hφm : Measurable φ) {Mφ : ℝ}
    (hφb : ∀ x, |φ x| ≤ Mφ) {g : Vec d → ℝ} (hg : IntegrableOn g U) :
    IntegrableOn (fun x => φ x * g x) U := by
  have hU_used : MeasurableSet U := hU
  have hUfin_used : volume U ≠ ⊤ := hUfin
  exact Integrable.bdd_mul hg hφm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact hφb x)

end

end HCPolySupport.HighContrast.Multiscale
end
