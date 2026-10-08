/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.CoarseBlockPerCellInput
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentHeadDefectHalves
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentScaleEnergyRoute

/-!
# High-contrast homogenization: Entry.Response.Kernel.DiagonalWeakNormAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Assembly of the diagonal weak-norm estimate

This file assembles the diagonal weak-norm estimate of the response-transfer proposition
`p.response.transfer` from its two halves, the `weakCellSum` and `weakAverageSum` bounds, adding
the hypothesis pair the underlying statement omitted and recording the resulting bound at the
estimate's own carriers. Alongside it sit the adjoint twin of the averaged-defect window sum,
sharing the good-branch coefficient `√2 (1 + √M · 3^(ρn/2))`; the recent-scale decomposition
restricted to the depth-`n` triadic index box and its window sum; and the coincidence, for the
adjoint response, of the normalized block's one-sided spectral bound with its operator norm at a
positive definite pair.
-/

section
/-!
## The averaged-defect window sum for the adjoint sample

This is the plus twin of the averaged-defect window sum `weakAverageSum_half_le`.  The
per-scale bound on the abstract family `A : ℕ → ℝ` is the same good-branch coefficient
`√2 (1 + √M · 3^{ρ n/2})`, and the window summation is the same arithmetic on the geometric
weights `3^{-n/2}` and `3^{-(1/2 - ρ/2)n}`.  The only change is the sample: the recentred field
`a_- = respCoeffMinus F a` and the response matrix `E_-^t = respEhatMinus P jStar F t` are
replaced by their adjoint counterparts `a_+ = respCoeffPlus F a` and
`E_+^t = respEhatPlus P jStar F t`.  This is the averaged-defect summand of the weak-norm
estimate `e.response.weak.estimate`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **`e.response.weak.estimate`, averaged-defect window sum for the adjoint sample.**  For the
adjoint sample `a_+ = respCoeffPlus F a`, the adjoint response matrix
`E_+^t = respEhatPlus P jStar F t`, and a family `A : ℕ → ℝ` bounded per scale by the
good-branch coefficient `√2 (1 + √M · 3^{ρ n/2})` against the averaged recent-defect size
`‖weakAverageDefect · E_+^t · a_+‖`, the `3^{-n/2}`-weighted sum over the window `n ≤ H` is
bounded by `4 K L` times the printed weighted averaged-defect sum
`∑ 3^{-(1/2 - ρ/2)n} ‖weakAverageDefect · E_+^t · a_+‖`.

`M = respAllScaleMax P γ jStar F t a` is assumed at most `1` (the nondegenerate branch), `K` and
`L` are nonnegative, and `_hE` records that the adjoint response matrix `E_+^t` is positive
definite; the latter is the nondegeneracy condition carried by the route. -/
theorem weakAverageSum_half_le_plus (P : Measure (CoeffSpace d)) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d)
    {K L : ℝ} (hK0 : 0 ≤ K) (hL0 : 0 ≤ L) (A : ℕ → ℝ)
    (_hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1)
    (hscale : ∀ n : ℕ, A n ≤
      Real.sqrt 2 * K *
        (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
          (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) * L *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatPlus P jStar F t) (respCoeffPlus F a))‖) :
    ∑ n ∈ Finset.range (H + 1), (3 : ℝ) ^ (-((n : ℝ) / 2)) * A n ≤
      4 * K * L *
        weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatPlus P jStar F t)
          (respCoeffPlus F a) := by
  have hrho0 : 0 ≤ Quenched.contrastRho γ := (respRho_pos hγ).le
  refine weakAverageSum_window_le (K := 4 * K) (L := L) _ t H (Quenched.contrastRho γ) _ _
    (fun n => (3 : ℝ) ^ (-((n : ℝ) / 2)) * A n) ?_
  intro n _
  set M : ℝ := respAllScaleMax P γ jStar F t a with hM
  set R : ℝ := (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2) with hR
  set W : ℝ := (3 : ℝ) ^ (-((n : ℝ) / 2)) with hW
  set D : ℝ := Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
    (respEhatPlus P jStar F t) (respCoeffPlus F a))‖ with hD
  have hR1 : (1 : ℝ) ≤ R := one_le_recentWeight hrho0 n
  have hW0 : (0 : ℝ) ≤ W := Real.rpow_nonneg (by norm_num) _
  have hD0 : (0 : ℝ) ≤ D := Real.sqrt_nonneg _
  have hrest0 : (0 : ℝ) ≤ K * L * D := mul_nonneg (mul_nonneg hK0 hL0) hD0
  have hcoeff : Real.sqrt 2 * (1 + Real.sqrt M * R) ≤ 4 * R := avCoeff_le hgood hR1
  have hstep : A n ≤ (4 * R) * (K * L * D) := by
    refine (hscale n).trans ?_
    calc
      Real.sqrt 2 * K * (1 + Real.sqrt M * R) * L * D
          = (Real.sqrt 2 * (1 + Real.sqrt M * R)) * (K * L * D) := by ring
      _ ≤ (4 * R) * (K * L * D) := mul_le_mul_of_nonneg_right hcoeff hrest0
  calc
    W * A n ≤ W * ((4 * R) * (K * L * D)) := mul_le_mul_of_nonneg_left hstep hW0
    _ = 4 * K * L * ((W * R) * D) := by ring
    _ = 4 * K * L * ((3 : ℝ) ^ (-((1 / 2 : ℝ) - Quenched.contrastRho γ / 2) * (n : ℝ)) * D) := by
        rw [hW, hR, recentWeight_mul]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The recent-scale decomposition with box-restricted integrability

The recent-scale decomposition compares the normalized root-mean-square, over the depth-`n`
triadic cells, of the transported and recentred parent cell averages with the corresponding child
average plus the average of the parent-minus-child difference.  Its conclusion sums only over the
cells indexed by `triadicIndexBox d n`, and its window sum only over `n ≤ H`, so the
integrability of the fields is needed only on those cells: a cell index outside the box is never
averaged.

This module restates the decomposition with that restricted hypothesis, which is the form the
optimizer field can actually supply, since the parent field is `L²` only on the adapted region
`U`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The recent-scale decomposition at one depth, with box-restricted integrability.**  At depth
`n`, the head term of the actual family — the normalized root-mean-square over the triadic cells
of the transported, recentred parent cell averages — is at most the corresponding child term plus
the average-defect term, assuming the componentwise integrability of the parent and child fields
only on the triadic cells indexed by `triadicIndexBox d n`. -/
theorem recent_scaleDecomposition_box_le (q : Mat d) (t : ℤ) (n : ℕ) (R : BlockMat d)
    (Xu : Vec d → BlockVec d) (Xv : (Fin d → ℤ) → Vec d → BlockVec d) (c : BlockVec d)
    (h1u : ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xu x).1 j) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h2u : ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xu x).2 j) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h1v : ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xv w x).1 j) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h2v : ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xv w x).2 j) (adaptedCellAtCenter q (t - (n : ℤ)) w)) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Xu - c))
            (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Xu - c)))
      ≤ Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Xv w) - c))
                (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Xv w) - c)))
        + Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                  (fun x => Xu x - Xv w x)))
                (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                  (fun x => Xu x - Xv w x)))) := by
  classical
  set C : (Fin d → ℤ) → BlockVec d := fun w =>
    blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Xv w) - c) with hC
  set D : (Fin d → ℤ) → BlockVec d := fun w =>
    blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
      (fun x => Xu x - Xv w x)) with hD
  have hsplit : ∀ w ∈ triadicIndexBox d n,
      blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Xu - c) = C w + D w :=
    fun w hw => recentCell_split R Xu (Xv w) c
      (h1u w hw) (h2u w hw) (h1v w hw) (h2v w hw)
  have hrw : ∑ w ∈ triadicIndexBox d n,
      blockVecDot
        (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Xu - c))
        (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Xu - c))
      = ∑ w ∈ triadicIndexBox d n, blockVecDot (C w + D w) (C w + D w) :=
    Finset.sum_congr rfl fun w hw => congrArg₂ blockVecDot (hsplit w hw) (hsplit w hw)
  rw [hrw]
  exact normalized_blockL2_add_le (triadicIndexBox d n) C D

omit [NeZero d] in
/-- **The recent-scale decomposition summed over the window, with box-restricted integrability.**
The depth-`n` decomposition summed over `n ≤ H` against the `3^{-n/2}` weights, assuming the
componentwise integrability of the parent and child fields only on the triadic cells indexed by
`triadicIndexBox d n` for each `n` in the window. -/
theorem recentHead_scaleDecomposition_box_le (q : Mat d) (t : ℤ) (H : ℕ) (R : BlockMat d)
    (Xu : Vec d → BlockVec d) (Xv : ℕ → (Fin d → ℤ) → Vec d → BlockVec d) (c : BlockVec d)
    (h1u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xu x).1 j) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h2u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xu x).2 j) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h1v : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xv n w x).1 j) (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (h2v : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (Xv n w x).2 j) (adaptedCellAtCenter q (t - (n : ℤ)) w)) :
    ∑ n ∈ Finset.range (H + 1),
        (3 : ℝ) ^ (-((n : ℝ) / 2)) *
          Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Xu - c))
                (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) Xu - c)))
      ≤ ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            (Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul R
                      (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Xv n w) - c))
                    (blockMatVecMul R
                      (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (Xv n w) - c)))
              + Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                  ∑ w ∈ triadicIndexBox d n,
                    blockVecDot
                      (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                        (fun x => Xu x - Xv n w x)))
                      (blockMatVecMul R (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                        (fun x => Xu x - Xv n w x))))) := by
  refine Finset.sum_le_sum fun n hn => ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
  exact recent_scaleDecomposition_box_le q t n R Xu (Xv n) c
    (h1u n hn) (h2u n hn) (h1v n hn) (h2v n hn)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Assembly of the diagonal weak norm estimate

This file assembles the estimate `diagonalWeakNorm_primal_le`
(`DiagonalWeakNormBound.lean`) from its two halves.  It adds declarations only and restates
or weakens none of them.

## What this file is for

The statement omitted the hypothesis pair `(hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)`
that the printed argument carries at the route's energy estimate.  Here the surviving gap is
exactly `(toFullBlockMat (respEhatMinus P jStar F t)).PosDef`, and that gap is dischargeable,
as established in `RecentHeadDefectHalves.lean`, from `RespCalibrated` together with
`RawOutput.symm` and `RawOutput.pos`.  This file chains those discharges into the context of
`diagonalWeakNorm_primal_le` rather than leaving them standing alone.

The results fall into three groups.

* The first concerns the maximum: the real-valued `respAllScaleMax` (`ResponseBlockObjects.lean`)
is a
  bare `sSup`, which on an unbounded set takes Lean's junk value `0`; an explicit finiteness
  hypothesis `hfinite : diagonalWeakMaximum … ≠ ⊤` excludes that.  An envelope constant —
  precisely what `pathwise_envelope` (`WeakEstimateAssembly.lean`) delivers almost
  everywhere — makes the defining set `BddAbove`, and the membership inequality that `hfinite`
  was there to license follows.
* The second concerns the mismatch between the two spectral quantities: the `weakCellSum` half
  concludes against `√‖toFullBlockMat (normalizedBlock Ê M₀)‖`, whereas the statement prints
  `√(blockSpecBound (normalizedBlock Ê M₀))`, and `blockSpecBound N ≤ ‖toFullBlockMat N‖` is the
  wrong direction.  Under the positive-definiteness condition the two are equal, because
  `normalizedBlock Ê M₀` is then positive definite, so the half can be restated on the printed
  quantity without touching the statement.
* The third composes the two halves into the printed first summand and reduces the remaining
  hypothesis to the two analytic facts on which it rests, recording what is still missing.

Every statement is proved here, on the carriers of this library.  The positive-definiteness of
the normalized block is supplied by `Annealed.normalizedBlock_posDef`
(`HCPoly/Entry/Annealed/Normalization.lean`), and the boundedness result rests on the finite-maximum
branch of the real-valued maximum.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub coarseBlock normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The positive-definiteness condition at the route's own binder bundle. -/

/-! ## The boundedness of the real-valued maximum. -/

omit [NeZero d] in
/-- The boundedness.  An envelope constant bounding every weighted spectral excess makes the
defining set of `respAllScaleMax` (`ResponseBlockObjects.lean`) bounded above.  The hypothesis holds
almost everywhere: it is the third component of `pathwise_envelope`
(`WeakEstimateAssembly.lean`).  This is the content, on a real-valued carrier, of the
finiteness hypothesis `hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤` that an earlier statement
carried: without it `sSup` takes the junk value `0`. -/
theorem respAllScaleMax_bddAbove_of_envelope (P : Measure (CoeffSpace d)) (γ : ℝ)
    (jStar : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d) {C : ℝ}
    (hterms : ∀ n : ℕ, ∀ z ∈ triadicIndexBox d n,
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        blockSpecBound (blockSub (normalizedBlock (coarseBlock
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a) (respMean P jStar F t))
          (Book.Ch02.blockIdentity d)) ≤ C) :
    BddAbove {y : ℝ | ∃ n : ℕ, ∃ z ∈ triadicIndexBox d n, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))} := by
  refine ⟨C, ?_⟩
  rintro y ⟨n, z, hz, rfl⟩
  exact hterms n z hz

/-! ## The `weakCellSum` half, on the quantity the printed statement uses. -/

omit [NeZero d] in
/-- The key equality.  On positive definite `N` and `M` the spectral positive part of
`normalizedBlock N M` is all of `normalizedBlock N M`, so the two quantities
`blockSpecBound (normalizedBlock Ê M₀)` and `‖toFullBlockMat (normalizedBlock Ê M₀)‖` coincide.
`Annealed.normalizedBlock_posDef` is `HCPoly/Entry/Annealed/Normalization.lean`; the hard half of
the
equality is `blockSpecBound_eq_norm_of_posSemidef`
(`RecentEnergyMapSupport.lean`). -/
theorem blockSpecBound_normalizedBlock_eq_norm (N M : BlockMat d)
    (hN : (toFullBlockMat N).PosDef) (hM : (toFullBlockMat M).PosDef) :
    blockSpecBound (normalizedBlock N M) = ‖toFullBlockMat (normalizedBlock N M)‖ :=
  blockSpecBound_eq_norm_of_posSemidef _
    (Annealed.normalizedBlock_posDef N M hN hM).posSemidef

omit [NeZero d] in
/-- The metric factor.  The same equality at the carriers of `diagonalWeakNorm_primal_le`: the
`K₀` of `p.response.transfer` as it is printed equals the `K₀` used by the `weakCellSum` half. -/
theorem respK0_specBound_eq_norm (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef) :
    blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)) =
      ‖toFullBlockMat (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖ :=
  blockSpecBound_normalizedBlock_eq_norm _ _ hE hM0

/-- The `weakCellSum` half on the printed quantity.  `weakCellSum_half_le`
(`RecentHeadDefectHalves.lean`) with its conclusion moved from the two-sided
operator norm to the one-sided `blockSpecBound` used in `DiagonalWeakNormBound.lean`.  The
statement of `diagonalWeakNorm_primal_le` is untouched; the change is licensed exactly by the
positive-definiteness condition, which is discharged above.  Constant `1` against the printed
`16`. -/
theorem weakCellSum_half_specBound_le
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (H : ℕ)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u)
    (hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a),
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffMinus F a) u))))
        ≤ Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqMinus P jStar F t e) *
            weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
              (respCoeffMinus F a) := by
  obtain ⟨V, hV⟩ := weakCellSum_half_le P jStar F t e hgrid a H u hu hE
  exact ⟨V, by rwa [respK0_specBound_eq_norm P jStar F t hE hM0]⟩

/-! ## Composition of the two halves into the first printed summand. -/

/-- The composition of the two halves, with the child-maximizer family produced before the
per-scale family.  The earlier composition statement binds the per-scale family `A` and its
constraint `hscale` before producing the child-maximizer family `V`.  The recent-scale
decomposition of the head term into the child term plus the average-defect family exhibits the
intended `A` — the average-defect family — and that family depends on `V`, so it cannot be
supplied to that statement at all: the `∃ V` is under the `∀ A`.

This declaration is that statement with `∃ V` moved outside `∀ A`.  It is strictly stronger than
the earlier statement (the same `V` now serves every `A`), nothing is weakened, and the proof is
the earlier statement's own, since it already obtains `V` from the `weakCellSum` half
independently of `A`. -/
theorem recentHead_halves_forall_le
    (P : Measure (CoeffSpace d)) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u)
    (hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a),
      ∀ A : ℕ → ℝ,
    (hscale : ∀ n : ℕ, A n ≤
      Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) *
          Real.sqrt (respLsqMinus P jStar F t e) *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatMinus P jStar F t) (respCoeffMinus F a))‖) →
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) * (Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffMinus F a) u)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffMinus F a) u)))) + A n)
        ≤ 16 *
            Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqMinus P jStar F t e) *
            (weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
                (respCoeffMinus F a) +
              weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatMinus P
                jStar F t)
                (respCoeffMinus F a)) := by
  classical
  set K : ℝ :=
    Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) with hK
  set L : ℝ := Real.sqrt (respLsqMinus P jStar F t e) with hL
  have hK0 : (0 : ℝ) ≤ K := Real.sqrt_nonneg _
  have hL0 : (0 : ℝ) ≤ L := Real.sqrt_nonneg _
  obtain ⟨V, hV⟩ := weakCellSum_half_specBound_le P jStar F t e hgrid a H u hu hE hM0
  refine ⟨V, fun A hscale => ?_⟩
  have hav := weakAverageSum_half_le (K := K) (L := L) P γ hγ jStar H F t a hK0 hL0 A hE
    hgood hscale
  have hcs0 : (0 : ℝ) ≤ weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
      (respCoeffMinus F a) := weakCellSum_nonneg _ _ _ _ _
  have has0 : (0 : ℝ) ≤ weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ)
      (respEhatMinus P jStar F t) (respCoeffMinus F a) := weakAverageSum_nonneg _ _ _ _ _ _
  have hsplit : ∀ n ∈ Finset.range (H + 1),
      (3 : ℝ) ^ (-((n : ℝ) / 2)) * (Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffMinus F a) u)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffMinus F a) u)))) + A n)
        = (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffMinus F a) u)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffMinus F a) u))))
          + (3 : ℝ) ^ (-((n : ℝ) / 2)) * A n := fun n _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  refine (add_le_add hV hav).trans ?_
  have hKLc : 0 ≤ K * L * weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
      (respCoeffMinus F a) := mul_nonneg (mul_nonneg hK0 hL0) hcs0
  have hKLa : 0 ≤ K * L * weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ)
      (respEhatMinus P jStar F t) (respCoeffMinus F a) := mul_nonneg (mul_nonneg hK0 hL0) has0
  linarith only [hK, hL, hKLc, hKLa]

/-- The composition of the recent-scale decomposition with the preceding result: the head of the
left-hand side built from the actual parent optimizer `u` — the field supplied by
`h6a_besovSeminorm_recentred_eq` and `h6a_besovSeminorm_head_tail_le`
(`RecentEnergyMapSupport.lean`) — is bounded by the entire first printed
summand `16 K₀ L⁻ (weakCellSum + weakAverageSum)`.

The earlier composition statement bounded a sum over the child maximizers plus an abstract `A`;
here the child maximizers are gone from the left-hand side and `A` is no longer abstract — it is
the explicit average-defect family, produced by the recent-scale decomposition together with `V`.

The only thing still assumed is `hscale`, now asked of that explicit family rather than of an
abstract one.  This is precisely the analytic recent-average bound on the average-defect family,
which is not proved anywhere here.  The integrability side conditions are the same ones the
recent-scale support lemmas already carry. -/
theorem recentHead_actual_le
    (P : Measure (CoeffSpace d)) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u)
    (hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1)
    (h1u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).1 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w))
    (h2u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).2 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a),
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffMinus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).1 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffMinus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).2 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n : ℕ, Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (fun x => optimizerField (respCoeffMinus F a) u x -
                          optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (fun x => optimizerField (respCoeffMinus F a) u x -
                          optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))) ≤
      Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) *
          Real.sqrt (respLsqMinus P jStar F t e) *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatMinus P jStar F t) (respCoeffMinus F a))‖) →
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffMinus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffMinus F a) u))))
        ≤ 16 *
            Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqMinus P jStar F t e) *
            (weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
                (respCoeffMinus F a) +
              weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatMinus P
                jStar F t)
                (respCoeffMinus F a)) := by
  classical
  obtain ⟨V, hV⟩ := recentHead_halves_forall_le P γ hγ jStar H F t e hgrid a u hu hE hM0 hgood
  refine ⟨V, fun h1v h2v hscale => ?_⟩
  refine le_trans ?_ (hV _ hscale)
  exact recentHead_scaleDecomposition_box_le (respGrid jStar F) t H (blockSqrt (respM0 F))
    (optimizerField (respCoeffMinus F a) u)
    (fun n w => optimizerField (respCoeffMinus F a)
      ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction))
    (cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u))
    h1u h2u h1v h2v

/-- The composition of the preceding result with its remaining hypothesis replaced by the two
analytic facts it rests on.  Its single remaining hypothesis `hscale` is replaced by a per-depth
per-cell energy family `G` satisfying:

* `hcell`: the recent-difference metric-norm-squared bound, composed with the all-scale-maximum
  response bound; and
* `henergy`: the recent-difference energy bound.

The reduction is `scaleInput_of_analytic` (`CoarseBlockPerCellInput.lean`).
Neither analytic fact is proved here: their root `energy_map_metric_le`
(`…/Provider/Response/EnergyMap.lean`) rests on a doubled-response / `blockSharp` sublayer
absent from both `HCPoly/Entry/` and the `CoarseGraining` dependency.  What this result
establishes is that
nothing else is missing between them and the entire first printed summand.

A side hypothesis `hLsq : 0 ≤ respLsqMinus …` is not needed: it is exactly the nonnegativity of
the quadratic form of the positive-definite `respEhatMinus` at `respxMinus`, supplied from `hE` by
`blockVecDot_nonneg_of_posSemidef` (`RecentScaleEnergyRoute.lean`).  Dropping a
hypothesis is a strengthening; nothing in the conclusion moved. -/
theorem recentHead_actual_of_analytic
    (P : Measure (CoeffSpace d)) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u)
    (hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1)
    (h1u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).1 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w))
    (h2u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).2 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a),
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffMinus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).1 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffMinus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).2 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n : ℕ, ∃ G : (Fin d → ℤ) → ℝ,
        (∀ w ∈ triadicIndexBox d n,
          blockVecDot
              (blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (fun x => optimizerField (respCoeffMinus F a) u x -
                    optimizerField (respCoeffMinus F a)
                      ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))
              (blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (fun x => optimizerField (respCoeffMinus F a) u x -
                    optimizerField (respCoeffMinus F a)
                      ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))
            ≤ (Real.sqrt
                  (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
                * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                    * (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2))) ^ 2 * G w) ∧
        ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n, G w
          ≤ 2 * respLsqMinus P jStar F t e
              * ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
                  (respEhatMinus P jStar F t) (respCoeffMinus F a))‖) →
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffMinus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffMinus F a) u))))
        ≤ 16 *
            Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqMinus P jStar F t e) *
            (weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
                (respCoeffMinus F a) +
              weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatMinus P
                jStar F t)
                (respCoeffMinus F a)) := by
  classical
  -- The former hypothesis `hLsq`, discharged from `hE`.
  have hLsq : 0 ≤ respLsqMinus P jStar F t e := by
    rw [respLsqMinus]
    exact blockVecDot_nonneg_of_posSemidef _ hE.posSemidef _
  obtain ⟨V, hV⟩ := recentHead_actual_le P γ hγ jStar H F t e hgrid a u hu hE hM0 hgood h1u h2u
  refine ⟨V, fun h1v h2v hin => hV h1v h2v (fun n => ?_)⟩
  obtain ⟨G, hcell, henergy⟩ := hin n
  exact scaleInput_of_analytic P γ jStar F t e a n
    (fun w x => optimizerField (respCoeffMinus F a) u x -
      optimizerField (respCoeffMinus F a)
        ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)
    G hLsq hcell henergy

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The metric factor of the normalized response block, adjoint sign

For a positive definite numerator and a positive definite normalizer, the spectral positive
part of the normalized block is the whole matrix, so its one-sided spectral bound coincides
with its operator norm.  This file records that coincidence for the adjoint response
`respEhatPlus`, the sign that is paired with `respxPlus` in the weak-norm estimate: the
metric factor printed there equals the one delivered by the cell-sum half.
-/

open HCPolySupport.HighContrast (CoeffSpace normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The spectral bound of the `respEhatPlus`-normalized response block equals its operator
norm, because both `respEhatPlus P jStar F t` and the normalizer `respM0 F` are positive
definite. -/
theorem respK0_specBound_eq_norm_plus (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef) :
    blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)) =
      ‖toFullBlockMat (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖ :=
  blockSpecBound_normalizedBlock_eq_norm _ _ hE hM0

end

end HCPolySupport.HighContrast.Multiscale
end
