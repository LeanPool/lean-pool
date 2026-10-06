/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AnnealedBlockOrder
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CanonicalReadoutMeasurability
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.OptimizerEnergyIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentCellDefectBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.SourceLoadHeadBound
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra

/-!
# High-contrast homogenization: Entry.Response.Rows.StationaryAnnealedErrorScalars

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Stationarity of the Annealed Block and the Cutoff Rows' Error Scalars

For a stationary law and a scale above the threshold `j_*`, every aligned cell of a generation is
an integer translate of the centred adapted cell; since the law is translation invariant, the two
diagonal sub-blocks of the annealed coarse block of `a_- = a - g` or `a_+ = a^T + g` are the same
matrix at every cell of the generation, and the annealed response of that family is likewise
independent of the aligned cell. Consequently the error scalars `respEJMinus`/`respTauMinus`,
each a Bochner integral of the pathwise response, and `respLsMinus`, a Bochner integral of a
coarse-block entry, are algebraic functions of the annealed recentred block under its entrywise
integrability. This file also identifies the annealed flat average of one descendant generation's
squared pathwise head, built from the two diagonal quadratic forms of that generation's own
coarse block, with the corresponding expression built from the single annealed block.  The
stationarity and these closed block forms are the ingredients consumed by the transfer step
`p.response.transfer`.
-/

section
/-!
## The annealed head of one descendant generation

The source load `L_s` of `p.response.transfer` is the sum over the descendant generations of
`3^{-3n/2}` times the flat average over that generation's cells of `(√α + √β)^2`, where `α` and `β`
are the two diagonal quadratic forms of the **annealed** coarse block of the cell.  The pairing of
the cutoff row produces instead the flat average of the same expression built from the **pathwise**
coarse blocks, followed by the expectation.  Moving the expectation inside a single generation is
the content here: for each cell the expectation of `(√α + √β)^2` is at most `(√E[α] + √E[β])^2`
by the sample Cauchy--Schwarz inequality, and the expectation of each pathwise coarse-block
quadratic form is the quadratic form of the annealed block.  Averaging over the cells of the
generation therefore recovers that generation's own summand of `L_s`, with the expectation on the
inside and no inversion and no Jensen step in the wrong direction.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The annealed head of one descendant generation.**  The flat cell average over the generation
of `3^{-3n/2}` subcells of `(√α + √β)^2` integrates to at most the corresponding flat average of
`(√E[α] + √E[β])^2`, where `α` and `β` are the upper-left and lower-right pathwise coarse-block
quadratic forms and the square roots on the right are taken of their annealed counterparts.  This is
the step that moves the expectation inside one generation's summand of the source load `L_s` of
`p.response.transfer`. -/
theorem integral_avsum_pathwise_head_le {d : ℕ} [NeZero d] (P : Measure (CoeffSpace d))
    (jStar : ℕ) (F : BlockMat d) (k : ℤ) (n : ℕ)
    (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (hUL : ∀ w ∈ triadicIndexBox d n, ∀ a : CoeffSpace d, 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
    (hLR : ∀ w ∈ triadicIndexBox d n, ∀ a : CoeffSpace d, 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2))
    (hentUL : ∀ w ∈ triadicIndexBox d n, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft i j) P)
    (hentLR : ∀ w ∈ triadicIndexBox d n, ∀ i j : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight i j) P)
    (hqUL : ∀ w ∈ triadicIndexBox d n, Integrable (fun a => vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1)) P)
    (hqLR : ∀ w ∈ triadicIndexBox d n, Integrable (fun a => vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2)) P)
    (hcross : ∀ w ∈ triadicIndexBox d n, Integrable (fun a =>
      Real.sqrt (vecDot Y.1 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
        * Real.sqrt (vecDot Y.2 (matVecMul
          (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2))) P)
    (hsq : ∀ w ∈ triadicIndexBox d n, Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2)))
        ^ 2) P) :
    (∫ a, ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
        (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2)))
          ^ 2 ∂P)
      ≤ ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k w) b).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k w) b).lowerRight Y.2)))
            ^ 2 := by
  have hc0 : 0 ≤ ((triadicIndexBox d n).card : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hstep : ∀ w ∈ triadicIndexBox d n,
      (∫ a, (Real.sqrt (vecDot Y.1 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
            (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2)))
          ^ 2 ∂P)
        ≤ (Real.sqrt (vecDot Y.1 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k w) b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k w) b).lowerRight Y.2)))
          ^ 2 := by
    intro w hw
    have hul := integral_vecDot_coarseBlock_upperLeft (P := P)
      (V := adaptedCellAtCenter (respGrid jStar F) k w) b Y.1 (hentUL w hw)
    have hlr := integral_vecDot_coarseBlock_lowerRight (P := P)
      (V := adaptedCellAtCenter (respGrid jStar F) k w) b Y.2 (hentLR w hw)
    have h := integral_sq_sqrt_add_sqrt_le P (hqUL w hw) (hqLR w hw) (hUL w hw)
      (hLR w hw) (hcross w hw) (hsq w hw)
    simp only [hul, hlr] at h
    exact h
  calc
    (∫ a, ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
        (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2)))
          ^ 2 ∂P)
      = ((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∫ a, ∑ w ∈ triadicIndexBox d n,
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2)))
              ^ 2 ∂P := integral_const_mul _ _
    _ = ((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            ∫ a, (Real.sqrt (vecDot Y.1 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                  (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) k w) (b a)).lowerRight Y.2)))
              ^ 2 ∂P := by
        rw [integral_finsetSum _ (fun w hw => hsq w hw)]
    _ ≤ ((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k w) b).upperLeft Y.1))
              + Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k w) b).lowerRight Y.2)))
              ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hc0

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The annealed-block form of the two error scalars of the cutoff rows

The cutoff rows of the response estimate bound the centred response by expressions in
`respEJMinus`, `respTauMinus` and `respLsMinus`.  The first two are Bochner integrals of the
pathwise response; under the entrywise integrability hypotheses the cutoff rows carry, both are
algebraic functions of the annealed recentred blocks.  This file records the two identities that
replace those integrals by the quadratic form of the annealed block.

The second identity is the underlying entrywise statement, `e.annealed.schur`: the quadratic form
of a doubled block commutes with the Bochner integral entrywise.  The first identity is then the
source form of the centred response energy `e.response.cutoff.estimate`: the pathwise response
`J(U_u, p, q'; b a)` is the block energy `x. A x / 2 - p. q'`, so its `P`-expectation is the
same block energy of the annealed block `E[A]`.
-/

open HCPolySupport.HighContrast (CoeffSpace blockVecDot_blockMatVecMul_eq_sum)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The quadratic form commutes with the annealed expectation.**  For any doubled vector `X`,
the `P`-integral of the pathwise quadratic form `X. (coarseBlockMatrix V (b a)) X` equals the
quadratic form of the entrywise annealed block `annealedBlockOf P V b`, whenever every entry of
the pathwise block is `P`-integrable.  This is the entrywise expectation identity `E[A]` of
`e.annealed.schur`. -/
theorem integral_blockVecDot_blockMatVecMul_coarseBlockMatrix {d : ℕ}
    (P : Measure (CoeffSpace d)) (V : Set (Vec d)) (b : CoeffSpace d → CoeffField d)
    (X : BlockVec d)
    (hint : ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlockMatrix V (b a)) α β) P) :
    (∫ a, blockVecDot X (blockMatVecMul (coarseBlockMatrix V (b a)) X) ∂P)
      = blockVecDot X (blockMatVecMul (annealedBlockOf P V b) X) := by
  have hentry : ∀ α β : BlockCoord d,
      blockMatEntry (annealedBlockOf P V b) α β
        = ∫ a, blockMatEntry (coarseBlockMatrix V (b a)) α β ∂P := by
    intro α β
    cases α <;> cases β <;> rfl
  have hterm : ∀ α β : BlockCoord d, Integrable (fun a =>
      toFullBlockVec X α *
        (blockMatEntry (coarseBlockMatrix V (b a)) α β * toFullBlockVec X β)) P :=
    fun α β =>
      ((hint α β).mul_const (toFullBlockVec X β)).const_mul (toFullBlockVec X α)
  have hrow : ∀ α : BlockCoord d, Integrable (fun a =>
      ∑ β : BlockCoord d, toFullBlockVec X α *
        (blockMatEntry (coarseBlockMatrix V (b a)) α β * toFullBlockVec X β)) P :=
    fun α => integrable_finsetSum _ fun β _ => hterm α β
  simp only [blockVecDot_blockMatVecMul_eq_sum, hentry]
  rw [integral_finsetSum _ fun α _ => hrow α]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_finsetSum _ fun β _ => hterm α β]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [integral_const_mul, integral_mul_const]

/-- **The pathwise response integrates to the annealed block energy.**  If the pathwise response
is the doubled block energy `x. A x / 2 - p. q'` with `x = (-p, q')` and `A` the coarse block
matrix of the adapted cell, and if the entries of `A` are `P`-integrable, then the expectation of
the response is the same block energy evaluated at the annealed block `Aann`:
`∫ J = x. Aann x / 2 - p. q'`.  This is the first step of the cutoff rows of
`e.response.cutoff.estimate`. -/
theorem integral_respJ_eq_blockResponseEnergy {d : ℕ}
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (qq : Mat d) (u : ℤ) (p q' : Vec d) (b : CoeffSpace d → CoeffField d) (Aann : BlockMat d)
    (hpath : ∀ a : CoeffSpace d, respJ qq u p q' (b a)
      = (1 / 2 : ℝ) * blockVecDot (-p, q')
          (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a)) (-p, q'))
        - vecDot p q')
    (hint : ∀ α β : BlockCoord d, Integrable (fun a =>
      blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a)) α β) P)
    (hann : annealedBlockOf P (HighContrast.adaptedCell qq u) b = Aann) :
    (∫ a, respJ qq u p q' (b a) ∂P)
      = (1 / 2 : ℝ) * blockVecDot (-p, q') (blockMatVecMul Aann (-p, q')) - vecDot p q' := by
  have hterm : ∀ α β : BlockCoord d, Integrable (fun a =>
      toFullBlockVec (-p, q') α *
        (blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a)) α β *
          toFullBlockVec (-p, q') β)) P :=
    fun α β =>
      ((hint α β).mul_const (toFullBlockVec (-p, q') β)).const_mul
        (toFullBlockVec (-p, q') α)
  have hQint : Integrable (fun a => blockVecDot (-p, q')
      (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a))
        (-p, q'))) P := by
    simp only [blockVecDot_blockMatVecMul_eq_sum]
    exact integrable_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun β _ => hterm α β
  have hQ := integral_blockVecDot_blockMatVecMul_coarseBlockMatrix P
    (HighContrast.adaptedCell qq u) b (-p, q') hint
  have huniv : P.real Set.univ = 1 := by simp
  simp only [hpath]
  rw [integral_sub (hQint.const_mul _) (integrable_const _), integral_const_mul, hQ, hann,
    integral_const, huniv, one_smul]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The annealed energies of the cutoff rows in closed block form

The cutoff rows of the response estimate bound the centred response with the two error scalars
`respEJMinus` and `respTauMinus`.  The first is the `P`-expectation of the recentred pathwise
response at one adapted cell; the second is the defect of that expectation between two scales.
Under the entrywise integrability of the coarse block carried by the cutoff rows, both are
algebraic functions of the recentred annealed block `respEhatMinus`: the pathwise response is the
block energy `x · A x / 2 - p · q'`, so its expectation is the same block energy of the annealed
block `E[A]`, and the pairing `p · q'` cancels in the defect.  These are the closed block forms
against which the cutoff rows are stated (`e.response.cutoff.estimate`).
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The `P`-expectation of the recentred pathwise response on an adapted cell `U_u` is the block
quadratic `½ x · E[A] x` of the recentred annealed block `respEhatMinus`, at the load
`x = (-p, q')`, minus the pairing `p · q'`.  This is the integral identity
`integral_respJ_eq_blockResponseEnergy` specialised to the recentred coefficient `a₋ = a - g`,
with its three inputs supplied by the coarse-block congruence, the entrywise transport of
integrability across that congruence, and the annealed-block identification
(`e.response.cutoff.estimate`, `e.annealed.schur`). -/
private theorem respIntegral_respCoeffMinus_eq_blockResponseEnergy {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (u : ℤ) (p q' : Vec d) (hq : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F u)) :
    (∫ a, respJ (respGrid jStar F) u p q' (respCoeffMinus F a) ∂P)
      = (1 / 2 : ℝ) * blockVecDot (-p, q')
          (blockMatVecMul (respEhatMinus P jStar F u) (-p, q'))
        - vecDot p q' := by
  have hintA : HasIntegrableCoarseBlock P (HighContrast.adaptedCell (respGrid jStar F) u) := hint
  have hpath : ∀ a : CoeffSpace d,
      respJ (respGrid jStar F) u p q' (respCoeffMinus F a)
        = (1 / 2 : ℝ) * blockVecDot (-p, q')
            (blockMatVecMul
              (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) u) (respCoeffMinus F a))
              (-p, q'))
          - vecDot p q' :=
    fun a => respJ_respCoeffMinus_eq (respGrid jStar F) hq u F a p q'
  have hint' : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) u) (respCoeffMinus F a))
      α β) P :=
    integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (G := respG F)
      (V := HighContrast.adaptedCell (respGrid jStar F) u) (b := respCoeffMinus F) hintA
      (fun a => coarseBlockMatrix_respCoeffMinus_eq_blockCongr (respGrid jStar F) hq u F a)
  have hann : annealedBlockOf P (HighContrast.adaptedCell (respGrid jStar F) u) (respCoeffMinus F)
      = respEhatMinus P jStar F u :=
    annealedBlockOf_respCoeffMinus_eq P jStar F u
      (fun a => hasQuadraticMu_adaptedCell (respGrid jStar F) hq u a) hint
  exact integral_respJ_eq_blockResponseEnergy P (respGrid jStar F) u p q'
    (respCoeffMinus F) (respEhatMinus P jStar F u) hpath hint' hann

/-- **The annealed energy of the cutoff minus rows as a block quadratic.**  Under entrywise
integrability of the coarse block, the `P`-expectation of the recentred pathwise response
`J(U_t, p, q⁻; a₋)` is the quadratic form `½ x · E[A] x` of the recentred annealed block
`respEhatMinus` at the load `x = (-p, q⁻)`, minus the pairing `p · q⁻`.  This is the closed block
form of the centred response energy `e.response.cutoff.estimate`. -/
theorem respEJMinus_eq_blockResponseEnergy {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    respEJMinus P jStar F t e
      = (1 / 2 : ℝ) * blockVecDot
          (-(respP (respMean P jStar F t) e), respqMinus P jStar F t e)
          (blockMatVecMul (respEhatMinus P jStar F t)
            (-(respP (respMean P jStar F t) e), respqMinus P jStar F t e))
        - vecDot (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) := by
  unfold respEJMinus
  exact respIntegral_respCoeffMinus_eq_blockResponseEnergy P jStar F t
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) hq hint

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The annealed response is the same on every aligned subcell

The mean cancellation behind `p.response.transfer` — the constant cell means cancel after
expectation because the scale-`s` translations are integral — rests on the statement that,
for a stationary law, the annealed response of a recentred coefficient family on an aligned
cell of a fixed scale is independent of the particular aligned cell.  The aligned cells of a
scale are integer translates of the centred cell, the annealed block of a translate is the
annealed block of the scale, and the pathwise response on any aligned cell is the block energy
of that cell's coarse block; hence the expectation is a function of the scale alone.

This module records that identity for both recentred families `a_-` and `a_+`.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  blockVecDot_blockMatVecMul_eq_sum coarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Stationary aligned cells have a scale-determined annealed response, minus sign.**  For a
stationary law `P` and the recentred coefficient `a_- = a - g` of `p.response.transfer`, the
`P`-expectation of the pathwise response on the aligned cell `adaptedCellAtCenter (respGrid jStar
F) j w`
is the block energy of the annealed block `Gᵀ E_j G`, independently of the cell index `w`. -/
theorem integral_responseJ_respCoeffMinus_adaptedCellAtCenter_eq_direct {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (p r : Vec d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) j w) p r (respCoeffMinus F a) ∂P)
      = blockResponseEnergy (blockCongr (respG F) (respMean P jStar F j)) p r := by
  have hq : IsUnit (respGrid jStar F) := by
    simpa [respGrid] using Geometry.isUnit_roundedGrid hjStar hm
  have hquad : ∀ a : CoeffSpace d,
      HasQuadraticMu (adaptedCellAtCenter (respGrid jStar F) j w) (⇑a.1 : CoeffField d) :=
    fun a => by
      simpa only [adaptedCellAtCenter] using
        hasQuadraticMu_adaptedCellTranslate (respGrid jStar F) hq j
          (adaptedCellCenter (respGrid jStar F) j w) a
  have hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffMinus F a)
        = blockCongr (respG F) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) j w) a) :=
    fun a => coarseBlockMatrix_sub_skew_eq_blockCongr (U := adaptedCellAtCenter (respGrid jStar F) j w)
      (a := (⇑a.1 : CoeffField d)) (g := respg F) (respg_isSkew F) (hquad a)
  have hpath : ∀ a : CoeffSpace d,
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) j w) p r (respCoeffMinus F a)
        = (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffMinus F a))
              (-p, r))
          - vecDot p r :=
    fun a => responseJ_adaptedCellAtCenter_respCoeffMinus (respGrid jStar F) hq j w F a p r
  have hint' : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffMinus F a)) α β) P :=
    integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (G := respG F)
      (V := adaptedCellAtCenter (respGrid jStar F) j w) (b := respCoeffMinus F) hint hb
  have hann : annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffMinus F)
      = blockCongr (respG F) (respMean P jStar F j) := by
    rw [annealedBlockOf_eq_blockCongr (respG F) (respCoeffMinus F) hint hb]
    congr 1
    have h := Annealed.annealedBlock_adaptedCellAtCenter P hstat jStar hjStar (explicitCanonicalMetric F) hm j hj w
    simpa [respGrid, respMean] using h
  have hterm : ∀ α β : BlockCoord d, Integrable (fun a =>
      toFullBlockVec (-p, r) α *
        (blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
          (respCoeffMinus F a)) α β * toFullBlockVec (-p, r) β)) P :=
    fun α β =>
      ((hint' α β).mul_const (toFullBlockVec (-p, r) β)).const_mul (toFullBlockVec (-p, r) α)
  have hQint : Integrable (fun a => blockVecDot (-p, r)
      (blockMatVecMul (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffMinus F a)) (-p, r))) P := by
    simp only [blockVecDot_blockMatVecMul_eq_sum]
    exact integrable_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun β _ => hterm α β
  have hQ := integral_blockVecDot_blockMatVecMul_coarseBlockMatrix P
    (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffMinus F) (-p, r) hint'
  have huniv : P.real Set.univ = 1 := by simp
  simp only [blockResponseEnergy, hpath]
  rw [integral_sub (hQint.const_mul _) (integrable_const _), integral_const_mul, hQ, hann,
    integral_const, huniv, one_smul]

/-- **Stationary aligned cells have a scale-determined annealed response, plus sign.**  For a
stationary law `P` and the recentred coefficient `a_+ = aᵀ + g` of `p.response.transfer`, the
`P`-expectation of the pathwise response on the aligned cell `adaptedCellAtCenter (respGrid jStar
F) j w`
is the block energy of the annealed block `G_+ᵀ E_j G_+`, independently of the cell index `w`. -/
theorem integral_responseJ_respCoeffPlus_adaptedCellAtCenter_eq_direct {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (p r : Vec d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    (∫ a, ResponseJ (adaptedCellAtCenter (respGrid jStar F) j w) p r (respCoeffPlus F a) ∂P)
      = blockResponseEnergy (blockCongr (respGPlus F) (respMean P jStar F j)) p r := by
  have hq : IsUnit (respGrid jStar F) := by
    simpa [respGrid] using Geometry.isUnit_roundedGrid hjStar hm
  have hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffPlus F a)
        = blockCongr (respGPlus F) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) j w) a) :=
    fun a => coarseBlockMatrix_respCoeffPlus_at hq j w F a
  have hpath : ∀ a : CoeffSpace d,
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) j w) p r (respCoeffPlus F a)
        = (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffPlus F a))
              (-p, r))
          - vecDot p r :=
    fun a => responseJ_adaptedCellAtCenter_respCoeffPlus (respGrid jStar F) hq j w F a p r
  have hint' : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffPlus F a)) α β) P :=
    integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (G := respGPlus F)
      (V := adaptedCellAtCenter (respGrid jStar F) j w) (b := respCoeffPlus F) hint hb
  have hann : annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffPlus F)
      = blockCongr (respGPlus F) (respMean P jStar F j) := by
    rw [annealedBlockOf_eq_blockCongr (respGPlus F) (respCoeffPlus F) hint hb]
    congr 1
    have h := Annealed.annealedBlock_adaptedCellAtCenter P hstat jStar hjStar (explicitCanonicalMetric F) hm j hj w
    simpa [respGrid, respMean] using h
  have hterm : ∀ α β : BlockCoord d, Integrable (fun a =>
      toFullBlockVec (-p, r) α *
        (blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
          (respCoeffPlus F a)) α β * toFullBlockVec (-p, r) β)) P :=
    fun α β =>
      ((hint' α β).mul_const (toFullBlockVec (-p, r) β)).const_mul (toFullBlockVec (-p, r) α)
  have hQint : Integrable (fun a => blockVecDot (-p, r)
      (blockMatVecMul (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffPlus F a)) (-p, r))) P := by
    simp only [blockVecDot_blockMatVecMul_eq_sum]
    exact integrable_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun β _ => hterm α β
  have hQ := integral_blockVecDot_blockMatVecMul_coarseBlockMatrix P
    (adaptedCellAtCenter (respGrid jStar F) j w) (respCoeffPlus F) (-p, r) hint'
  have huniv : P.real Set.univ = 1 := by simp
  simp only [blockResponseEnergy, hpath]
  rw [integral_sub (hQint.const_mul _) (integrable_const _), integral_const_mul, hQ, hann,
    integral_const, huniv, one_smul]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The annealed block of an aligned cell is independent of the cell

For a stationary law `P` and a scale `j` above `j_*`, the annealed block of a recentred
coefficient family `a_- = a - g` or `a_+ = aᵀ + g` on an aligned cell of the adapted grid is
the same matrix at every cell of the scale.  Every scale-`j` aligned cell is an integer
translate of the centred cell, the law is invariant under integer translations, and the
recentring subtracts (respectively adds) a constant matrix field, which commutes with
translation.  This is the `w`-independence that makes the flat average over the `3^{H d}`
subcells of the direct full-dual pairing collapse to the head term of `respSourceLoad` in
`p.response.transfer`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter measurable_translateCoeff
  translateCoeff)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory Geometry

noncomputable section

/-- A translated adapted cell is the translate of the centred adapted cell: both are the
image of `⋄_j^q` under `x ↦ y + x`. -/
private theorem adaptedCellTranslate_eq_translateSet {d : ℕ} (q : Mat d) (j : ℤ) (y : Vec d) :
    HighContrast.adaptedCellTranslate q j y = translateSet y (HighContrast.adaptedCell q j) := by
  ext x
  simp only [HighContrast.adaptedCellTranslate, translateSet, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw, hwxy⟩
    exact ⟨w, hw, by rw [← hwxy, add_comm]⟩
  · rintro ⟨w, hw, hwxy⟩
    exact ⟨w, hw, by rw [hwxy, add_comm]⟩

/-- The coarse block of the recentred field `a_- = a - g` on an integer translate of a cell is
the coarse block of the translated recentred field on the cell.  The recentring subtracts the
constant matrix field `g`, which is unaffected by translation, so the covariance is that of the
coarse block matrix itself. -/
private theorem coarseBlockMatrix_adaptedCellTranslate_respCoeffMinus {d : ℕ}
    (q : Mat d) (j : ℤ) (z : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (HighContrast.adaptedCellTranslate q j (Source.AKL.intTranslation z))
        (respCoeffMinus F a)
      = coarseBlockMatrix (HighContrast.adaptedCell q j) (respCoeffMinus F (translateCoeff z a)) := by
  rw [adaptedCellTranslate_eq_translateSet,
    coarseBlockMatrix_translateSet_eq_translateCoeffField]
  apply coarseBlockMatrix_congr_of_ae_eq
  apply ae_restrict_of_ae
  filter_upwards [Source.AKL.translateField_ae z a.1] with x hxpt
  exact (congrArg (fun M : Mat d => M - respg F) hxpt).symm

/-- The coarse block of the recentred field `a_+ = aᵀ + g` on an integer translate of a cell is
the coarse block of the translated recentred field on the cell.  The recentring adds the
constant matrix field `g`, which is unaffected by translation, so the covariance is that of the
coarse block matrix itself. -/
private theorem coarseBlockMatrix_adaptedCellTranslate_respCoeffPlus {d : ℕ}
    (q : Mat d) (j : ℤ) (z : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (HighContrast.adaptedCellTranslate q j (Source.AKL.intTranslation z))
        (respCoeffPlus F a)
      = coarseBlockMatrix (HighContrast.adaptedCell q j) (respCoeffPlus F (translateCoeff z a)) := by
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
      G (HighContrast.adaptedCellTranslate (explicitRoundedGrid jStar m) j (Source.AKL.intTranslation z))
          a
        = G (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) (translateCoeff z a))
    (hmeas : AEStronglyMeasurable (G (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)) P) :
    (∫ a, G (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) a ∂P)
      = ∫ a, G (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) a ∂P := by
  obtain ⟨z, hz⟩ := Annealed.adaptedCellCenter_eq_intTranslation jStar m hj w
  have hcongr : (∫ a, G (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) a ∂P) =
      ∫ a, G (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) (translateCoeff z a) ∂P := by
    apply integral_congr_ae
    filter_upwards with a
    change G (HighContrast.adaptedCellTranslate (explicitRoundedGrid jStar m) j
          (adaptedCellCenter (explicitRoundedGrid jStar m) j w)) a
        = G (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) (translateCoeff z a)
    rw [hz]
    exact hG z a
  rw [hcongr]
  exact integral_comp_translateCoeff_eq_aux P hstat z _ hmeas

/-- **The annealed block of the recentred field is the same on every aligned cell, minus
sign.**  For a stationary law `P` and the recentred coefficient `a_- = a - g` of
`p.response.transfer`, the `P`-entrywise annealed block of the pathwise coarse block on an
aligned cell of scale `j ≥ j_*` is the annealed block of the centred cell, independently of the
cell index `w`. -/
theorem annealedBlockOf_adaptedCellAtCenter_respCoeffMinus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (F : BlockMat d) (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (hmeas : ∀ i k : Fin d,
      AEStronglyMeasurable (fun a =>
        (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
          (respCoeffMinus F a)).upperLeft i k) P)
    (hmeas' : ∀ i k : Fin d,
      AEStronglyMeasurable (fun a =>
        (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
          (respCoeffMinus F a)).lowerRight i k) P) :
    ((annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) (respCoeffMinus F)).upperLeft
        = (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
            (respCoeffMinus F)).upperLeft)
      ∧ ((annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
            (respCoeffMinus F)).lowerRight
        = (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
            (respCoeffMinus F)).lowerRight) := by
  constructor
  · ext i k
    have h := integral_cellFunctional_adaptedCellAtCenter_eq_aux P hstat jStar m j hj w
      (fun V a => (coarseBlockMatrix V (respCoeffMinus F a)).upperLeft i k)
      (fun z a => congrArg (fun B : BlockMat d => B.upperLeft i k)
        (coarseBlockMatrix_adaptedCellTranslate_respCoeffMinus (explicitRoundedGrid jStar m) j z F a))
      (hmeas i k)
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffMinus F)).upperLeft i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
              (respCoeffMinus F a)).upperLeft i k ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffMinus F)).upperLeft i k
          = ∫ a, (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
              (respCoeffMinus F a)).upperLeft i k ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_cellFunctional_adaptedCellAtCenter_eq_aux P hstat jStar m j hj w
      (fun V a => (coarseBlockMatrix V (respCoeffMinus F a)).lowerRight i k)
      (fun z a => congrArg (fun B : BlockMat d => B.lowerRight i k)
        (coarseBlockMatrix_adaptedCellTranslate_respCoeffMinus (explicitRoundedGrid jStar m) j z F a))
      (hmeas' i k)
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffMinus F)).lowerRight i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
              (respCoeffMinus F a)).lowerRight i k ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffMinus F)).lowerRight i k
          = ∫ a, (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
              (respCoeffMinus F a)).lowerRight i k ∂P := rfl
    rw [hred, hred']
    exact h

/-- **The annealed block of the recentred field is the same on every aligned cell, plus
sign.**  For a stationary law `P` and the recentred coefficient `a_+ = aᵀ + g` of
`p.response.transfer`, the `P`-entrywise annealed block of the pathwise coarse block on an
aligned cell of scale `j ≥ j_*` is the annealed block of the centred cell, independently of the
cell index `w`. -/
theorem annealedBlockOf_adaptedCellAtCenter_respCoeffPlus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (F : BlockMat d) (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (hmeas : ∀ i k : Fin d,
      AEStronglyMeasurable (fun a =>
        (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
          (respCoeffPlus F a)).upperLeft i k) P)
    (hmeas' : ∀ i k : Fin d,
      AEStronglyMeasurable (fun a =>
        (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
          (respCoeffPlus F a)).lowerRight i k) P) :
    ((annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) (respCoeffPlus F)).upperLeft
        = (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
            (respCoeffPlus F)).upperLeft)
      ∧ ((annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
            (respCoeffPlus F)).lowerRight
        = (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
            (respCoeffPlus F)).lowerRight) := by
  constructor
  · ext i k
    have h := integral_cellFunctional_adaptedCellAtCenter_eq_aux P hstat jStar m j hj w
      (fun V a => (coarseBlockMatrix V (respCoeffPlus F a)).upperLeft i k)
      (fun z a => congrArg (fun B : BlockMat d => B.upperLeft i k)
        (coarseBlockMatrix_adaptedCellTranslate_respCoeffPlus (explicitRoundedGrid jStar m) j z F a))
      (hmeas i k)
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffPlus F)).upperLeft i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
              (respCoeffPlus F a)).upperLeft i k ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffPlus F)).upperLeft i k
          = ∫ a, (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
              (respCoeffPlus F a)).upperLeft i k ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_cellFunctional_adaptedCellAtCenter_eq_aux P hstat jStar m j hj w
      (fun V a => (coarseBlockMatrix V (respCoeffPlus F a)).lowerRight i k)
      (fun z a => congrArg (fun B : BlockMat d => B.lowerRight i k)
        (coarseBlockMatrix_adaptedCellTranslate_respCoeffPlus (explicitRoundedGrid jStar m) j z F a))
      (hmeas' i k)
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffPlus F)).lowerRight i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
              (respCoeffPlus F a)).lowerRight i k ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffPlus F)).lowerRight i k
          = ∫ a, (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
              (respCoeffPlus F a)).lowerRight i k ∂P := rfl
    rw [hred, hred']
    exact h

end

end HCPolySupport.HighContrast.Multiscale
end
