/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseAbsolute
public import LeanPool.HighContrastHomogenization.Geometry.AspectRatioMonotone
public import LeanPool.HighContrastHomogenization.Provider.Initialization.IdentityGrid
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.TraceGap

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastHattedCarrier

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The hatted small-contrast carrier

The small-contrast argument uses the normalized trace of the two symmetric
Schur blocks.  This file records that carrier on a doubled block and relates it
directly to the calibrated primal--adjoint centered responses.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory Set

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The normalized trace of the upper Schur block relative to the lower one. -/
@[expose]
def schurHattedContrast (S SStar : Mat d) : ℝ :=
  (d : ℝ)⁻¹ * Matrix.trace
    (matSqrt SStar⁻¹ * S * matSqrt SStar⁻¹)

/-- The hatted contrast of a doubled block, written with its lower-right block,
which is the inverse lower Schur block on positive data. -/
@[expose]
def hattedContrast (H : BlockMat d) : ℝ :=
  (d : ℝ)⁻¹ * Matrix.trace
    (matSqrt H.lowerRight * schurSigma H * matSqrt H.lowerRight)

/-- The hatted contrast of the annealed response on an adapted cell. -/
@[expose]
def adaptedHattedContrast (P : Measure (CoeffSpace d)) (q : Mat d)
    (m : ℤ) : ℝ :=
  hattedContrast (adaptedMean P q m)

/-- On positive data cyclicity writes the hatted carrier without square roots. -/
theorem hattedContrast_eq_trace_lowerRight_mul {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpos : BlockPosDef H) :
    hattedContrast H =
      (d : ℝ)⁻¹ * Matrix.trace (H.lowerRight * schurSigma H) := by
  have hroot : matSqrt H.lowerRight * matSqrt H.lowerRight = H.lowerRight :=
    (matSqrt_spec (posSemidef_lowerRight hsymm hpos)).2
  rw [hattedContrast, Matrix.trace_mul_cycle, hroot]

/-- The hatted carrier is monotone for the doubled Loewner order on symmetric
positive blocks. -/
theorem hattedContrast_le_of_blockMatLoewnerLE {A E : BlockMat d}
    (hAsymm : IsSymmetricBlockMat A) (hApos : BlockPosDef A)
    (hEsymm : IsSymmetricBlockMat E) (hEpos : BlockPosDef E)
    (hle : BlockMatLoewnerLE A E) :
    hattedContrast A ≤ hattedContrast E := by
  have hAlower : A.lowerRight.PosDef := posDef_lowerRight hAsymm hApos
  have hElower : E.lowerRight.PosDef := posDef_lowerRight hEsymm hEpos
  have hlower : A.lowerRight ≤ E.lowerRight :=
    Initialization.le_of_matLoewnerLE hAlower.isHermitian hElower.isHermitian
      (matLoewnerLE_lowerRight_of_blockMatLoewnerLE hle)
  have hAsigma : (schurSigma A).PosSemidef :=
    posSemidef_schurSigma hAsymm hApos
  have hEsigma : (schurSigma E).PosSemidef :=
    posSemidef_schurSigma hEsymm hEpos
  have hsigma : schurSigma A ≤ schurSigma E := by
    apply Initialization.le_of_matLoewnerLE hAsigma.isHermitian hEsigma.isHermitian
    refine (matLoewnerLE_schurSigma_skewCorrectedForm
      hApos (schurSkew E)).trans ?_
    have hfixed := matLoewnerLE_skewCorrectedForm_of_blockMatLoewnerLE
      hAsymm hApos hEsymm hEpos hle (schurSkew E)
    simpa only [skewCorrectedForm, sub_self, Matrix.transpose_zero,
      Matrix.zero_mul, Matrix.mul_zero, add_zero] using hfixed
  have hfirst :
      Matrix.trace (A.lowerRight * schurSigma A) ≤
        Matrix.trace (E.lowerRight * schurSigma A) := by
    have htrace := PortableHistory.trace_mul_le_trace_mul hAsigma hlower
    rwa [Matrix.trace_mul_comm (schurSigma A) A.lowerRight,
      Matrix.trace_mul_comm (schurSigma A) E.lowerRight] at htrace
  have hsecond :
      Matrix.trace (E.lowerRight * schurSigma A) ≤
        Matrix.trace (E.lowerRight * schurSigma E) :=
    PortableHistory.trace_mul_le_trace_mul hElower.posSemidef hsigma
  rw [hattedContrast_eq_trace_lowerRight_mul hAsymm hApos,
    hattedContrast_eq_trace_lowerRight_mul hEsymm hEpos]
  exact mul_le_mul_of_nonneg_left (hfirst.trans hsecond) (by positivity)

/-- The normalized trace carrier is bounded by the intrinsic polynomial
contrast. -/
theorem hattedContrast_le_blockContrast [NeZero d] {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpos : BlockPosDef H) :
    hattedContrast H ≤ blockContrast H := by
  obtain ⟨h, -, hcorrected⟩ :=
    Initialization.exists_isSkewMat_matLoewnerLE_refContrast_smul hsymm hpos
  have hsigmaLoewner : MatLoewnerLE (schurSigma H)
      (blockContrast H • schurSigmaStar H) :=
    (matLoewnerLE_schurSigma_skewCorrectedForm hpos h).trans
      (by simpa only [refContrast] using hcorrected)
  have hlower : H.lowerRight.PosDef := posDef_lowerRight hsymm hpos
  have hstar : (schurSigmaStar H).PosDef := by
    simpa only [schurSigmaStar] using hlower.inv
  have hscaled : (blockContrast H • schurSigmaStar H).PosSemidef :=
    hstar.posSemidef.smul (blockContrast_nonneg H)
  have hsigma : schurSigma H ≤ blockContrast H • schurSigmaStar H :=
    Initialization.le_of_matLoewnerLE (posSemidef_schurSigma hsymm hpos).isHermitian
      hscaled.isHermitian hsigmaLoewner
  have htrace : Matrix.trace (H.lowerRight * schurSigma H) ≤
      (d : ℝ) * blockContrast H := by
    calc
      Matrix.trace (H.lowerRight * schurSigma H) ≤
          Matrix.trace
            (H.lowerRight * (blockContrast H • schurSigmaStar H)) :=
        PortableHistory.trace_mul_le_trace_mul hlower.posSemidef hsigma
      _ = blockContrast H * Matrix.trace
          (H.lowerRight * schurSigmaStar H) := by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      _ = blockContrast H * (d : ℝ) := by
        rw [schurSigmaStar,
          Matrix.mul_nonsing_inv _ (isUnit_det_lowerRight hpos), Matrix.trace_one]
        simp only [Fintype.card_fin]
      _ = (d : ℝ) * blockContrast H := mul_comm _ _
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne d)
  rw [hattedContrast_eq_trace_lowerRight_mul hsymm hpos]
  calc
    (d : ℝ)⁻¹ * Matrix.trace (H.lowerRight * schurSigma H) ≤
        (d : ℝ)⁻¹ * ((d : ℝ) * blockContrast H) :=
      mul_le_mul_of_nonneg_left htrace (by positivity)
    _ = blockContrast H := by
      rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul]

/-- The hatted contrast decreases along one fixed rounded adapted grid. -/
theorem adaptedHattedContrast_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    {j p : ℤ} (hlj : l ≤ j) (hjp : j ≤ p)
    (hfinj : HasFiniteAdaptedMean P q j)
    (hfinp : HasFiniteAdaptedMean P q p) :
    adaptedHattedContrast P q p ≤ adaptedHattedContrast P q j := by
  apply hattedContrast_le_of_blockMatLoewnerLE
  · exact Recurrence.isSymmetricBlockMat_adaptedMean P q p
  · exact Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hgrid p hfinp
  · exact Recurrence.isSymmetricBlockMat_adaptedMean P q j
  · exact Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hgrid j hfinj
  · exact Recurrence.adaptedMean_le hstat hgrid hlj hjp hfinj hfinp

/-- On the Euclidean grid, the adapted carrier is the hatted carrier of the
annealed response on the centered cube. -/
theorem adaptedHattedContrast_one (P : Measure (CoeffSpace d)) (m : ℤ) :
    adaptedHattedContrast P (1 : Mat d) m =
      hattedContrast (annealedBlock P (centeredCube d m)) := by
  rw [adaptedHattedContrast, adaptedMean, Initialization.adaptedCell_one]

/-- On the Euclidean grid, the adapted hatted carrier is bounded by the
annealed intrinsic contrast. -/
theorem adaptedHattedContrast_one_le_annealedContrast [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (m : ℤ) :
    adaptedHattedContrast P (1 : Mat d) m ≤ annealedContrast P m := by
  rw [adaptedHattedContrast_one, annealedContrast]
  exact hattedContrast_le_blockContrast
    (isSymmetricBlockMat_annealedBlock P (centeredCube d m))
    (blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag m)

/-- Euclidean annealed smallness therefore initializes the adapted hatted
carrier at the same generation. -/
theorem adaptedHattedContrast_one_sub_one_le_of_annealedContrast_sub_one_le
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (m : ℤ) {c : ℝ} (hsmall : annealedContrast P m - 1 ≤ c) :
    adaptedHattedContrast P (1 : Mat d) m - 1 ≤ c :=
  (sub_le_sub_right (adaptedHattedContrast_one_le_annealedContrast hdag m) 1).trans
    hsmall

/-- A Schur representation identifies the intrinsic block carrier with the
two-matrix Schur carrier. -/
theorem hattedContrast_eq_schurHattedContrast {H : BlockMat d}
    {S SStar K : Mat d} (hStar : SStar.PosDef)
    (hH : toFullBlockMat H = schurBlock S SStar K) :
    hattedContrast H = schurHattedContrast S SStar := by
  have hStarDet : IsUnit SStar.det := isUnit_det_of_posDef hStar
  have hlowerRight : H.lowerRight = SStar⁻¹ := by
    have hblock : H.lowerRight = (toFullBlockMat H).toBlocks₂₂ := rfl
    rw [hblock, hH, toBlocks₂₂_schurBlock]
  have hlowerLeft : H.lowerLeft = -(SStar⁻¹ * K) := by
    have hblock : H.lowerLeft = (toFullBlockMat H).toBlocks₂₁ := rfl
    rw [hblock, hH, toBlocks₂₁_schurBlock]
  have hupperLeft : H.upperLeft = S + Kᴴ * SStar⁻¹ * K := by
    have hblock : H.upperLeft = (toFullBlockMat H).toBlocks₁₁ := rfl
    rw [hblock, hH, toBlocks₁₁_schurBlock]
  have hskew : schurSkew H = K := by
    rw [schurSkew, hlowerRight, hlowerLeft,
      Matrix.nonsing_inv_nonsing_inv _ hStarDet, Matrix.mul_neg,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hStarDet,
      Matrix.one_mul, neg_neg]
  have hsigma : schurSigma H = S := by
    rw [schurSigma, hupperLeft, hlowerRight, hskew,
      ← Response.conjTranspose_eq_matTranspose]
    abel
  rw [hattedContrast, schurHattedContrast, hlowerRight, hsigma]

/-- The hatted defect is the dimension-normalized trace of the positive Schur
excess. -/
theorem schurHattedContrast_sub_one_eq_trace_centeredResponseX [NeZero d]
    (S SStar : Mat d) :
    schurHattedContrast S SStar - 1 =
      (d : ℝ)⁻¹ * Matrix.trace (Response.centeredResponseX S SStar) := by
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne d)
  rw [schurHattedContrast, Response.centeredResponseX, Matrix.trace_sub,
    Matrix.trace_one]
  simp only [Fintype.card_fin]
  rw [mul_sub]
  have hcancel : (d : ℝ)⁻¹ * (d : ℝ) = 1 := inv_mul_cancel₀ hd0
  rw [hcancel]

/-- The source hatted defect is controlled directly by the calibrated absolute
primal--adjoint centered response supremum. -/
theorem schurHattedContrast_sub_one_le_absoluteCenteredResponseSup
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Domain d) (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) :
    schurHattedContrast S SStar - 1 ≤
      sSup
        ((fun e : Vec d =>
            |Response.centeredResponse P U
              (Response.centeredResponseLoadP S SStar K e)
              (Response.centeredResponseLoadQ S SStar K e -
                Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)| +
            |Response.centeredAdjointResponse P U
              (Response.centeredResponseLoadP S SStar K e)
              (Response.centeredResponseLoadQ S SStar K e +
                Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)|) ''
          {e : Vec d | e ⬝ᵥ e = 1}) := by
  let responseSup : ℝ :=
    sSup
      ((fun e : Vec d =>
          |Response.centeredResponse P U
            (Response.centeredResponseLoadP S SStar K e)
            (Response.centeredResponseLoadQ S SStar K e -
              Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)| +
          |Response.centeredAdjointResponse P U
            (Response.centeredResponseLoadP S SStar K e)
            (Response.centeredResponseLoadQ S SStar K e +
              Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)|) ''
        {e : Vec d | e ⬝ᵥ e = 1})
  have hbdd := Response.bddAbove_absolute_centeredResponses U hint hStar hE
  have hbasis (i : Fin d) :
      Response.centeredResponseTraceValue P U S SStar K
          (Pi.single i (1 : ℝ)) ≤ responseSup := by
    have hunit : (Pi.single i (1 : ℝ) : Vec d) ⬝ᵥ
        Pi.single i (1 : ℝ) = 1 := by
      simp [dotProduct, Pi.single_apply, mul_ite, Finset.sum_ite_eq']
    calc
      Response.centeredResponseTraceValue P U S SStar K
          (Pi.single i (1 : ℝ)) ≤
          |Response.centeredResponse P U
            (Response.centeredResponseLoadP S SStar K (Pi.single i (1 : ℝ)))
            (Response.centeredResponseLoadQ S SStar K (Pi.single i (1 : ℝ)) -
              Response.responseSkew K *ᵥ
                Response.centeredResponseLoadP S SStar K (Pi.single i (1 : ℝ)))| +
          |Response.centeredAdjointResponse P U
            (Response.centeredResponseLoadP S SStar K (Pi.single i (1 : ℝ)))
            (Response.centeredResponseLoadQ S SStar K (Pi.single i (1 : ℝ)) +
              Response.responseSkew K *ᵥ
                Response.centeredResponseLoadP S SStar K (Pi.single i (1 : ℝ)))| := by
        rw [Response.centeredResponseTraceValue]
        exact add_le_add (le_abs_self _) (le_abs_self _)
      _ ≤ responseSup := by
        apply le_csSup hbdd
        exact ⟨Pi.single i (1 : ℝ), hunit, rfl⟩
  have hsum :
      (∑ i : Fin d, Response.centeredResponseTraceValue P U S SStar K
        (Pi.single i (1 : ℝ))) ≤ (d : ℝ) * responseSup := by
    calc
      (∑ i : Fin d, Response.centeredResponseTraceValue P U S SStar K
          (Pi.single i (1 : ℝ))) ≤ ∑ _i : Fin d, responseSup :=
        Finset.sum_le_sum fun i _ ↦ hbasis i
      _ = (d : ℝ) * responseSup := by simp
  have hY0 : 0 ≤ Matrix.trace (Response.centeredResponseY SStar K) :=
    (Response.centeredResponseY_posSemidef hStar K).trace_nonneg
  have htrace : Matrix.trace (Response.centeredResponseX S SStar) ≤
      (d : ℝ) * responseSup := by
    have hidentity := Response.sum_centeredResponseTraceValue U hint hS hStar hE
    rw [hidentity] at hsum
    linarith only [hsum, hY0]
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne d)
  have hinv : 0 ≤ (d : ℝ)⁻¹ := by positivity
  rw [schurHattedContrast_sub_one_eq_trace_centeredResponseX S SStar]
  change (d : ℝ)⁻¹ * Matrix.trace (Response.centeredResponseX S SStar) ≤ responseSup
  calc
    (d : ℝ)⁻¹ * Matrix.trace (Response.centeredResponseX S SStar) ≤
        (d : ℝ)⁻¹ * ((d : ℝ) * responseSup) :=
      mul_le_mul_of_nonneg_left htrace hinv
    _ = responseSup := by
      rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul]

/-- The same response lower bound, expressed on the annealed doubled block. -/
theorem hattedContrast_annealedBlock_sub_one_le_absoluteCenteredResponseSup
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Domain d) (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    {S SStar K : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hE : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K) :
    hattedContrast (annealedBlock P (U : Set (Vec d))) - 1 ≤
      sSup
        ((fun e : Vec d =>
            |Response.centeredResponse P U
              (Response.centeredResponseLoadP S SStar K e)
              (Response.centeredResponseLoadQ S SStar K e -
                Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)| +
            |Response.centeredAdjointResponse P U
              (Response.centeredResponseLoadP S SStar K e)
              (Response.centeredResponseLoadQ S SStar K e +
                Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)|) ''
          {e : Vec d | e ⬝ᵥ e = 1}) := by
  rw [hattedContrast_eq_schurHattedContrast hStar hE]
  exact schurHattedContrast_sub_one_le_absoluteCenteredResponseSup
    U hint hS hStar hE

end

end HCPolySupport.HighContrast.Quenched
