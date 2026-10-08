/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.Attainment

/-!
# High-contrast homogenization: Geometry.AspectRatioOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The reference aspect ratio under the Schur ordering

The reference aspect ratio `Π = Λ_0 / λ_0` of `e.reference.aspect.ratio` is not
bounded below by one for an arbitrary symmetric positive definite doubled block:
the doubled dilation `c · I` has `Π = c²`, which is smaller than one for
`c < 1`.  What forces `1 ≤ Π` is the ordering of the two symmetric Schur blocks
of the parametrization `e.annealed.schur`, namely `σ_* ≤ σ`.

The proof is a chain of three Loewner inequalities.  Positivity of the
lower-right block makes the skew correction `(k - h)ᵗ σ_*⁻¹ (k - h)` nonnegative
at every `h`, so `σ ≤ σ + (k - h)ᵗ σ_*⁻¹ (k - h)`; evaluating at a skew matrix
realizing `Λ_0` gives `σ ≤ Λ_0 · I`.  Conjugating by the square root of the
lower-right block turns the definition of the spectral bound `|σ_*⁻¹|` into
`I ≤ |σ_*⁻¹| · σ_*`.  Composing the two through the hypothesis `σ_* ≤ σ` gives
`I ≤ (|σ_*⁻¹| Λ_0) · I`, and testing against a vector of unit length reads off
`1 ≤ Λ_0 |σ_*⁻¹| = Π`.

The bound is sharp: at `σ_* = σ` the chain is an equality and `Π = 1`.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-! ## Quadratic-form bookkeeping -/

private theorem matVecMul_one_left (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem vecDot_matVecMul_one (x : Vec d) :
    vecDot x (matVecMul (1 : Mat d) x) = vecNormSq x := by
  rw [matVecMul_one_left]
  rfl

private theorem vecDot_matVecMul_smul_one (t : ℝ) (x : Vec d) :
    vecDot x (matVecMul (t • (1 : Mat d)) x) = t * vecNormSq x := by
  rw [smul_matVecMul, matVecMul_one_left, vecDot_smul_right]
  rfl

private theorem vecDot_matVecMul_conj (D M : Mat d) (x : Vec d) :
    vecDot x (matVecMul (matTranspose D * M * D) x) =
      vecDot (matVecMul D x) (matVecMul M (matVecMul D x)) := by
  rw [mul_assoc, ← matVecMul_mul, vecDot_matVecMul_transpose, matVecMul_mul]

private theorem vecNormSq_single (j : Fin d) :
    vecNormSq (Pi.single j (1 : ℝ)) = 1 := by
  change vecDot (Pi.single j (1 : ℝ)) (Pi.single j (1 : ℝ)) = 1
  simp [vecDot, Pi.single_apply, mul_ite, Finset.sum_ite_eq']

/-- In a positive dimension there is a vector of unit length. -/
private theorem exists_vecNormSq_eq_one [NeZero d] : ∃ e : Vec d, vecNormSq e = 1 :=
  ⟨Pi.single ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ (1 : ℝ), vecNormSq_single _⟩

/-- The Loewner order is preserved by nonnegative scaling. -/
theorem matLoewnerLE_smul {c : ℝ} (hc : 0 ≤ c) {A B : Mat d} (h : MatLoewnerLE A B) :
    MatLoewnerLE (c • A) (c • B) := by
  intro x
  have hA : vecDot x (matVecMul (c • A) x) = c * vecDot x (matVecMul A x) := by
    rw [smul_matVecMul, vecDot_smul_right]
  have hB : vecDot x (matVecMul (c • B) x) = c * vecDot x (matVecMul B x) := by
    rw [smul_matVecMul, vecDot_smul_right]
  have hstep : c * vecDot x (matVecMul A x) ≤ c * vecDot x (matVecMul B x) :=
    mul_le_mul_of_nonneg_left (by linarith only [h x]) hc
  rw [hA, hB]
  linarith only [hstep]

/-! ## The aspect ratio as a product -/

/-- The aspect ratio `Π = Λ_0 / λ_0` written as the product `Λ_0 |σ_{*,0}^{-1}|`
of the two constants of `e.reference.aspect.ratio`. -/
theorem aspectRatio_eq_bigLambdaRef_mul_specBound (E : BlockMat d) :
    aspectRatio E = bigLambdaRef E * specBound E.lowerRight := by
  rw [aspectRatio, lambdaRef, div_eq_mul_inv, inv_inv]

/-! ## The two halves of the chain -/

private theorem zero_le_vecDot_matVecMul_lowerRight {E : BlockMat d}
    (hpos : Book.Ch02.BlockPosDef E) (y : Vec d) :
    0 ≤ vecDot y (matVecMul E.lowerRight y) := by
  by_cases hy : y = 0
  · subst hy
    rw [matVecMul_zero, vecDot_zero_left]
  · exact (quadratic_pos_lowerRight hpos y hy).le

/-- The skew correction only increases the Schur block: `σ ≤ σ + (k - h)ᵗ σ_*⁻¹
(k - h)` at every `h`, because the lower-right block is positive. -/
theorem matLoewnerLE_schurSigma_skewCorrectedForm {E : BlockMat d}
    (hpos : Book.Ch02.BlockPosDef E) (h : Mat d) :
    MatLoewnerLE (schurSigma E) (skewCorrectedForm E h) := by
  intro x
  have hcorr : 0 ≤ vecDot x (matVecMul
      (matTranspose (schurSkew E - h) * E.lowerRight * (schurSkew E - h)) x) := by
    rw [vecDot_matVecMul_conj]
    exact zero_le_vecDot_matVecMul_lowerRight hpos _
  have hsplit : vecDot x (matVecMul (skewCorrectedForm E h) x) =
      vecDot x (matVecMul (schurSigma E) x) +
        vecDot x (matVecMul
          (matTranspose (schurSkew E - h) * E.lowerRight * (schurSkew E - h)) x) := by
    rw [skewCorrectedForm, add_matVecMul, vecDot_add_right]
  rw [hsplit]
  linarith only [hcorr]

/-- **The upper half of the chain**: the Schur block `σ` is dominated by
`Λ_0 · I`.  The reference constant is realized at some skew matrix, and the
skew-corrected form there dominates `σ`. -/
theorem matLoewnerLE_schurSigma_bigLambdaRef_smul_one {E : BlockMat d}
    (hpos : Book.Ch02.BlockPosDef E) :
    MatLoewnerLE (schurSigma E) (bigLambdaRef E • (1 : Mat d)) := by
  obtain ⟨h, -, hLam⟩ := exists_isSkewMat_bigLambdaRef_eq hpos
  refine (matLoewnerLE_schurSigma_skewCorrectedForm hpos h).trans ?_
  rw [hLam]
  exact matLoewnerLE_specBound_smul_one _

/-- **The lower half of the chain**: `I ≤ |σ_{*,0}^{-1}| · σ_{*,0}`.  This is the
definition of the spectral bound of the lower-right block, conjugated by the
square root of that block, which carries `σ_{*,0}` to the identity. -/
theorem matLoewnerLE_one_specBound_smul_schurSigmaStar {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E) :
    MatLoewnerLE (1 : Mat d) (specBound E.lowerRight • schurSigmaStar E) := by
  obtain ⟨hRsymm, hRdet, hRRinv⟩ := matSqrt_lowerRight_spec hsymm hpos
  have hRR : matSqrt E.lowerRight * matSqrt E.lowerRight = E.lowerRight :=
    (matSqrt_spec (posSemidef_lowerRight hsymm hpos)).2
  refine (matLoewnerLE_smul_iff_conj hRsymm hRRinv hRdet (specBound E.lowerRight)).2 ?_
  rw [Matrix.mul_one, hRR]
  exact matLoewnerLE_specBound_smul_one _

/-! ## The conclusion -/

/-- **The aspect ratio is at least one under the Schur ordering.**  For a
symmetric positive definite doubled block whose two symmetric Schur blocks are
ordered, `σ_* ≤ σ`, the reference aspect ratio `Π` of `e.reference.aspect.ratio`
satisfies `1 ≤ Π`.

The hypothesis cannot be dropped: the doubled dilation by `c` has `σ = c · I`,
`σ_* = c⁻¹ · I` and `Π = c²`, so `Π < 1` exactly when the ordering fails.  It is
also not vacuous nor too strong: at `c = 1` the ordering holds with equality and
`Π = 1`, so the bound is attained. -/
theorem one_le_aspectRatio_of_schurSigmaStar_le [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E)
    (horder : MatLoewnerLE (schurSigmaStar E) (schurSigma E)) :
    1 ≤ aspectRatio E := by
  have hchain : MatLoewnerLE (1 : Mat d)
      ((specBound E.lowerRight * bigLambdaRef E) • (1 : Mat d)) := by
    have hstep := (matLoewnerLE_one_specBound_smul_schurSigmaStar hsymm hpos).trans
      (matLoewnerLE_smul (specBound_nonneg _)
        (horder.trans (matLoewnerLE_schurSigma_bigLambdaRef_smul_one hpos)))
    rwa [smul_smul] at hstep
  obtain ⟨e, he⟩ := exists_vecNormSq_eq_one (d := d)
  have hq := hchain e
  rw [vecDot_matVecMul_one, vecDot_matVecMul_smul_one, he] at hq
  rw [aspectRatio_eq_bigLambdaRef_mul_specBound, mul_comm]
  linarith only [hq]

end

end HighContrast
end HCPolySupport
