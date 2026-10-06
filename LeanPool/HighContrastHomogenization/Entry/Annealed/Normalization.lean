/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedCellFoundations
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.DriftAdvance

/-!
# High-contrast homogenization: Entry.Annealed.Normalization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Actual expectation and identity normalization

Finite entrywise expectations commute with deterministic matrix multiplication, so the
entrywise integral of the actual coarse block is the annealed block and the entrywise
integral of the normalized actual block is the normalized annealed mean.  Reading the
identity normalizer at one generation fixes the diagonal normalized mean at the doubled
identity; the actual block is then centered on its annealed mean, its centered fluctuations
have all finite Schatten moments, and a positive actual normalizer keeps the normalized
block positive definite.  These normalization identities are what the parent--child
recurrence `p.fixed.geometry.parent.child.recurrence` applies to its normalized fluctuation.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedMean annealedBlock
  blockMatEntry_annealedBlock blockSub coarseBlock normalizedBlock
  toFullBlockMat_eq_blockMatEntry)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory Geometry

noncomputable section

/-- Each entry remains integrable after left and right deterministic multiplication. -/
theorem integrable_fullBlock_mul {d : ℕ} {P : Measure (CoeffSpace d)}
    {A : CoeffSpace d → BlockMat d}
    (hA : ∀ α β, Integrable (fun a => blockMatEntry (A a) α β) P)
    (B C : FullBlockMat d) (α β : BlockCoord d) :
    Integrable (fun a => (B * toFullBlockMat (A a) * C) α β) P := by
  simp only [Matrix.mul_apply, toFullBlockMat_eq_blockMatEntry]
  exact integrable_finsetSum _ fun i _ =>
    (integrable_finsetSum _ fun l _ => (hA l i).const_mul (B α l)).mul_const (C i β)

/-- Actual finite entrywise expectation commutes with deterministic matrix products. -/
theorem integral_fullBlock_mul {d : ℕ} {P : Measure (CoeffSpace d)}
    {A : CoeffSpace d → BlockMat d}
    (hA : ∀ α β, Integrable (fun a => blockMatEntry (A a) α β) P)
    (B C : FullBlockMat d) :
    (fun α β => ∫ a, (B * toFullBlockMat (A a) * C) α β ∂P) =
      B * Matrix.of (fun α β => ∫ a, blockMatEntry (A a) α β ∂P) * C := by
  funext α β
  simp only [Matrix.mul_apply, toFullBlockMat_eq_blockMatEntry]
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_finsetSum _ fun l _ => (hA l i).const_mul (B α l)).mul_const (C i β))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_const]
  congr 1
  rw [integral_finsetSum _ (fun l _ => (hA l i).const_mul (B α l))]
  simp only [integral_const_mul, Matrix.of_apply]

/-- The annealed matrix is exactly the entrywise integral in full coordinates. -/
theorem fullBlock_integral_coarseBlock {d : ℕ} (P : Measure (CoeffSpace d))
    (U : Set (Vec d)) :
    (fun α β => ∫ a, blockMatEntry (coarseBlock U a) α β ∂P) =
      toFullBlockMat (annealedBlock P U) := by
  funext α β
  exact (blockMatEntry_annealedBlock P U α β).symm

/-- The expectation of the normalized actual block is its normalized actual mean. -/
theorem integral_normalizedBlock_coarseBlock {d : ℕ} {P : Measure (CoeffSpace d)}
    {U : Set (Vec d)} (hU : HasIntegrableCoarseBlock P U) (R : BlockMat d) :
    ofFullBlockMat (fun α β => ∫ a,
      blockMatEntry (normalizedBlock (coarseBlock U a) R) α β ∂P) =
      normalizedBlock (annealedBlock P U) R := by
  simp only [normalizedBlock, blockMatEntry_ofFullBlockMat]
  rw [integral_fullBlock_mul hU, fullBlock_integral_coarseBlock]
  rfl

/-- O8: the actual diagonal normalized mean is the doubled identity. -/
theorem normalizedMean_self (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j : ℤ) :
    relMean P (explicitRoundedGrid jStar m) j j = Book.Ch02.blockIdentity d := by
  exact Multiscale.normalizedBlock_self_of_posDef _
    (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm j)

/-- The diagonal normalized coarse block has identity expectation under the actual law. -/
theorem integral_normalizedBlock_self (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j : ℤ) :
    ofFullBlockMat (fun α β => ∫ a, blockMatEntry
      (normalizedBlock (coarseBlock (adaptedCell (explicitRoundedGrid jStar m) j) a)
        (adaptedMean P (explicitRoundedGrid jStar m) j)) α β ∂P) = Book.Ch02.blockIdentity d := by
  have hint : HasIntegrableCoarseBlock P (adaptedCell (explicitRoundedGrid jStar m) j) := by
    simpa [adaptedCellTranslate] using hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S
      hstat hdag jStar hjStar m hm j 0
  rw [integral_normalizedBlock_coarseBlock hint]
  exact normalizedMean_self d hd P γ E Ψ K S hstat hdag jStar hjStar m hm j

/-- Centered normalized actual coarse blocks have zero entrywise expectation. -/
theorem integral_centered_normalized_coarseBlock {d : ℕ} {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {U : Set (Vec d)} (hU : HasIntegrableCoarseBlock P U)
    (R : BlockMat d) :
    ofFullBlockMat (fun α β => ∫ a, blockMatEntry
      (normalizedBlock (blockSub (coarseBlock U a) (annealedBlock P U)) R) α β ∂P) =
      ofFullBlockMat (0 : FullBlockMat d) := by
  have hsub (A B : BlockMat d) (α β : BlockCoord d) :
      blockMatEntry (blockSub A B) α β = blockMatEntry A α β - blockMatEntry B α β := by
    cases α <;> cases β <;> rfl
  have hc (α β : BlockCoord d) : Integrable (fun a =>
      blockMatEntry (blockSub (coarseBlock U a) (annealedBlock P U)) α β) P := by
    simpa only [hsub] using! (hU α β).sub (integrable_const _)
  have he : Matrix.of (fun α β => ∫ a,
      blockMatEntry (blockSub (coarseBlock U a) (annealedBlock P U)) α β ∂P) =
      (0 : FullBlockMat d) := by
    ext α β
    simp only [Matrix.of_apply, hsub]
    rw [integral_sub (hU α β) (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul,
      blockMatEntry_annealedBlock, sub_self, Matrix.zero_apply]
  simp only [normalizedBlock, blockMatEntry_ofFullBlockMat]
  rw [integral_fullBlock_mul hc, he, mul_zero, zero_mul]

/-- Every actual fluctuation has all finite Schatten moments, at arbitrary real centers. -/
theorem memLqSchatten_normalizedFluctuation (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j k : ℤ) (y : Vec d) (N : ℝ) (hN : 1 ≤ N) :
    SchattenMemLp P N (normalizedFluctuation P (explicitRoundedGrid jStar m) j k y) := by
  have hA := Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag
    jStar hjStar m hm j y N hN
  have hM := Analysis.memLqSchatten_const P hN (adaptedMean P (explicitRoundedGrid jStar m) j)
    (isSymmetricBlockMat_annealedBlock P _)
  exact Source.memLqSchatten_normalizedBlock (hA.sub hM hN) hN _

/-- Invertible inverse-root congruence preserves full strict positivity. -/
theorem normalizedBlock_posDef {d : ℕ} (F G : BlockMat d)
    (hF : (toFullBlockMat F).PosDef) (hG : (toFullBlockMat G).PosDef) :
    (toFullBlockMat (normalizedBlock F G)).PosDef := by
  have hS := Multiscale.matSqrt_inv_posDef_full hG
  simpa only [normalizedBlock, toFullBlockMat_ofFullBlockMat, hS.isHermitian.eq] using
    hF.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hS.isUnit)

end

end HCPolySupport.HighContrast.Annealed
