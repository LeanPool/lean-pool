/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.AffineAdaptedCellResponseParentRow
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedOuterScaleFubini

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.AffineAdaptedCellResponseFillingSummable

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Summability of the adapted-target filling row

The codimension-one filling weight is summable against the normalized
reference response row.  This removes the last conditional summability
premise from the affine adapted-cell response comparison.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The response row of an enclosing normalized-root parent is summable after
multiplication by the general adapted-filling weights. -/
theorem summable_normalizedRoot_adaptedTarget_enclosingParentRow
    [NeZero d] {s : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2)
    (abar : Mat d)
    (aRef : Book.Ch03.CoeffFamily d)
    {p : Mat d} (n j M : ℤ) (hnM : n ≤ M) :
    Summable (fun u : ℕ ↦
      (if u = 0 then 1 else
        6 * (d : ℝ) * Real.sqrt d *
          ‖p⁻¹ * Selection.normalizedRoot (symmPart abar)‖ *
          (3 : ℝ) ^ ((n - (u : ℤ)) - j)) *
        Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          (originCube d M) (n - (u : ℤ)) aRef (1 : Mat d)) := by
  let G : ℕ := (M - n).toNat
  have hG : (G : ℤ) = M - n := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hnM)
  let A : ℕ → ℝ := fun k ↦
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
      (originCube d M) (M - (k : ℤ)) aRef (1 : Mat d)
  have hA0 : ∀ k, 0 ≤ A k := by
    intro k
    exact Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg
      (originCube d M) (by simp only [originCube]; omega) aRef (1 : Mat d)
  have hA : Summable (fun k : ℕ ↦
      Book.Ch02.geometricWeight s 2 k * A k) := by
    simpa only [A, originCube] using
      Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        (originCube d M) aRef (1 : Mat d) hs
  let C : ℝ :=
    6 * (d : ℝ) * Real.sqrt d *
      ‖p⁻¹ * Selection.normalizedRoot (symmPart abar)‖ *
      (3 : ℝ) ^ (n - j)
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hbase : Summable (fun u : ℕ ↦
      (C * (3 : ℝ) ^ (-(u : ℤ))) * A (G + u)) :=
    by
      simpa only [zero_add] using
        (Transport.summable_boundaryConvolution_shift_and_tsum_le
          hs hsHalf hC0 G A hA0 hA).1 0
  rw [← summable_nat_add_iff 1]
  refine ((summable_nat_add_iff 1).2 hbase).congr ?_
  intro u
  have hpos : u + 1 ≠ 0 := Nat.succ_ne_zero u
  have hscale : M - ((G : ℤ) + ((u : ℤ) + 1)) =
      n - ((u : ℤ) + 1) := by
    rw [hG]
    ring
  have hpow : (3 : ℝ) ^ (n - j) *
      (3 : ℝ) ^ (-((u : ℤ) + 1)) =
        (3 : ℝ) ^ ((n - ((u : ℤ) + 1)) - j) := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  simp only [hpos, ite_false, A, C, Nat.cast_add, Nat.cast_one]
  rw [hscale]
  rw [← hpow]
  ring

/-- The normalized-reference response comparison on an arbitrary adapted
target has no remaining summability premise. -/
theorem exists_normalizedRootLoads_adaptedTarget_le_enclosingParentRow_summable
    [NeZero d] {s : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2)
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (t : ℤ)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ R : TriadicCube d,
      (aRef.coeffOn R).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField)
    {p : Mat d} (hp : p.PosDef) (n j M : ℤ) (hnM : n ≤ M) (y : Vec d)
    (hEnclose : adaptedCellTranslate p j y ⊆
      adaptedCell (Selection.normalizedRoot (symmPart abar)) M)
    (e : FullBlockVec d) (he : Book.Ch02.fullBlockVecNormSq e = 1) :
    ∃ (P Q : BlockVec d) (Z : ℤ → Finset (Fin d → ℤ)),
      normalizedReferencePrimalLoad abar P = ofFullBlockVec e ∧
      normalizedReferenceDualLoad abar Q = ofFullBlockVec e ∧
      (∀ r, ↑(Z r) = Transport.fillingIndex (Selection.normalizedRoot (symmPart abar)) n
        (adaptedCellTranslate p j y) r) ∧
      Transport.coeffSpaceDoubledResponse (adaptedCellTranslate p j y) a P Q ≤
        ∑' u : ℕ,
          (if u = 0 then 1 else
            6 * (d : ℝ) * Real.sqrt d *
              ‖p⁻¹ * Selection.normalizedRoot (symmPart abar)‖ *
              (3 : ℝ) ^ ((n - (u : ℤ)) - j)) *
            Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
              (originCube d M) (n - (u : ℤ)) aRef (1 : Mat d) := by
  obtain ⟨P, Q, Z, hP, hQ, hZ, hcompare⟩ :=
    exists_normalizedRootLoads_adaptedTarget_le_enclosingParentRow
      a abar hS t aRef haRef hp n j M hnM y hEnclose e he
  refine ⟨P, Q, Z, hP, hQ, hZ, hcompare ?_⟩
  exact summable_normalizedRoot_adaptedTarget_enclosingParentRow
    hs hsHalf abar aRef n j M hnM

end

end RowSupply
end HighContrast
end HCPolySupport
