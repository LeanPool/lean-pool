/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.GeneralAdaptedCellFillingDescendants

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.AffineAdaptedCellResponseParentRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Adapted-target response priced by one reference parent row

An enclosing exact normalized-root parent turns every response maximum in the
general filling into the corresponding descendant maximum of that one parent.
Thus the only series left at this level is the certificate's own reference
response row multiplied by the explicit filling weights.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The doubled response on an arbitrary adapted target is controlled by the
descendant-response row of one enclosing exact normalized-root parent. -/
theorem exists_normalizedRootLoads_adaptedTarget_le_enclosingParentRow
    [NeZero d] (a : CoeffSpace d) (abar : Mat d)
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
      (Summable (fun u : ℕ ↦
        (if u = 0 then 1 else
          6 * (d : ℝ) * Real.sqrt d *
            ‖p⁻¹ * Selection.normalizedRoot (symmPart abar)‖ *
            (3 : ℝ) ^ ((n - (u : ℤ)) - j)) *
          Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
            (originCube d M) (n - (u : ℤ)) aRef (1 : Mat d)) →
        Transport.coeffSpaceDoubledResponse (adaptedCellTranslate p j y) a P Q ≤
          ∑' u : ℕ,
            (if u = 0 then 1 else
              6 * (d : ℝ) * Real.sqrt d *
                ‖p⁻¹ * Selection.normalizedRoot (symmPart abar)‖ *
                (3 : ℝ) ^ ((n - (u : ℤ)) - j)) *
              Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
                (originCube d M) (n - (u : ℤ)) aRef (1 : Mat d)) := by
  let q : Mat d := Selection.normalizedRoot (symmPart abar)
  let hq : q.PosDef := normalizedRoot_posDef_of_posDef hS
  obtain ⟨P, Q, Z, hP, hQ, hZ, haggregate⟩ :=
    exists_normalizedRootLoads_adaptedTarget_doubledResponse_le_tsum
      a abar hS t aRef haRef hp n j y e he
  refine ⟨P, Q, Z, hP, hQ, hZ, ?_⟩
  intro hsum
  let B : ℤ → ℝ := fun r ↦
    if r ≤ M then
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
        (originCube d M) r aRef (1 : Mat d)
    else 0
  have hB0 : ∀ r, 0 ≤ B r := by
    intro r
    by_cases hr : r ≤ M
    · rw [show B r = Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          (originCube d M) r aRef (1 : Mat d) by simp only [B, ite_eq_left hr]]
      exact Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg
        (originCube d M) hr aRef (1 : Mat d)
    · simp only [B, ite_eq_right hr, le_rfl]
  have hmax : ∀ (u : ℕ) (w : Fin d → ℤ), w ∈ Z (n - (u : ℤ)) →
      Book.Ch02.normalizedBlockResponseMax
          (translateCube w (originCube d (n - (u : ℤ)))) aRef (1 : Mat d) ≤
        B (n - (u : ℤ)) := by
    intro u w hw
    have hscale : n - (u : ℤ) ≤ M := by omega
    have hdesc : translateCube w (originCube d (n - (u : ℤ))) ∈
        descendantsAtScale (originCube d M) (n - (u : ℤ)) := by
      apply translateCube_mem_descendantsAtScale_originCube_of_mem_adaptedTarget_filling
        hq hnM hZ hEnclose hw
    simpa only [B, ite_eq_left hscale] using
      Book.Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
        aRef (1 : Mat d) hdesc
  have hB_at (u : ℕ) : B (n - (u : ℤ)) =
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
        (originCube d M) (n - (u : ℤ)) aRef (1 : Mat d) := by
    have hscale : n - (u : ℤ) ≤ M := by omega
    simp only [B, ite_eq_left hscale]
  have hsumB : Summable (fun u : ℕ ↦
      (if u = 0 then 1 else
        6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ *
          (3 : ℝ) ^ ((n - (u : ℤ)) - j)) * B (n - (u : ℤ))) := by
    simpa only [hB_at, q] using hsum
  have hout := haggregate B hB0 hmax hsumB
  simpa only [hB_at, q] using hout

end

end RowSupply
end HighContrast
end HCPolySupport
