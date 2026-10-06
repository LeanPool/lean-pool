/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.GeneralAdaptedCellDoubledResponseAggregation
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedNormalizedRootCellResponseMax

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.AffineAdaptedCellResponseFilling

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalized-reference response on an affine adapted target

The inverse physical loads attached to a unit normalized-reference load work
on every exact normalized-root cell.  Combining that available cell estimate
with the general maximal filling carries the response to any positive-
definite adapted target, including targets produced by a bounded scalar
dilation and a matrix gauge.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- A unit identity-reference load admits physical inverse loads whose doubled
response on an arbitrary adapted target is controlled by any summable
row-majorant for the exact normalized-root response maxima.  The target grid
`p` is unrestricted apart from positive definiteness; hence residual scalar
dilations and the square-root gauge enter only through `‖p⁻¹ q‖`. -/
theorem exists_normalizedRootLoads_adaptedTarget_doubledResponse_le_tsum
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
    {p : Mat d} (hp : p.PosDef) (n j : ℤ) (y : Vec d)
    (e : FullBlockVec d) (he : Book.Ch02.fullBlockVecNormSq e = 1) :
    ∃ (P Q : BlockVec d) (Z : ℤ → Finset (Fin d → ℤ)),
      normalizedReferencePrimalLoad abar P = ofFullBlockVec e ∧
      normalizedReferenceDualLoad abar Q = ofFullBlockVec e ∧
      (∀ r, ↑(Z r) = Transport.fillingIndex (Selection.normalizedRoot (symmPart abar)) n
        (adaptedCellTranslate p j y) r) ∧
      ∀ B : ℤ → ℝ,
        (∀ r, 0 ≤ B r) →
        (∀ (u : ℕ) (w : Fin d → ℤ), w ∈ Z (n - (u : ℤ)) →
          Book.Ch02.normalizedBlockResponseMax
              (translateCube w (originCube d (n - (u : ℤ))))
              aRef (1 : Mat d) ≤ B (n - (u : ℤ))) →
        Summable (fun u : ℕ ↦
          (if u = 0 then 1 else
            6 * (d : ℝ) * Real.sqrt d *
              ‖p⁻¹ * Selection.normalizedRoot (symmPart abar)‖ *
              (3 : ℝ) ^ ((n - (u : ℤ)) - j)) * B (n - (u : ℤ))) →
        Transport.coeffSpaceDoubledResponse (adaptedCellTranslate p j y) a P Q ≤
          ∑' u : ℕ,
            (if u = 0 then 1 else
              6 * (d : ℝ) * Real.sqrt d *
                ‖p⁻¹ * Selection.normalizedRoot (symmPart abar)‖ *
                (3 : ℝ) ^ ((n - (u : ℤ)) - j)) * B (n - (u : ℤ)) := by
  obtain ⟨P, Q, hP, hQ, hcell⟩ :=
    exists_normalizedRootCell_doubledResponseJ_le_normalizedBlockResponseMax
      a abar hS t aRef haRef e he
  let hq := normalizedRoot_posDef_of_posDef hS
  obtain ⟨Z, hZ, haggregate⟩ :=
    exists_coeffSpaceDoubledResponse_adaptedCellTranslate_le_tsum_rowMajorant
      hp hq n j y a P Q
  refine ⟨P, Q, Z, hP, hQ, hZ, ?_⟩
  intro B hB0 hmax hsum
  apply haggregate B hB0
  · intro u w hw
    exact (hcell (n - (u : ℤ)) w).trans (hmax u w hw)
  · exact hsum

end

end RowSupply
end HighContrast
end HCPolySupport
