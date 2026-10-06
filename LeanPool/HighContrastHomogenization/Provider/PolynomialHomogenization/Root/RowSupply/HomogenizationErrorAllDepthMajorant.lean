/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.Finite

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.HomogenizationErrorAllDepthMajorant

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# All-depth majorants for the cube homogenization error

The squared `p = infinity`, `q = 2` homogenization error is the weighted sum
of the descendant response maxima.  Consequently, any summable pointwise
majorant for that row gives a majorant for the complete error.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Book.Ch02

noncomputable section

variable {d : ℕ}

/-- A summable pointwise majorant for every descendant response row controls
the complete squared homogenization error. -/
theorem homogenizationErrorOnCube_infinity_two_sq_le_tsum_of_max_le
    [NeZero d] (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (a : TriadicCoeffFamily d) (a0 : Mat d) (B : ℕ → ℝ)
    (hB : Summable (fun l : ℕ ↦ Book.Ch02.geometricWeight s 2 l * B l))
    (hmax : ∀ l : ℕ,
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          Q (Q.scale - (l : ℤ)) a a0 ≤ B l) :
    Book.Ch02.HomogenizationErrorOnCube
        Q s .infinity (.finite 2) a a0 ^ 2 ≤
      ∑' l : ℕ, Book.Ch02.geometricWeight s 2 l * B l := by
  have hresponse : Summable (fun l : ℕ ↦
      Book.Ch02.geometricWeight s 2 l *
        Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          Q (Q.scale - (l : ℤ)) a a0) := by
    simpa using
      Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        Q a a0 hs
  have hterm : ∀ l : ℕ,
      Book.Ch02.geometricWeight s 2 l *
          Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
            Q (Q.scale - (l : ℤ)) a a0 ≤
        Book.Ch02.geometricWeight s 2 l * B l := by
    intro l
    have hweight : 0 ≤ Book.Ch02.geometricWeight s 2 l := by
      simpa [Book.Ch02.geometricWeight_eq_old] using
        (HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) l
          (by positivity : 0 ≤ s * (2 : ℝ)))
    exact mul_le_mul_of_nonneg_left (hmax l) hweight
  rw [Book.Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs a a0]
  exact hresponse.tsum_le_tsum hterm hB

/-- The corresponding unsquared estimate, in the form consumed by response
pricing, is obtained by taking the nonnegative square root. -/
theorem homogenizationErrorOnCube_infinity_two_le_sqrt_tsum_of_max_le
    [NeZero d] (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (a : TriadicCoeffFamily d) (a0 : Mat d) (B : ℕ → ℝ)
    (hB : Summable (fun l : ℕ ↦ Book.Ch02.geometricWeight s 2 l * B l))
    (hmax : ∀ l : ℕ,
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
          Q (Q.scale - (l : ℤ)) a a0 ≤ B l) :
    Book.Ch02.HomogenizationErrorOnCube
        Q s .infinity (.finite 2) a a0 ≤
      Real.sqrt (∑' l : ℕ, Book.Ch02.geometricWeight s 2 l * B l) := by
  let E : ℝ := Book.Ch02.HomogenizationErrorOnCube
    Q s .infinity (.finite 2) a a0
  have hE : 0 ≤ E := by
    dsimp only [E]
    unfold Book.Ch02.HomogenizationErrorOnCube
      Book.Ch02.HomogenizationError Book.Ch02.HomogenizationErrorFinite
    exact Real.rpow_nonneg
      (tsum_nonneg fun l ↦ mul_nonneg
        (by
          simpa [Book.Ch02.geometricWeight_eq_old] using
            (HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) l
              (by positivity : 0 ≤ s * (2 : ℝ))))
        (Real.rpow_nonneg
          (Book.Ch02.scaleResponseAtScale_infinity_nonneg Q (by omega) a a0) _)) _
  have hsq : E ^ 2 ≤
      ∑' l : ℕ, Book.Ch02.geometricWeight s 2 l * B l := by
    exact homogenizationErrorOnCube_infinity_two_sq_le_tsum_of_max_le
      Q hs a a0 B hB hmax
  calc
    E = Real.sqrt (E ^ 2) := (Real.sqrt_sq hE).symm
    _ ≤ Real.sqrt (∑' l : ℕ,
        Book.Ch02.geometricWeight s 2 l * B l) := Real.sqrt_le_sqrt hsq

end

end RowSupply
end HighContrast
end HCPolySupport
