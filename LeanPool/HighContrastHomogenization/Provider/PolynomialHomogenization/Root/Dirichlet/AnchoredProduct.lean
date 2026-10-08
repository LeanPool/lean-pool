/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrameExponentFold
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.PrintCellAnchoredObservationResponse
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.CellAnchoredPhysicalFluxFrameAlgebra

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.Dirichlet.AnchoredProduct

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The anchored product

Anchoring the response bound at the observation cell multiplies it by the
cell's own scale factor.  In the parent-anchored response formula the cell index
enters only through the difference `M - K_i`, so the anchoring cancels it
exactly: the anchored product does not depend on the cell at all, and its whole
scale content is the frame exponent `(s - kappa) M + kappa L`.

That cancellation is what makes the frame exponent the only place the
eccentricity can enter, and hence what makes the fold of the previous modules
the whole of the repair.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply


noncomputable section

variable {d : ℕ}

/-- **The anchored product is cell-free.**  The observation cell's scale factor
cancels the cell index in the parent-anchored response formula, leaving the
frame exponent. -/
theorem printCellScaleFactor_mul_responseBound_eq
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    {s deltaScaled Cresponse kappaRate : ℝ} {M : ℤ} {L : ℕ}
    (responseBound : system.CellIndex → ℝ)
    (hresponseFormula : ∀ i, responseBound i =
      Cresponse *
        Real.rpow (3 : ℝ)
          (s * ((M : ℝ) -
            (((ruledObservationCube system i).scale : ℤ) : ℝ))) *
        Real.sqrt deltaScaled *
        Real.rpow (3 : ℝ) (-kappaRate * ((M : ℝ) - ((L : ℕ) : ℝ))))
    (i : system.CellIndex) :
    printCellScaleFactor (ruledObservationCube system i) s *
        responseBound i =
      (Cresponse * Real.sqrt deltaScaled) *
        Real.rpow (3 : ℝ)
          ((s - kappaRate) * (M : ℝ) + kappaRate * ((L : ℕ) : ℝ)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hrw : ∀ e : ℝ, Real.rpow (3 : ℝ) e = (3 : ℝ) ^ e := fun _ => rfl
  have hcombine :
      (3 : ℝ) ^ (s * (((ruledObservationCube system i).scale : ℤ) : ℝ)) *
          (3 : ℝ) ^ (s * ((M : ℝ) -
            (((ruledObservationCube system i).scale : ℤ) : ℝ))) *
          (3 : ℝ) ^ (-kappaRate * ((M : ℝ) - ((L : ℕ) : ℝ))) =
        (3 : ℝ) ^ ((s - kappaRate) * (M : ℝ) +
          kappaRate * ((L : ℕ) : ℝ)) := by
    rw [← Real.rpow_add h3, ← Real.rpow_add h3]
    congr 1
    ring
  simp only [hresponseFormula i, printCellScaleFactor, hrw]
  rw [← hcombine]
  ring

end

end RowSupply
end HighContrast
end HCPolySupport
