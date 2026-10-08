/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileDefectIdentities
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowMeanEstimates

/-!
# High-contrast homogenization: Provider.Response.AnnealedDefectIdentification

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cellwise defects and the response defect

The defect half of a cutoff-defect mean row consumes a family of cell defects
whose normalized average is twice the response defect.  The response defect is
defined as the expectation of a difference of two responses, while the cellwise
data arrives as a difference of two expectations; the two agree once both
responses are integrable.

This module records that identification, the normalized average that follows
from it, and the nonnegativity of each cell defect in the same literal form.
The geometry of the cells enters only through the hypothesis that every cell
carries the same annealed response, which is what the alignment of the grid
supplies.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

open Book.Ch02 MeasureTheory

variable {d : ℕ}

/-! ## Normalized averages of a function that is constant on its index set -/

/-- A normalized average of a function that is constant on the index set is that
constant. -/
theorem avsum_eq_of_forall_eq {ι : Type*} {Z : Finset ι} (hZ : Z.Nonempty)
    {f : ι → ℝ} {c : ℝ} (hf : ∀ z ∈ Z, f z = c) : avsum Z f = c := by
  calc avsum Z f = avsum Z (fun _ => c) := by
        rw [avsum_eq, avsum_eq]
        exact congrArg _ (Finset.sum_congr rfl hf)
    _ = c := avsum_const hZ c

/-! ## The response defect as a difference of expectations -/

/-- **The primal response defect is a difference of expectations.**  The defect
is defined as one expectation of a difference; splitting it needs both responses
to be integrable. -/
theorem profilePrimalResponseDefect_eq_sub_integral (P : Measure (CoeffSpace d))
    {q : Mat d} (hq : q.PosDef) (g : Mat d) (hg : IsSkewMat g) (s t : ℤ)
    (p r : Vec d)
    (hs : Integrable (fun a => responseJ (adaptedDomain hq s)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq s)) p r) P)
    (ht : Integrable (fun a => responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r) P) :
    profilePrimalResponseDefect P hq g hg s t p r =
      (∫ a, responseJ (adaptedDomain hq s)
          ((a.subSkew g hg).coeffOn (adaptedDomain hq s)) p r ∂P) -
        ∫ a, responseJ (adaptedDomain hq t)
          ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r ∂P := by
  rw [profilePrimalResponseDefect_eq]
  exact integral_sub hs ht

/-- The coefficient-transpose response defect as a difference of
expectations. -/
theorem profileAdjointResponseDefect_eq_sub_integral (P : Measure (CoeffSpace d))
    {q : Mat d} (hq : q.PosDef) (g : Mat d) (hg : IsSkewMat g) (s t : ℤ)
    (p r : Vec d)
    (hs : Integrable (fun a => responseJ (adaptedDomain hq s)
      ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq s)) p r) P)
    (ht : Integrable (fun a => responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r) P) :
    profileAdjointResponseDefect P hq g hg s t p r =
      (∫ a, responseJ (adaptedDomain hq s)
          ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq s)) p r ∂P) -
        ∫ a, responseJ (adaptedDomain hq t)
          ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r ∂P := by
  rw [profileAdjointResponseDefect_eq]
  exact integral_sub hs ht

/-! ## The cellwise defects -/

/-! ## The normalized average and the nonnegativity -/

end

end Response
end HighContrast
end HCPolySupport
