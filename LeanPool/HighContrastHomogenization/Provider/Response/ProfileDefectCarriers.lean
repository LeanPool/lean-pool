/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewAdjoint

/-!
# High-contrast homogenization: Provider.Response.ProfileDefectCarriers

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Positive response-defect carriers

The response defects compare the annealed variational values on two adapted
cells after a fixed skew recentering.  The primal and coefficient-transpose
problems retain separate load pairs.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The recentered annealed block `Ê_k = G_gᵀ E_k G_g`. -/
@[expose]
def profileRecenteredMean (P : Measure (CoeffSpace d)) (q g : Mat d)
    (k : ℤ) : BlockMat d :=
  blockMatMul (blockMatTranspose (blockG g))
    (blockMatMul (adaptedMean P q k) (blockG g))

/-- The coefficient-transpose recentered mean `Ê_kᵃᵈ = D Ê_k D`. -/
@[expose]
def profileRecenteredAdjointMean (P : Measure (CoeffSpace d))
    (q g : Mat d) (k : ℤ) : BlockMat d :=
  blockMatMul (blockDiag 1 (-1))
    (blockMatMul (profileRecenteredMean P q g k) (blockDiag 1 (-1)))

/-- The defining equation for the coefficient-transpose recentered mean. -/
theorem profileRecenteredAdjointMean_eq (P : Measure (CoeffSpace d))
    (q g : Mat d) (k : ℤ) :
    profileRecenteredAdjointMean P q g k =
      blockMatMul (blockDiag 1 (-1))
        (blockMatMul (profileRecenteredMean P q g k)
          (blockDiag 1 (-1))) := rfl

/-- The primal positive response defect `τ⁻_{t,s}`. -/
@[expose]
def profilePrimalResponseDefect (P : Measure (CoeffSpace d))
    {q : Mat d} (hq : q.PosDef) (g : Mat d) (hg : IsSkewMat g)
    (s t : ℤ) (p r : Vec d) : ℝ :=
  ∫ a, responseJ (adaptedDomain hq s)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq s)) p r -
    responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r ∂P

/-- The defining equation for `τ⁻_{t,s}`. -/
theorem profilePrimalResponseDefect_eq (P : Measure (CoeffSpace d))
    {q : Mat d} (hq : q.PosDef) (g : Mat d) (hg : IsSkewMat g)
    (s t : ℤ) (p r : Vec d) :
    profilePrimalResponseDefect P hq g hg s t p r =
      ∫ a, responseJ (adaptedDomain hq s)
          ((a.subSkew g hg).coeffOn (adaptedDomain hq s)) p r -
        responseJ (adaptedDomain hq t)
          ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r ∂P := rfl

/-- The coefficient-transpose positive response defect `τ⁺_{t,s}`. -/
@[expose]
def profileAdjointResponseDefect (P : Measure (CoeffSpace d))
    {q : Mat d} (hq : q.PosDef) (g : Mat d) (hg : IsSkewMat g)
    (s t : ℤ) (p r : Vec d) : ℝ :=
  ∫ a, responseJ (adaptedDomain hq s)
      ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq s)) p r -
    responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r ∂P

/-- The defining equation for `τ⁺_{t,s}`. -/
theorem profileAdjointResponseDefect_eq (P : Measure (CoeffSpace d))
    {q : Mat d} (hq : q.PosDef) (g : Mat d) (hg : IsSkewMat g)
    (s t : ℤ) (p r : Vec d) :
    profileAdjointResponseDefect P hq g hg s t p r =
      ∫ a, responseJ (adaptedDomain hq s)
          ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq s)) p r -
        responseJ (adaptedDomain hq t)
          ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r ∂P := rfl

end

end HCPolySupport.HighContrast.Response
