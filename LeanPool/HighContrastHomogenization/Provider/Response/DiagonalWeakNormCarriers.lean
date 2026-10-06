/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AlignedIdentities
public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNormAPI
public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNormCellAverage
public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNormGeometric
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationSize
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellPositivity

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormCarriers

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Carriers for the diagonal adapted-cube weak norm

This file records the scalar and matrix quantities of the weak-norm estimate for
the optimizer state used in `p.response.transfer`, from its normalization
prefactors to its recent-scale sums.  Infinite maxima take values in `ℝ≥0∞`; all
recent-scale sums remain finite real sums.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Metric and load factors -/

/-- The metric comparison factor
`K_{M,E} = |M₀⁻¹ᐟ² E M₀⁻¹ᐟ²|¹ᐟ²`, one of the normalization prefactors of the
weak-norm estimate. -/
@[expose]
def diagonalWeakMetricFactor (m0 : Mat d) (E : BlockMat d) : ℝ :=
  Real.sqrt (blockSize E (blockDiag m0 m0⁻¹))

/-- The defining equation for `K_{M,E}`. -/
theorem diagonalWeakMetricFactor_eq (m0 : Mat d) (E : BlockMat d) :
    diagonalWeakMetricFactor m0 E =
      Real.sqrt (blockSize E (blockDiag m0 m0⁻¹)) := rfl

/-- The primal load factor
`L_E⁻(p,q) = |E¹ᐟ²(-p,q)|`, the first of the two load sizes of the weak-norm
estimate. -/
@[expose]
def diagonalWeakLoadMinus (E : BlockMat d) (p q : Vec d) : ℝ :=
  Real.sqrt
    (blockVecDot ((-p, q) : BlockVec d)
      (blockMatVecMul E ((-p, q) : BlockVec d)))

/-- The defining equation for `L_E⁻`. -/
theorem diagonalWeakLoadMinus_eq (E : BlockMat d) (p q : Vec d) :
    diagonalWeakLoadMinus E p q =
      Real.sqrt
        (blockVecDot ((-p, q) : BlockVec d)
          (blockMatVecMul E ((-p, q) : BlockVec d))) := rfl

/-- The adjoint load factor
`L_E⁺(p,q) = |E¹ᐟ²(p,q)|`, the second of the two load sizes of the weak-norm
estimate. -/
@[expose]
def diagonalWeakLoadPlus (E : BlockMat d) (p q : Vec d) : ℝ :=
  Real.sqrt
    (blockVecDot ((p, q) : BlockVec d)
      (blockMatVecMul E ((p, q) : BlockVec d)))

/-- The defining equation for `L_E⁺`. -/
theorem diagonalWeakLoadPlus_eq (E : BlockMat d) (p q : Vec d) :
    diagonalWeakLoadPlus E p q =
      Real.sqrt
        (blockVecDot ((p, q) : BlockVec d)
          (blockMatVecMul E ((p, q) : BlockVec d))) := rfl

theorem diagonalWeakMetricFactor_nonneg (m0 : Mat d) (E : BlockMat d) :
    0 ≤ diagonalWeakMetricFactor m0 E :=
  Real.sqrt_nonneg _

theorem diagonalWeakLoadMinus_nonneg (E : BlockMat d) (p q : Vec d) :
    0 ≤ diagonalWeakLoadMinus E p q :=
  Real.sqrt_nonneg _

theorem diagonalWeakLoadPlus_nonneg (E : BlockMat d) (p q : Vec d) :
    0 ≤ diagonalWeakLoadPlus E p q :=
  Real.sqrt_nonneg _

/-! ## The all-scale maximum -/

/-- The all-scale maximum `ℳ_{t,ρ}(E)`, the weighted maximum of the positive
parts of the normalized block defects over the lower generations.  The supremum
ranges over every integer `k ≤ t`, so its fail-closed value is extended real. -/
@[expose]
def diagonalWeakMaximum (rho : ℝ) (q : Mat d) (t : ℤ)
    (E : BlockMat d) (a : CoeffSpace d) : ℝ≥0∞ :=
  ⨆ (k : ℤ) (_ : k ≤ t) (w : Fin d → ℤ)
      (_ : w ∈ alignedIndex q k t),
    ENNReal.ofReal
      ((3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) *
        blockExcess (adaptedResponse q k w a) E)

/-- The defining equation for the all-scale maximum. -/
theorem diagonalWeakMaximum_eq (rho : ℝ) (q : Mat d) (t : ℤ)
    (E : BlockMat d) (a : CoeffSpace d) :
    diagonalWeakMaximum rho q t E a =
      ⨆ (k : ℤ) (_ : k ≤ t) (w : Fin d → ℤ)
          (_ : w ∈ alignedIndex q k t),
        ENNReal.ofReal
          ((3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) *
            blockExcess (adaptedResponse q k w a) E) := rfl

/-- Every aligned cell term is bounded by the all-scale maximum. -/
theorem weighted_excess_le_diagonalWeakMaximum (rho : ℝ) (q : Mat d)
    (t k : ℤ) (E : BlockMat d) (a : CoeffSpace d) (hkt : k ≤ t)
    (w : Fin d → ℤ) (hw : w ∈ alignedIndex q k t) :
    ENNReal.ofReal
        ((3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) *
          blockExcess (adaptedResponse q k w a) E) ≤
      diagonalWeakMaximum rho q t E a := by
  exact le_iSup_of_le k <| le_iSup_of_le hkt <|
    le_iSup_of_le w <| le_iSup_of_le hw le_rfl

/-! ## Recent defects -/

/-- The recent cell defect `C_{k,t}(E)` of the weak-norm estimate. -/
@[expose]
def diagonalWeakCellDefect (q : Mat d) (k t : ℤ)
    (E : BlockMat d) (a : CoeffSpace d) : ℝ :=
  Real.sqrt
    (avsum (alignedIndex q k t) fun w =>
      blockSize
        (blockSub (adaptedResponse q k w a)
          (coarseBlock (adaptedCell q t) a)) E ^ 2)

/-- The defining equation for `C_{k,t}(E)`. -/
theorem diagonalWeakCellDefect_eq (q : Mat d) (k t : ℤ)
    (E : BlockMat d) (a : CoeffSpace d) :
    diagonalWeakCellDefect q k t E a =
      Real.sqrt
        (avsum (alignedIndex q k t) fun w =>
          blockSize
            (blockSub (adaptedResponse q k w a)
              (coarseBlock (adaptedCell q t) a)) E ^ 2) := rfl

/-- The recent averaged normalized defect `D_{k,t}(E)` of the weak-norm
estimate. -/
@[expose]
def diagonalWeakAverageDefect (q : Mat d) (k t : ℤ)
    (E : BlockMat d) (a : CoeffSpace d) : BlockMat d :=
  ofFullBlockMat
    (((alignedIndex q k t).card : ℝ)⁻¹ •
      ∑ w ∈ alignedIndex q k t,
        toFullBlockMat
          (normalizedBlock
            (blockSub (adaptedResponse q k w a)
              (coarseBlock (adaptedCell q t) a)) E))

/-- The defining equation for `D_{k,t}(E)`. -/
theorem diagonalWeakAverageDefect_eq (q : Mat d) (k t : ℤ)
    (E : BlockMat d) (a : CoeffSpace d) :
    diagonalWeakAverageDefect q k t E a =
      ofFullBlockMat
        (((alignedIndex q k t).card : ℝ)⁻¹ •
          ∑ w ∈ alignedIndex q k t,
            toFullBlockMat
              (normalizedBlock
                (blockSub (adaptedResponse q k w a)
                  (coarseBlock (adaptedCell q t) a)) E)) := rfl

theorem diagonalWeakCellDefect_nonneg (q : Mat d) (k t : ℤ)
    (E : BlockMat d) (a : CoeffSpace d) :
    0 ≤ diagonalWeakCellDefect q k t E a :=
  Real.sqrt_nonneg _

/-! ## Recent finite sums -/

/-- The recent cell sum `𝒰_cell`, the weighted sum of the recent cell defects
over the finite window.  The index `j` represents the scale
`k = t-j`; `range (H+1)` includes both endpoints. -/
@[expose]
def diagonalWeakCellSum (q : Mat d) (t : ℤ) (H : ℕ) (s : ℝ)
    (E : BlockMat d) (a : CoeffSpace d) : ℝ :=
  ∑ j ∈ Finset.range (H + 1),
    (3 : ℝ) ^ (-s * (j : ℝ)) *
      diagonalWeakCellDefect q (t - (j : ℤ)) t E a

/-- The defining equation for `𝒰_cell`. -/
theorem diagonalWeakCellSum_eq (q : Mat d) (t : ℤ) (H : ℕ) (s : ℝ)
    (E : BlockMat d) (a : CoeffSpace d) :
    diagonalWeakCellSum q t H s E a =
      ∑ j ∈ Finset.range (H + 1),
        (3 : ℝ) ^ (-s * (j : ℝ)) *
          diagonalWeakCellDefect q (t - (j : ℤ)) t E a := rfl

/-- The recent averaged-defect sum `𝒰_av`, the weighted sum of the averaged
recent defects over the finite window. -/
@[expose]
def diagonalWeakAverageSum (q : Mat d) (t : ℤ) (H : ℕ) (s rho : ℝ)
    (E : BlockMat d) (a : CoeffSpace d) : ℝ :=
  ∑ j ∈ Finset.range (H + 1),
    (3 : ℝ) ^ (-(s - rho / 2) * (j : ℝ)) *
      Real.sqrt
        (blockSize (diagonalWeakAverageDefect q (t - (j : ℤ)) t E a)
          (blockIdentity d))

/-- The defining equation for `𝒰_av`. -/
theorem diagonalWeakAverageSum_eq (q : Mat d) (t : ℤ) (H : ℕ)
    (s rho : ℝ) (E : BlockMat d) (a : CoeffSpace d) :
    diagonalWeakAverageSum q t H s rho E a =
      ∑ j ∈ Finset.range (H + 1),
        (3 : ℝ) ^ (-(s - rho / 2) * (j : ℝ)) *
          Real.sqrt
            (blockSize (diagonalWeakAverageDefect q (t - (j : ℤ)) t E a)
              (blockIdentity d)) := rfl

theorem diagonalWeakCellSum_nonneg (q : Mat d) (t : ℤ) (H : ℕ) (s : ℝ)
    (E : BlockMat d) (a : CoeffSpace d) :
    0 ≤ diagonalWeakCellSum q t H s E a := by
  refine Finset.sum_nonneg fun j _ => mul_nonneg ?_ ?_
  · exact Real.rpow_nonneg (by norm_num) _
  · exact diagonalWeakCellDefect_nonneg q (t - (j : ℤ)) t E a

theorem diagonalWeakAverageSum_nonneg (q : Mat d) (t : ℤ) (H : ℕ)
    (s rho : ℝ) (E : BlockMat d) (a : CoeffSpace d) :
    0 ≤ diagonalWeakAverageSum q t H s rho E a := by
  refine Finset.sum_nonneg fun _ _ => mul_nonneg ?_ (Real.sqrt_nonneg _)
  exact Real.rpow_nonneg (by norm_num) _

end

end Response
end HighContrast
end HCPolySupport
