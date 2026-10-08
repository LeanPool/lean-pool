/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.ParentChildRecurrence
public import LeanPool.HighContrastHomogenization.Entry.MatrixAveraging

/-!
# High-contrast homogenization: Entry.ParentChildRecurrence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Exact parent–child recurrence

Under the standing ellipticity threshold, the localised quotient Schatten norm of the
normalised fluctuation at the parent scale is bounded by its value at the child scale,
multiplied by the exponential of the determinant increment and the two printed scale
factors, with the source constant of the matrix-averaging statement. This is the exact
parent–child recurrence of `p.fixed.geometry.parent.child.recurrence`, with the mean
positive-definiteness and finite-moment premises discharged from the two printed constants
without slack.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Entry
open MeasureTheory

/-- The exact printed recurrence, near `p.fixed.geometry.parent.child.recurrence`. -/
theorem fixed_geometry_parent_child_recurrence
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
        (_hP : IsProbabilityMeasure P) (_hstat : IsStationaryLaw P) (_hunit : IsUnitRangeLaw P)
        (_hell : CoarseEllipticityDagger P γ E Ψ K S)
        (N : ℕ) (_hN : 2 ≤ N) (_hNeven : Even N)
        (jStar : ℕ) (_hj : 2 * d ≤ 3 ^ jStar)
        (_hsrc : ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ))
        (m : Mat d) (_hm : m.PosDef)
        (j h : ℤ) (_hjgen : (jStar : ℤ) ≤ j) (_hh : 1 ≤ h),
        lqSchattenNorm P (N : ℝ)
            (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar m) (j + h)) ≤
          (N : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * (1 + (2 * (d : ℝ)) ^ ((N : ℝ))⁻¹) *
                (3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ)) *
                Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar m) j (j + h)) *
              lqSchattenNorm P (N : ℝ)
                (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar m) j) +
            2 * (1 + (d : ℝ) ^ (1 - ((N : ℝ))⁻¹)) *
                Real.exp
                  ((1 - ((N : ℝ))⁻¹) *
                    detIncrement P (Geometry.explicitRoundedGrid jStar m) j (j + h)) *
                (Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar m) j (j + h)) - 1) ^
                  ((N : ℝ))⁻¹ := by
  obtain ⟨Csrc, hCsrc, havg⟩ := fixed_geometry_matrix_averaging d hd γ hγ
  refine ⟨Csrc, hCsrc, ?_⟩
  intro P E Ψ K S hP hstat hunit hell N hN hNeven jStar hj hsrc m hm j h hjgen hh
  apply Annealed.parent_child_recurrence_of_averaging d hd P hP γ E Ψ K S hstat hell
    N hN jStar hj m hm j h hjgen hh
  dsimp only
  intro R hRsymm hRpos
  exact havg P E Ψ K S hP hstat hunit hell N hN hNeven jStar hj hsrc m hm j hjgen
    (Annealed.alignedChildren (Geometry.explicitRoundedGrid jStar m) j h.toNat)
    (Annealed.alignedChildren_nonempty _ _ _) (Annealed.alignedChildren_subset_lattice _ _ _)
    R hRsymm hRpos

end HCPolySupport.HighContrast.Entry
