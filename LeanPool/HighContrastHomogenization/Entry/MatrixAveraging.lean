/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.MatrixAveraging

/-!
# High-contrast homogenization: Entry.MatrixAveraging

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite-range matrix averaging

This module proves the finite-range matrix averaging statement of
`HCPoly/Entry/Statements/MatrixAveraging.lean`. It serves the labelled result
`l.fixed.geometry.matrix.averaging`: the even-moment matrix estimate,
residue-class independence, stationary transport, and convex recombination
from ordinary support.

We choose `Csrc = 1` before the law and geometry. This preserves the exact
standing threshold premise; it does not assert the stochastic source
estimate with constant one. This averaging proof needs only moment finiteness,
which the standing law supplies at every bounded cell. The unused standing
binders are underscore-renamed without changing their type, kind, or position.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean blockSub coarseBlock normalizedBlock)
namespace HCPolySupport.HighContrast.Entry
open MeasureTheory

/-- The exact finite-range averaging statement; source near `l.fixed.geometry.matrix.averaging`. -/
theorem fixed_geometry_matrix_averaging
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
        (_hP : IsProbabilityMeasure P) (_hstat : IsStationaryLaw P) (_hunit : IsUnitRangeLaw P)
        (_hell : CoarseEllipticityDagger P γ E Ψ K S)
        (N : ℕ) (_hN : 2 ≤ N) (_hNeven : Even N)
        (jStar : ℕ) (_hj : 2 * d ≤ 3 ^ jStar)
        (_hsrc : ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ))
        (m : Mat d) (_hm : m.PosDef)
        (j : ℤ) (_hjgen : (jStar : ℤ) ≤ j)
        (Z : Finset (Vec d)) (_hZne : Z.Nonempty)
        (_hZ : (Z : Set (Vec d)) ⊆ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar m) j)
        (R : BlockMat d) (_hRsymm : IsSymmetricBlockMat R) (_hRpos : Book.Ch02.BlockPosDef R),
        lqSchattenNorm P (N : ℝ)
            (fun a =>
              ofFullBlockMat
                ((Z.card : ℝ)⁻¹ •
                  ∑ z ∈ Z,
                    toFullBlockMat
                      (normalizedBlock
                        (blockSub
                          (coarseBlock
                            (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j z) a)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j))
                        R))) ≤
          (N : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) / (Z.card : ℝ) ^ ((1 : ℝ) / 2) *
            lqSchattenNorm P (N : ℝ)
              (fun a =>
                normalizedBlock
                  (blockSub (coarseBlock (HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) j) a)
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j))
                  R) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro P E Ψ K S hP hstat hunit hell N hN hNeven jStar hj _hsrc m hm j hjgen Z hZne hZ R hRsymm hRpos
  exact Annealed.matrix_averaging_roundedGrid d hd P hP γ E Ψ K S hstat hunit hell
    N hN hNeven jStar hj m hm j hjgen Z hZne hZ R hRsymm hRpos

end HCPolySupport.HighContrast.Entry
