/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Besov.Carriers
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeBesovPoincare.W12Embedding
public import LeanPool.HighContrastHomogenization.Support.Besov.Duality.GlobalComparison
public import LeanPool.HighContrastHomogenization.Support.Besov.Duality.CaccioppoliBridge

/-!
# MultiscalePoincareBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The multiscale Poincare bridge at the genuine negative Sobolev carrier

This module proves that the manuscript object `3^{-m}‖F‖_{\Hminusul(\cu_m)}` of
a vector field `F` on a triadic cube of scale `m` is bounded by the multiscale
sum of its cube averages, and specializes that bound to the canonical maximizer
gradient centred at the coarse scale-separation vector.  This is the
`\ell^2`-aggregated form of the estimate that ABK26 obtains by citing the
multiscale Poincare inequality of AK.Book, Proposition 1.10.

The estimate is proved directly at the genuine Chapter 1 negative Sobolev
carrier of `Carriers.lean`.  No Besov surrogate appears on the left-hand side.

## Route

1. `cubeBesovDualMeanZeroTestGlobal_rescaled_test`: a Chapter 1 mean-zero
   `W^{1,2}` test in the unit normalized gradient ball, rescaled by the
   scale-free constant `testRescaleConstant`, is an admissible mean-zero
   negative Besov test at `(s,p,q) = (1,2,1)`.  The analytic input is the
   upstream embedding `cubeBesovPartialSeminormTop_one_two_le_normalizedW1pSeminorm`
   (`Homogenization/Sobolev/Foundations/CubeBesovPoincare/W12Embedding.lean`).
   The exponent bookkeeping is `cubeBesovConjExponent 1 = ∞` and
   `cubeBesovConjExponent 2 = 2`, so the dual test seminorm at `(1,2,1)` is the
   positive Besov `B^1_{2,∞}` partial seminorm.
2. `normalizedMeanZeroHMinusOneSeminorm_le_multiscalePoincareConstant_mul_cubeBesovCircNorm`:
   pairing against the rescaled test and taking the supremum over the test
   class gives the scalar bridge, composed with the upstream comparison
   `cubeBesovDualMeanZeroSeminorm_le_note_constant_mul_cubeBesovCircNorm`
   (`Homogenization/Besov/Duality/GlobalComparison.lean`) at `s = 1`, `p = 2`,
   `q = 1`, all of whose hypotheses hold at those exponents.
3. `scaledNegHMinusOne_le_multiscaleAverageSum`: coordinatewise aggregation in
   the same Euclidean `\ell^2` shape in which `scaledNegHMinusOne` is defined.
4. `scaledNegHMinusOne_maximizerGradientDefect_le_multiscaleAverageSum`: the
   instance at the Chapter 2 canonical maximizer gradient, centred at
   `coarseScaleSeparation`.

## Correspondence with the printed display

`cubeBesovCircDepthWeight_one` records that at `s = 1` the depth-`j` negative
circ weight of a cube of scale `m` is `3^{m-j}`.  Since the depth-`j` circ
average is `avsum_{z\in3^{m-j}\Zd\cap\cu_m}|(f)_{z+\cu_{m-j}}|^2` and the `q =
1` circ norm sums those terms over all depths, the quantity
`3^{-m}·cubeBesovCircNorm Q 1 2 1 f` is the printed right-hand side
`Σ_{n=-∞}^{m} 3^{-(m-n)}(avsum_z |(f)_{z+\cu_n}|^2)^{1/2}` under the reindexing
`n = m - j`.  This identification is a formalization reading, not a Lean
theorem: only the weight half of it, `cubeBesovCircDepthWeight_one`, is
formalized here; the remaining identification of the depth average and of the
depth sum with the printed average and sum is read off the upstream definitions
`cubeBesovCircDepthAverage`, `cubeBesovCircPartialSeminorm` and
`cubeBesovCircNorm` by inspection.

The conclusion proved here aggregates the components in `\ell^2`, which is the
same aggregation used to define `scaledNegHMinusOne`.  By Minkowski's
inequality in the coordinate index, that `\ell^2` aggregate is bounded by the
printed sum of Euclidean averages, so the bound proved here implies the printed
display with the same constant.
-/

namespace Algsuperdiff.Section3.Provider.Besov

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open scoped ENNReal

noncomputable section

variable {d : ℕ}

variable [NeZero d]

/-! ## Weight bookkeeping -/

omit [NeZero d] in
/-- At `s = 1` the depth-`j` negative circ weight of a cube of scale `m` is
`3^{m-j}`.  Hence `3^{-m}` times the negative circ norm at `(s,p,q) = (1,2,1)`
is exactly the manuscript sum `Σ_{n ≤ m} 3^{-(m-n)}(avsum_z |(f)_{z+□_n}|²)^{1/2}`
under the reindexing `n = m - j`. -/
theorem cubeBesovCircDepthWeight_one (Q : TriadicCube d) (j : ℕ) :
    cubeBesovCircDepthWeight Q 1 j = (3 : ℝ) ^ Q.scale / (3 : ℝ) ^ j := by
  rw [cubeBesovCircDepthWeight, Real.rpow_one, cubeScaleFactor]

/-! ## The canonical maximizer instance -/

/-- The manuscript field `∇v(·,\cu_m,p,q;\a) - (\s_*^{-1}(\cu_m)(q+\k(\cu_m)p) -
p)`, written from the Chapter 2 canonical maximizer. -/
noncomputable def maximizerGradientDefect (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (p q : Vec d) :
    Vec d → Vec d :=
  fun x =>
    (Ch02.canonicalMaximizer
        (Ch02.responseExistenceTheory (Ch02.cubeDomain Q)
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q))
        p q).toSolution.toH1.grad x -
      coarseScaleSeparation a ha Q p q

end

end Algsuperdiff.Section3.Provider.Besov
