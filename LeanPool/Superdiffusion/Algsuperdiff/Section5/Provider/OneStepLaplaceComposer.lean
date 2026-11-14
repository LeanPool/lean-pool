/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.OneStepLaplace
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Trace.GoodCubeCrossing

/-!
# OneStepLaplaceComposer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The contraction factor and the site embedding of the one-step Laplace estimate

The one-step estimate on a good cube produces, at one centre, a strict
contraction for the negative exponential of the exit time from the enlarged
cube.  Its discount rate is `(C T(3^n))⁻¹` and its factor is
`oneStepLaplaceContraction` at the two scale constants of the exit-time
comparison, and neither depends on the centre of the cell, on the direction of
the datum, or on the sample: the constant `C` of the exit-time comparison is
returned once and for all, before the model, the accuracy, the scale and the
centre are quantified.

## The two indexings

The cells are the closed scale-`(n-1)` cells `z + □_{n-1}` centred at the
embedded lattice sites `3^{n-1} z`, and the enlargements are the open cubes
`z + □_n`.  The one-step estimate speaks of the pair
`(closure (y + □_{n-1}), y + □_n)`, so the two agree once the site embedding
`rescaledLatticePoint n` is recognized as `rescaleSite (n - 1)`.

## Main results

* `oneStepLaplaceContraction_ne_top`, `oneStepLaplaceContraction_lt_one` — the
  contraction factor is finite and strictly below one.
* `rescaledLatticePoint_eq_rescaleSite`, `good_goodSiteEnum` — the site
  embedding of the two indexings above, and the goodness of an enumerated site.

## References

* ABK26, the one-step Laplace estimate and the chaining of Section 5.3.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open Algsuperdiff.Section5.Trace
open DivergenceFormProcess.StoppedDirichlet
open HCPolySupport MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-! ## 1. The contraction factor -/

/-- The contraction factor is finite. -/
theorem oneStepLaplaceContraction_ne_top (Cup clow : ℝ≥0) :
    oneStepLaplaceContraction Cup clow ≠ ⊤ := by
  unfold oneStepLaplaceContraction
  exact ENNReal.sub_ne_top ENNReal.one_ne_top

/-- The contraction factor is strictly below one whenever both scale constants
are positive. -/
theorem oneStepLaplaceContraction_lt_one {Cup clow : ℝ≥0} (hCup : 0 < Cup)
    (hclow : 0 < clow) : oneStepLaplaceContraction Cup clow < 1 := by
  have hpPos : (0 : ℝ≥0∞) < survivalProbabilityConstant Cup clow := by
    rw [ENNReal.coe_pos]
    unfold survivalProbabilityConstant
    positivity
  have hePos : 0 < 1 - ENNReal.ofReal (Real.exp (-(clow : ℝ) / (2 * Cup))) := by
    apply tsub_pos_of_lt
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff zero_lt_one]
    exact Real.exp_lt_one_iff.mpr
      (div_neg_of_neg_of_pos (neg_neg_of_pos (NNReal.coe_pos.mpr hclow))
        (mul_pos two_pos (NNReal.coe_pos.mpr hCup)))
  unfold oneStepLaplaceContraction
  exact ENNReal.sub_lt_self ENNReal.one_ne_top (by norm_num)
    (ENNReal.mul_pos hpPos.ne' hePos.ne').ne'

/-! ## 3. The site embedding -/

/-- The embedding of the site lattice used by the good cube events is the
embedding of the scale-`(n-1)` partition. -/
theorem rescaledLatticePoint_eq_rescaleSite {d : ℕ} (n : ℤ)
    (z : Section5.Percolation.Site d) :
    rescaledLatticePoint n z = rescaleSite (n - 1) z := by
  rw [rescaledLatticePoint_eq_paperLatticePoint]
  rfl

/-- Every enumerated site of a centred lattice cube is good. -/
theorem good_goodSiteEnum {d k : ℕ} (Good : Section5.Percolation.Site d → Prop)
    [DecidablePred Good] (j : Fin (goodSites k Good).card) :
    Good (goodSiteEnum k Good j) :=
  (Finset.mem_filter.mp (Finset.coe_mem ((goodSites k Good).equivFin.symm j))).2

end

end Algsuperdiff.Section5.Provider
