/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangePoweredGauge

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeFiniteRangeDatum

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The finite-range coarse-ellipticity datum

The Gaussian half of the quenched tail needs the stopping-radius family read
against the Gaussian concentration gauge supplied by unit range of dependence
rather than against the source gauge of `e.coarse.ellipticity`.  Everything
downstream of such a datum is already available; this file names the datum, shows
what it delivers, and records why it is a genuine additional input rather than a
consequence of the assumptions already carried.

The gauge of a coarse-ellipticity datum occurs in one clause only, the source
tail.  The other clauses are monotone in the source scale in the *unfavourable*
direction: enlarging the source scale preserves the discounted Loewner bound but
enlarges the upper-tail event, so it can only make the tail heavier.  A datum at a
stronger gauge carried by a larger source scale therefore forces the original
source scale to satisfy the stronger tail already.  That is the content of
the source-tail bound below, and it is why the finite-range datum is carried
here as a named hypothesis instead of being derived.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Monotonicity of the two clauses in the source scale -/

/-- **The discounted Loewner bound is monotone in the source scale.**  Enlarging
the source scale shrinks the event on which the bound is asserted, so the bound
is inherited. -/
theorem coarseBound_of_source_le {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
    {Psi : ℝ → ℝ} {K : ℝ} {S S' : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S) (hle : ∀ a, S a ≤ S' a) :
    ∀ᵐ a ∂P, ∀ m : ℤ, S' a ≤ (3 : ℝ) ^ m →
      ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
        standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale ((3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ)))) E) := by
  filter_upwards [hdag.coarse_bound] with a ha m hm
  exact ha m (le_trans (hle a) hm)

/-- **The gauge-change interface.**  A coarse-ellipticity datum may be re-read
against any admissible gauge, at any source scale at least the original one, once
that scale's tail against the new gauge is supplied.  The tail is the only clause
that has to be re-proved. -/
theorem coarseEllipticityDagger_of_source_le {P : Measure (CoeffSpace d)} {g : ℝ}
    {E : BlockMat d} {Psi Psi' : ℝ → ℝ} {K K' : ℝ} {S S' : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S) (hle : ∀ a, S a ≤ S' a)
    (hmeas : Measurable S') (hnonneg : ∀ a, 0 ≤ S' a)
    (hadm : IndependentSums.AdmissiblePsi Psi') (hK' : 1 < K')
    (hgrowth : IndependentSums.HasPsiGrowth Psi' K')
    (htail : ∀ t : ℝ, 0 < t →
      P.real (IndependentSums.upperTailEvent S' t) ≤ (Psi' t)⁻¹) :
    HCPoly.Frozen.CoarseEllipticityDagger P g E Psi' K' S' where
  g_mem := hdag.g_mem
  refBlock_isSymm := hdag.refBlock_isSymm
  refBlock_posDef := hdag.refBlock_posDef
  gauge_admissible := hadm
  one_lt_growthWitness := hK'
  gauge_growth := hgrowth
  source_measurable := hmeas
  source_nonneg := hnonneg
  source_tail := htail
  coarse_bound := coarseBound_of_source_le hdag hle

/-! ## Why the finite-range datum is an additional input -/

/-! ## The named datum and what it delivers -/

end

end Quenched
end HighContrast
end HCPolySupport
