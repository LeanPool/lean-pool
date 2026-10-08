/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledHardyPositiveRow
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledPairingAggregation
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledBufferedComparisonRealization
public import LeanPool.HighContrastHomogenization.Provider.Regularity.OrderDecouplingBoundary

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.RuledLocalizationAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Assembly of the ruled localization provider

This module couples one ruled Whitney carrier, one buffered comparison
realization, the positive Hardy row, and the print-order rate certificate.
The comparison realization and its finite quantitative schedule are retained
as a named selected-instance trace; no datum or Caccioppoli premise is
strengthened to every carrier or every comparison family.

The numerical endpoint below is the common cap for the two realized rows.
Its coefficient is selected before the stochastic exponent, and that exponent
is selected before the comparison matrix, coefficient sample, and domain.
-/

namespace HCPolySupport
namespace HighContrast
open Book Book.Ch03 MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem isEllipticFieldOn_of_pointwise_representative
    {lam Lam : ℝ} {f : CoeffField d} (hf : Measurable f)
    (hell : ∀ x, IsEllipticMatrix lam Lam (f x))
    {U : Set (Vec d)} (hU : MeasurableSet U) :
    IsEllipticFieldOn lam Lam U f := by
  classical
  refine ⟨?_, fun x _ => hell x⟩
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  exact Measurable.ite hU
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hf))
    measurable_const

/-- The normalized duality price obtained when each of the two realized rows
is bounded by the same finite error cap. -/
@[expose]
def ruledScheduledTwoRowCap
    (d : ℕ) (hardyConstant errorCap : ℝ≥0∞) : ℝ≥0∞ :=
  ((fractionalDualToBesovConstant d) ^ (2 : ℕ) * errorCap) ^
        (1 / 2 : ℝ) * hardyConstant ^ (1 / 2 : ℝ) +
    ((fractionalDualToBesovConstant d) ^ (2 : ℕ) * errorCap) ^
        (1 / 2 : ℝ) * hardyConstant ^ (1 / 2 : ℝ)

/-- The available integrable Hardy selector supplies the exact constant consumed
by the dependent assembly constructor, with no continuity or carrier
premise. -/
theorem exists_ruledHardySelection
    (d : ℕ) [NeZero d] {rho Rad s : ℝ}
    {U : Set (Vec d)} (hSandwich : HasBallSandwich U rho Rad)
    (hs : 0 < s) (hsHalf : s < 1 / 2) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (V : Set (Vec d)), IsOpenBoundedConvexDomain V →
        HasBallSandwich V rho Rad →
        ∀ (system : EnlargedMarginRuledTriadicWhitneySystem V rho Rad)
          (G : Vec d → Vec d),
          Integrable G (volume.restrict V) →
            normalizedWhitneyRowEnergy system
                (ruledPositiveWhitneyCellEnergy system s G) ≤
              C * hsNormSq V s G := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  obtain ⟨hrho, hRadNonneg, center, hinner, houter⟩ := hSandwich
  have hRad : 0 < Rad := by
    have hcenterOuter :=
      houter (hinner (center_mem_euclideanBallAt center hrho))
    rw [mem_euclideanBallAt_iff] at hcenterOuter
    have hzero : vecNormSq (center - center) = 0 := by
      rw [sub_self, vecNormSq_eq_zero_iff]
    rw [hzero] at hcenterOuter
    nlinarith only [hcenterOuter, hRadNonneg]
  exact exists_normalizedRuledPositiveWhitneyRowHsConstant
    hd hrho hRad hs hsHalf

end

end HighContrast
end HCPolySupport
