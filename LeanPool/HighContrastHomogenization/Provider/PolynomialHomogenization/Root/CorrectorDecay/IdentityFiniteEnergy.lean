/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentityGaugeSpecialization
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderIdentityCubeDualRegularity

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentityFiniteEnergy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped BigOperators

noncomputable section

open FiniteLipschitzCoreInternal

/-- The exact-identity finite recurrence closes under the same summable-tail
budget as the available rounded recurrence. -/
theorem finiteCenteredEnergy_le_of_identityGoodTail
    {d : ℕ} {s : ℝ}
    {a : Book.Ch03.CoeffFamily d} {C : ℝ} (hC : 1 ≤ C)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a)
    (hrecurrence : ∀ q ∈ Finset.Icc n m,
      finiteCenteredCubeSolutionEnergy a m u q ≤
        C * finiteCenteredCubeSolutionEnergy a m u m +
          C * ∑ j ∈ Finset.Ioc q m,
            scalarIdentityWeakError a s j *
              finiteCenteredCubeSolutionEnergy a m u j)
    (hTail : ScalarIdentityGoodTailOnInterval a s (2 * C)⁻¹ n m) :
    ∀ q ∈ Finset.Icc n m,
      finiteCenteredCubeSolutionEnergy a m u q ≤
        2 * C * finiteCenteredCubeSolutionEnergy a m u m := by
  let D : ℤ → ℝ := finiteCenteredCubeSolutionEnergy a m u
  let E : ℤ → ℝ := scalarIdentityWeakError a s
  have hD : ∀ j ∈ Finset.Icc n m, 0 ≤ D j := by
    intro j _hj
    exact finiteLipschitzEnergyRow_nonneg a m u j
  have hE : ∀ j ∈ Finset.Icc n m, 0 ≤ E j := by
    intro j _hj
    exact scalarIdentityWeakError_nonneg a s j
  have hrec : ∀ q ∈ Finset.Icc n m,
      D q ≤ C * D m + C * ∑ j ∈ Finset.Ioc q m, E j * D j := by
    intro q hq
    simpa only [D, E] using hrecurrence q hq
  have hsmall : ∑ j ∈ Finset.Icc n m, E j ≤ (2 * C)⁻¹ := by
    simpa only [ScalarIdentityGoodTailOnInterval, E] using hTail
  intro q hq
  have hbound := smallTail_interval_bound C D E hnm hC hD hE hrec
    hsmall q hq
  simpa only [D] using hbound

end

end HighContrast
end HCPolySupport
