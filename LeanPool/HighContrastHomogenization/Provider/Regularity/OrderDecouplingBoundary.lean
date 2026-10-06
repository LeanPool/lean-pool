/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.OrderDecoupledRoundedApplication
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRateBearingCommonAffineGoodScaleEvent

/-!
# High-contrast homogenization: Provider.Regularity.OrderDecouplingBoundary

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Boundary of the order-decoupled rounded interface

The deterministic response is selected before the stochastic exponent.  This
module records the joint interface and the strict direction between its two
orders.  In particular, the printed-order row cannot be read as a row at the
private response order without an additional theorem.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

/-- The private order is strictly below every admissible printed order. -/
theorem privateRoundedOrder_lt_printCertificateOrder
    (d : ℕ) [NeZero d] {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    (privateRoundedPhysicalDirichletSpine d).order.1 <
      printCertificateOrder g := by
  have hPrivate :=
    (privateRoundedPhysicalDirichletSpine d).order_lt_one_twelfth
  have hg0 : 0 ≤ g := hg.1
  dsimp only [printCertificateOrder]
  linarith only [hPrivate, hg0]

end

end HighContrast
end HCPolySupport
