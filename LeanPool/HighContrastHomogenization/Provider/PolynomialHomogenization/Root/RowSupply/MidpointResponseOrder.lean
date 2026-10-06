/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Certificate.PrintOrderCertificate

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.MidpointResponseOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Midpoint response order

The response order is chosen midway between half the physical block-row
weight and the printed certificate order.  The resulting two strict margins
are equal, while the squared response row retains a positive summability gap.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Certificate

/-- The midpoint of `printRowOrder g / 2` and `printCertificateOrder g`. -/
@[expose]
noncomputable def midpointResponseOrder (g : ℝ) : ℝ :=
  (3 + 5 * g) / 16

theorem midpointResponseOrder_margins {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    0 < midpointResponseOrder g ∧
      printRowOrder g / 2 < midpointResponseOrder g ∧
      midpointResponseOrder g < printCertificateOrder g ∧
      2 * midpointResponseOrder g - printRowOrder g = (1 - g) / 8 ∧
      1 - 2 * midpointResponseOrder g = 5 * (1 - g) / 8 ∧
      midpointResponseOrder g < 1 / 2 := by
  have hg0 : 0 ≤ g := hg.1
  have hg1 : g < 1 := hg.2
  unfold midpointResponseOrder printRowOrder printCertificateOrder
  constructor
  · linarith only [hg0]
  constructor
  · linarith only [hg1]
  constructor
  · linarith only [hg1]
  constructor
  · ring
  constructor
  · ring
  · linarith only [hg1]

theorem printRowOrder_lt_twice_midpointResponseOrder {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    printRowOrder g < 2 * midpointResponseOrder g := by
  have hmargin := (midpointResponseOrder_margins hg).2.2.2.1
  linarith only [hmargin, hg.2]

end RowSupply
end HighContrast
end HCPolySupport
