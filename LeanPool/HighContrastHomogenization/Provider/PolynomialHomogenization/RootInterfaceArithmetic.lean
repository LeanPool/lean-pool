/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.RootInterfaceArithmetic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Arithmetic reconciliation for the homogenization root

The root statement carries one polynomial exponent and one error exponent that
several clauses share.  Every occurrence of the constant is weakened by
enlarging it and every occurrence of the error exponent is weakened by
shrinking it, so providers producing different values can be reconciled by a
maximum and a minimum.  This module records the four comparisons that make
that reconciliation legal.

The block-to-matrix identification is no longer an arithmetic gap: the root
retains the annealed sandwich and contrast decay until the canonical block is
identified.  The quenched side likewise retains the source burn bound.  The
finite enlargement of the normalized reference family is part of the
`GoodScale` certificate, so it neither changes the real random scale nor adds
an arithmetic weakening to the frozen conclusion.
-/

namespace HCPolySupport
namespace HighContrast
namespace RootInterface

open MeasureTheory

/-- A polynomial length bound at a base of at least one is weakened by
enlarging the exponent. -/
theorem le_rpow_of_le_rpow_of_exponent_le {base c c' y : ℝ} (hbase : 1 ≤ base)
    (hc : c ≤ c') (hy : y ≤ base ^ c) : y ≤ base ^ c' :=
  hy.trans (Real.rpow_le_rpow_of_exponent_le hbase hc)

/-- The Dirichlet error factor is read at a base of at most one, so it is
weakened by shrinking the exponent. -/
theorem rpow_le_rpow_of_exponent_ge_of_le_one {x kap kap' : ℝ} (hx : 0 < x)
    (hx1 : x ≤ 1) (hkap : kap' ≤ kap) : x ^ kap ≤ x ^ kap' :=
  Real.rpow_le_rpow_of_exponent_ge hx hx1 hkap

/-- The corrector error factor is read at a base of at least one and a negative
exponent, so it too is weakened by shrinking the exponent. -/
theorem rpow_neg_le_rpow_neg_of_exponent_ge {x kap kap' : ℝ} (hx : 1 ≤ x)
    (hkap : kap' ≤ kap) : x ^ (-kap) ≤ x ^ (-kap') :=
  Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hkap)

end RootInterface
end HighContrast
end HCPolySupport
