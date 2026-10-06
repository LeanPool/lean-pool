/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1BaseSlopeEnergyControl
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1CanonicalProjectionAbsoluteDecay
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.CanonicalGaugeSpine
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLocalCauchy

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.PrintOrderGaugeRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The printed-order exact-gauge simultaneous-slope row

Closing the large-scale C¹ slope approximation clause directly meets four enumerated obstructions:

1. the only quantitative tail the corrector-decay layer exports is at `printCertificateOrder g`;
2. the simultaneous-slope C1 theorem required its order `< 1 / 12`;
3. the printed certificate order is not below `1 / 12`, which refutes (1)
   against (2);
4. the private-order datum in `CanonicalPullbackCorrectorFamily` is only a
   qualitative summable tail whose delay `L` and restart `n'` are selected
   *after* the sample `(a, x)`.

After the corrector cone is lifted to the printed window `s < 1 / 2`
and the fourteen order binders are
lifted with it, obstruction (2) disappears and with it (3).  This module then
removes (4) as well: the certificate's **own** print-order power tail converts
to a good tail whose start is `Quenched.triadicCeilingIndex x` with **no**
delay and **no** restart, so the C1 constants can be selected before the
sample.

The price is exactly the ceiling-exporting smallness interface root-interface ceiling: the
corrector smallness `c` must be at most a law-free `cMax` fixed by `(d, g, eta)`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The printed certificate order lies strictly inside the lifted corrector
window `(0, 1/2)` for every root-admissible contrast exponent. -/
theorem printCertificateOrder_pos_of_mem_Ico {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) : 0 < printCertificateOrder g := by
  have hg0 : (0 : ℝ) ≤ g := hg.1
  unfold printCertificateOrder
  linarith only [hg0]

/-- The printed certificate order is admissible for the lifted cone. -/
theorem printCertificateOrder_lt_half_of_mem_Ico {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) : printCertificateOrder g < 1 / 2 := by
  have hg1 : g < 1 := hg.2
  unfold printCertificateOrder
  linarith only [hg1]

end

end Root
end HighContrast
end HCPolySupport
