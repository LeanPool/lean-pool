/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.CeilingReconciliation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.ReconciledSmallnessCertificate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The reconciled-smallness certificate: the assembly at the reconciled
# corrector smallness

The restated assembly `RootInterface.polynomial_homogenization_of_quenched_scale_v2`
takes `GoodScale` as a **parameter bound before `g`**.  The the ceiling-exporting smallness
interface ceiling
therefore cannot be a constant chosen after `g` — but it can be `cStar g` for a
function `cStar : ℝ → ℝ` bound before `GoodScale`.  That is what
`reconciledRootGoodScale` is.

`hhomogenized` is then **proved** at this certificate, character for character
in the assembly's binder shape, checked by the partial application below,
which supplies `hquenched` and `hhomogenized` and leaves exactly the six
clauses.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set
open RowSupply (eccentricityFoldFactor)

noncomputable section

/-- **The reconciled root certificate.**  The `c`-parameterised printed-order
certificate, read at the reconciled `g`-indexed corrector smallness. -/
@[expose]
def reconciledRootGoodScale (d : ℕ) [NeZero d] (cStar : ℝ → ℝ) :
    ℝ → ℝ → Mat d → CoeffSpace d → ℝ → Prop :=
  fun g kappaRate abar a x => rootGoodScaleAt d g (cStar g) kappaRate abar a x

/-! ## The providers, read at the reconciled-smallness certificate -/

end

end CorrectorComposition
end HighContrast
end HCPolySupport
