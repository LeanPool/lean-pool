/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.ObservationFamilyRow

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.BoundaryEnergyFiniteness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# (ε): the boundary-energy finiteness transport

Tabulating the module against the restated Dirichlet clause exposes one
premise not named elsewhere.  The `hBoundaryTop` premise asks for
`boundaryEnergy ≠ ⊤`, and the energy price from the modules named above instantiates
`boundaryEnergy` at the **gauge-conjugated** boundary datum

```
hsNormSq U s₀ (fun y ↦ matVecMul (matSqrt (symmPart abar)) (g₀.grad y)),
```

while the hole supplies finiteness for the **unconjugated** one,
`hsNormSq U s₀ g₀.grad ≠ ⊤`.

The transport is the pointwise matrix action `hsNormSq_matVecMul_le`
(`HCPoly.Analytic.AffineFractionalNorm`), whose cost is the squared
operator norm — finite, so it moves finiteness across with nothing to pay.  No
hypothesis on `abar`, the domain or the order is needed.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **(ε).**  The frozen hole's finiteness premise for the boundary datum
transports to the gauge-conjugated boundary energy that the `hBoundaryTop` premise
reads. -/
theorem hsNormSq_matSqrt_symmPart_ne_top (abar : Mat d) {U : Set (Vec d)}
    {s : ℝ} {G : Vec d → Vec d} (hG : hsNormSq U s G ≠ ⊤) :
    hsNormSq U s
        (fun y ↦ matVecMul (matSqrt (symmPart abar)) (G y)) ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG)
    (hsNormSq_matVecMul_le (matSqrt (symmPart abar)) U s G)

end

end RowSupply
end HighContrast
end HCPolySupport
