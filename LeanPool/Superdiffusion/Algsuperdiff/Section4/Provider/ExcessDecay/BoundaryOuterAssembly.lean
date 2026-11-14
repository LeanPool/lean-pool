/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryOuterCaccioppoli
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ForcingCorrection

/-!
# BoundaryOuterAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary-regime energy estimate at the frozen theorem's own window

```text
  ν ⨍_{(x+□_{k-2})∩□_m} |∇u|²
      ≤ 3^d · [ 2 · P_{s,t} · λ_t 3^{-2k} ‖u(·+c) - v‖²_{L²(□_k)}
                + 2 · 18^d · ( C r^{-3/2} Λ⁻ [g]_{B^r}
                             + C r^{-1/2} Λ⁺ ‖∇h‖_{B^r} )² ] .
```

Everything on the left is the anchor's; everything on the right is
CoarseGraining's, at the covering cube `□_k` in its own frame, at the
translated sample `τ_c ω`, `c = wellPlacedCentre x m k`.  The comparison
solution `v` is *produced*, not assumed: it is the Dirichlet solution on `□_k`
carrying the transported boundary datum `h(·+c)`.

## Why the localized datum is the only possible hypothesis (disclosed)

At `Q = □_m` that is the anchor's own condition, but at `Q = □_m` the
Caccioppoli core is `□_m ∩ (w+□_{m-2})` and the covering ratio to the anchor's
window `x+□_n` is `3^{(m-2-n)d}`, which destroys the estimate.  That is the
content of `BoundaryOuterCaccioppoli`; here it is discharged.

## The `ν |∇u|²` reading

The antisymmetric flux shift leaves the symmetric part of the coefficient
untouched and the cutoff coefficient's symmetric part is `ν Id`
(`AntisymmetricShiftCutoff`), so CoarseGraining's `localizedCoeffEnergyValue`
at the flux-corrected family is literally `ν` times the normalized average of
`|∇u|²`.  The covering transport is therefore an *identity* on the integrand
and an inequality only in the volume ratio.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`;
  `l.harmonic.approximation.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The window centre in the covering cube's frame -/

/-- The anchor's window centre, seen from the well-placed centre, lies in `□_k` —
the hypothesis `x ∈ openCubeSet Q` of CoarseGraining's Caccioppoli theorem. -/
theorem sub_wellPlacedCentre_mem_openCubeSet {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k ≤ m) :
    x - wellPlacedCentre x m k ∈ openCubeSet (originCube d k) := by
  have hmem : x ∈ truncatedWindow x m k := mem_truncatedWindow_self k hx
  have h := truncatedWindow_subset_image_add_wellPlacedCentre x hkm (le_refl k) hmem
  rwa [mem_image_add_iff] at h

/-! ## 2. The covering transport of the anchor's window energy -/

/-! ## 3. The composed boundary display at the anchor's window -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
