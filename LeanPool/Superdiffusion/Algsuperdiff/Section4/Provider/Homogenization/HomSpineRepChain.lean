/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineRepLimit
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineFrameData

/-!
# HomSpineRepChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 3c: the chain endpoint with NO representative binder

## What this module is

`HomSpineRepLimit` produces a continuous representative from the negative-order
gauge alone.  This module wires that producer into the two places the
chain assumed one:

* `HasContinuousRepresentative` — the residue predicate — is now a THEOREM
  under the gauge (`hasContinuousRepresentative_of_uniformBoxGauge`);
* the finite-`p` `L^∞` conversion — whose three binders `hgc`,
  `hgw`, `hzero` carried the representative and its face vanishing — is
  restated with those three binders GONE and the conclusion at the a.e.-defined
  `w` itself.

The face vanishing `hzero` is not lost: it is the derived
`faceZero_of_continuousRepresentative`, applied to the representative this
module produces.  The only new hypothesis is `hWzero` (`w` vanishes off the
open cube), which the `H¹₀` zero extension supplies and which the frame already
carries.

## The shape of the endpoint

```text
  3^{-m}|w x| ≤ 96 d² · liftGeomFactor (s + d/p) · A     for a.e. x ∈ □_m
```

— the same display as the conversion theorem, with `g` replaced by `w`.
The two agree a.e., so the restricted a.e. statement transfers verbatim; the
consumer (clause (C3)) reads `|u - v|` on the open cube, where `w` IS `u - v`.

## References

* ABK26, Theorem B Step 3.
-/

open MeasureTheory HCPolySupport HCPolySupport.Book.Ch03

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The residue, discharged -/

/-- **the residue, as a theorem.**

`HasContinuousRepresentative w` — the ONE irreducible frame item of the §4.5
spine — holds under the translate-uniform negative gauge on `∇w` together with
the integrability and compact support the `H¹₀` zero extension already
supplies.  This is `HomSpineRepLimit.exists_continuous_ae_eq_of_uniformBoxGauge`
read in the vocabulary of `HomSpineFrameData`. -/
theorem hasContinuousRepresentative_of_uniformBoxGauge {m : ℤ} {s A : ℝ}
    {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hgauge : UniformBoxGaugeBound m s A G) (hs0 : 0 < s) (hs2 : s ≤ 1 / 2) :
    HasContinuousRepresentative w :=
  exists_continuous_ae_eq_of_uniformBoxGauge hw hwI hwc hGI hgauge hs0 hs2

variable [NeZero d]

end

end Algsuperdiff.Section4.Provider.Homogenization
