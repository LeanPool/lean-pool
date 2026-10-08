/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.PushforwardMarkerLinearity

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.CertificateProjections

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The certificate projections, discharged

Three certificate-side premises were carried as *consumer-supplied*
corrector-family hypotheses:

* the corrector-and-flux decay clause's `hproject` — `rootGoodScaleAt … →
PrintOrderRateBearingCommonAffineGoodScale …`;
* the large-scale Lipschitz estimate clause's `hcustody` — `rootGoodScaleAt … →
DecoupledRootGoodScale d g cD κc …`;
* the ceiling comparisons that let a module read the certificate at its own
  smallness.

All three are **theorems**, not assumptions, once the certificate is the ceiling-exporting
smallness interface `c`-parameterised one.  The reason is structural and worth stating:

* `RootInterface.RootGoodScale` hides its smallness behind `∃ c ∈ Ioo 0 1`, and the
  root instantiation pins that `c` to `1/2`.  The only available transport,
  `PrintOrderRateBearingCommonAffineGoodScale.mono_smallness`, moves the
  smallness **upward** only.  So from `RootGoodScale` one cannot reach the corrector-and-flux
  decay clause's
  `canonicalCorrectorSmallness d g hg` or the large-scale Lipschitz estimate clause's `(2 *
  Crec)⁻¹`, both of which
  may be far below `1/2`.  That is exactly the gap
  `HCPoly.Provider.PolynomialHomogenization.RootInterface.SmallnessMonotone`'s own docstring names.
* `CorrectorComposition.rootGoodScaleAt` exposes the smallness as a binder, and
  `exists_rootGoodScaleAt_of_quenchedRow` proves `hhomogenized` at **every**
  smallness.  So the certificate can be *produced* at `cStar g` below every
  module ceiling, and `mono_smallness` then moves it **up** to each module's own
  constant.  The direction of the monotonicity is now the useful one.

The projections themselves are then one field access plus one application.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The two projections -/

/-- **The ceiling-exporting smallness interface exposes the printed rate-bearing certificate at
its own smallness.**  It is literally the `good` field of the retained-row
structure; nothing is estimated. -/
theorem printOrderGoodScale_of_rootGoodScaleAt [NeZero d] {g c kappaRate : ℝ}
    {abar : Mat d} {a : CoeffSpace d} {x : ℝ}
    (h : rootGoodScaleAt d g c kappaRate abar a x) :
    PrintOrderRateBearingCommonAffineGoodScale d g c kappaRate abar a x := by
  obtain ⟨hh, _hc, _hdelta⟩ := h
  exact hh.good

/-- The same certificate read at any **larger** smallness. -/
theorem printOrderGoodScale_of_rootGoodScaleAt_mono [NeZero d]
    {g c c' kappaRate : ℝ} {abar : Mat d} {a : CoeffSpace d} {x : ℝ}
    (h : rootGoodScaleAt d g c kappaRate abar a x)
    (hkappa : 0 < kappaRate) (hc : 0 < c) (hcc : c ≤ c') :
    PrintOrderRateBearingCommonAffineGoodScale d g c' kappaRate abar a x :=
  RootInterface.PrintOrderRateBearingCommonAffineGoodScale.mono_smallness
    (printOrderGoodScale_of_rootGoodScaleAt h) hkappa hc hcc

/-- **The decoupled certificate the large-scale Lipschitz estimate clause consumes.**  The
private-order half is
recovered from the printed one by
`Root.DecoupledRootGoodScale.of_printOrder`; nothing stochastic is added. -/
theorem decoupledRootGoodScale_of_rootGoodScaleAt [NeZero d]
    {g c cD kappaRate : ℝ} {abar : Mat d} {a : CoeffSpace d} {x : ℝ}
    (h : rootGoodScaleAt d g c kappaRate abar a x)
    (hkappa : 0 < kappaRate) (hc : 0 < c) (hcc : c ≤ cD) :
    Root.DecoupledRootGoodScale d g cD kappaRate abar a x :=
  Root.DecoupledRootGoodScale.of_printOrder
    (printOrderGoodScale_of_rootGoodScaleAt_mono h hkappa hc hcc)

/-! ## The two hole-side corrector-family hypothesis premises, discharged -/

/-- **the large-scale Lipschitz estimate clause's certificate projection**, in the exact shape
`exists_largeScaleLipschitz_of_goodScaleProjection` demands.  This is the whole
of the large-scale Lipschitz estimate clause's residue, and it is a theorem. -/
theorem largeScaleLipschitz_certificateProjection (d : ℕ) [NeZero d] :
    ∀ (g : ℝ), g ∈ Ico (0 : ℝ) 1 →
      ∀ (Crec cD : ℝ), 1 ≤ Crec → cD = (2 * Crec)⁻¹ → cD ∈ Ioo (0 : ℝ) 1 →
        ∀ (c : ℝ), c ∈ Ioo (0 : ℝ) 1 → c ≤ cD →
          ∀ κc : ℝ, 0 < κc →
            ∀ (abar : Mat d) (a : CoeffSpace d) (x : ℝ), 1 ≤ x →
              rootGoodScaleAt d g c κc abar a x →
                Root.DecoupledRootGoodScale d g cD κc abar a x :=
  fun _g _hg _Crec _cD _hCrec _hcD _hcDRange _c hc hccD _κc hκc _abar _a _x
    _hx hgood ↦
    decoupledRootGoodScale_of_rootGoodScaleAt hgood hκc hc.1 hccD

/-! ## the large-scale Lipschitz estimate clause, unconditional at the ceiling-exporting smallness
interface -/

/-- **the large-scale Lipschitz estimate clause at the `c`-parameterised certificate, with no
hypothesis at
all.**  The ceiling `cMax` is the `(2 * Crec)⁻¹` the decoupled terminal
itself selects. -/
theorem exists_largeScaleLipschitz_of_reconciledRootGoodScale (d : ℕ) [NeZero d] :
    ∀ g : ℝ, g ∈ Ico (0 : ℝ) 1 →
      ∃ cMax : ℝ, cMax ∈ Ioo (0 : ℝ) 1 ∧
        ∀ c : ℝ, c ∈ Ioo (0 : ℝ) 1 → c ≤ cMax →
          ∀ κc : ℝ, 0 < κc →
            ∃ C : ℝ, 0 < C ∧
              ∀ (abar : Mat d) (a : CoeffSpace d) (x : ℝ), 1 ≤ x →
                rootGoodScaleAt d g c κc abar a x →
                ∀ R : ℝ, x ≤ R →
                  ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
                    MemH1a (fun y ↦ a.1 y) (ellipsoid abar R) u Du →
                    IsWeakSolutionOn (fun y ↦ a.1 y) (ellipsoid abar R) Du →
                      ∀ r : ℝ, r ∈ Icc x R →
                        weightedGradNorm (fun y ↦ a.1 y)
                            (ellipsoid abar r) Du ≤
                          ENNReal.ofReal C *
                            weightedGradNorm (fun y ↦ a.1 y)
                              (ellipsoid abar R) Du :=
  exists_largeScaleLipschitz_of_goodScaleProjection d
    (fun g c κc ↦ rootGoodScaleAt d g c κc)
    (largeScaleLipschitz_certificateProjection d)

/-! ## the corrector-and-flux decay clause, reduced to the family corrector-family hypothesis
alone -/

end

end CorrectorComposition
end HighContrast
end HCPolySupport
