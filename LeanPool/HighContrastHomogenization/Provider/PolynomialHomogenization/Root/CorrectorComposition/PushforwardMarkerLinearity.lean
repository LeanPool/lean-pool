/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.PushforwardCorrectorFamily
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.CertificatePositiveDefiniteness

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.PushforwardMarkerLinearity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The corrector side recomposed at the pushforward marker

`RootInterface.polynomial_homogenization_of_quenched_scale_v2` is instantiated at

* `GoodScale   := reconciledRootGoodScale d cStar`   (the ceiling-exporting smallness interface),
* `CorrectorFamily := Root.RootPushCorrectorFamilyPredicate d`  (the
  pushforward marker).

`hhomogenized` is already proved.  This module discharges
the stationary corrector family clause from the stationary corrector family clause's
`correctorFamilyHole_of_normalizedSupply`, and
supplies the slope linearity that the large-scale C¹ slope approximation clause needs from the
marker itself, so that no
clause of the corrector side is left as a bare assumption about the family.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

/-- Slope linearity holds for **every** pair carrying the pushforward marker,
not just for the one the hole returns: the marker is the definitional record. -/
theorem pushforwardMarker_linear (d : ℕ) [NeZero d] :
    ∀ (abar : Mat d) (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
      (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
      Root.RootPushCorrectorFamilyPredicate d abar Phi gradPhi →
      ∀ (c : ℝ) (e e' : Vec d) (a : CoeffSpace d),
        gradPhi (c • e + e') a =ᵐ[volume]
          fun y ↦ c • gradPhi e a y + gradPhi e' a y := by
  rintro abar Phi gradPhi ⟨hS, rfl, rfl⟩ c e e' a
  exact Root.pushforwardPhysicalGradPhi_linear d abar hS c e e' a

end

end CorrectorComposition
end HighContrast
end HCPolySupport
