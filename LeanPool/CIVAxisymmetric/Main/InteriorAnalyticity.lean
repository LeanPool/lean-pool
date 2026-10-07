/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Hypotheses
public import LeanPool.CIVAxisymmetric.Prerequisites.Kahane.Induction

/-!
# The public statement `CIV.Main.interiorAnalyticity`

This module proves the statement `CIV.interiorAnalyticity`: a classical solution of `eq:nse:forced`
on `B(R) × (t₁, t₂)` with a locally uniformly spatially analytic force is locally uniformly
spatially analytic (`thm:analytic:interior`). The proof is `CIV.kahane_interiorAnalyticity`: on
nested regions inside each compactly contained cylinder, the weighted derivatives of the velocity
and the pressure are bounded by a factorial majorant, by induction on the order, through interior
gradient bounds for the heat operator and the Laplacian.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV
namespace Main

/-- The public statement of interior analyticity (`thm:analytic:interior`). -/
theorem interiorAnalyticity (R t₁ t₂ : ℝ) (hR : 0 < R) (ht : t₁ < t₂)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f (spaceTimeSet (vec3Ball 0 R) (Ioo t₁ t₂)))
    (hf : LocallyUniformlyAnalyticOn f R t₁ t₂) :
    LocallyUniformlyAnalyticOn u R t₁ t₂ :=
  kahane_interiorAnalyticity R t₁ t₂ hR ht u p f hsol hf

end Main
end CIV
