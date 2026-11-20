/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryPotentialRadialLSI.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryRadialProductLSI
public import LeanPool.GinibrePoincare.Analysis.StrongConvexPotentialRadialLSI

/-!
# Alternative Bakry Emery potential radial LSI

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmery_potential_smooth_radial_lsi`.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff NNReal
namespace GinibrePoincare
noncomputable section

/-- Radial LSI with the paper curvature constant for the actual nonquadratic log gas, obtained
from its actual Kostlan law, strongly convex Euclidean lifts and entropy
tensorization. The Gaussian-quantile route is independent of this endpoint. -/
theorem bakryEmery_potential_radial_lsi (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ 1 F)
    (hs : IsSymmetricRadiusTest n F) {K : ℝ≥0} (hLip : LipschitzWith K F)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ r, |F r| ≤ C) :
    squareEntropy (potentialMeasure n V) (fun z => F (magnitudeVector z)) ≤
      (2 / ((n : ℝ) * ρ)) *
        potentialGradientEnergy n V (fun z => F (magnitudeVector z)) := by
  refine potential_radial_lsi_of_radiusProduct_lsi n hn ρ hρ hV hrot hc ?_ F hF hs hLip C hC hb
  intro F hF K hLip C hC hb
  exact bakryEmery_radiusProduct_lsi n hn ρ hρ hV hrot hc F hF hLip C hC hb

/-- The paper's smooth compact radial observables, with all profile regularity
and boundedness derived from the observable itself. -/
theorem bakryEmery_potential_smooth_radial_lsi (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : Configuration n → ℝ) (hf : IsSmoothCompactSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    squareEntropy (potentialMeasure n V) f ≤
      (2 / ((n : ℝ) * ρ)) * potentialGradientEnergy n V f := by
  refine potential_smooth_radial_lsi_of_profile_lsi n ?_ f hf hr
  intro F hF hs K hLip C hC hb
  exact bakryEmery_potential_radial_lsi n hn ρ hρ hV hrot hc F hF hs hLip C hC hb

end
end GinibrePoincare
