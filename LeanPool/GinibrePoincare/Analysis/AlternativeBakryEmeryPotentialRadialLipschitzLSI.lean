/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryPotentialRadialLipschitzLSI.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryPotentialRadialLSI
public import LeanPool.GinibrePoincare.Analysis.StrongConvexPotentialRadialLipschitzLSI
/-!
# Alternative Bakry Emery potential radial lipschitz LSI

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmery_potential_bounded_lipschitz_radial_lsi`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ContDiff NNReal BigOperators
namespace GinibrePoincare
noncomputable section

/-- The independent Bakry–Émery radial LSI for all bounded symmetric Lipschitz magnitude profiles,
under the genuine interacting nonquadratic law, with the actual a.e. gradient. -/
theorem bakryEmery_potential_radial_lsi_lipschitz (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (F : (Fin n → ℝ) → ℝ) (hs : IsSymmetricRadiusTest n F)
    {K : ℝ≥0} (hF : LipschitzWith K F) (C : ℝ) (hb : ∀ r, |F r| ≤ C) :
    squareEntropy (potentialMeasure n V) (fun z => F (magnitudeVector z)) ≤
      (2 / ((n : ℝ) * ρ)) * potentialGradientEnergy n V (fun z => F (magnitudeVector z)) := by
  refine potential_radial_lsi_lipschitz_of_radiusProduct_lsi n hn ρ hρ hV hrot hc ?_ F hs hF C hb
  intro F K hF C hb
  exact bakryEmery_radiusProduct_lsi_lipschitz n hn ρ hρ hV hrot hc F hF C hb

/-- A bounded Lipschitz extension of the smooth compactly supported radial inequality
in Theorem 1.14(2). The existential radial witness carries no regularity hypothesis. -/
theorem bakryEmery_potential_bounded_lipschitz_radial_lsi (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : Configuration n → ℝ) (hs : IsSymmetric f)
    {K : ℝ≥0} (hf : LipschitzWith K f) (C : ℝ) (hb : ∀ z, |f z| ≤ C)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    squareEntropy (potentialMeasure n V) f ≤
      (2 / ((n : ℝ) * ρ)) * potentialGradientEnergy n V f := by
  refine potential_bounded_lipschitz_radial_lsi_of_profile_lsi n ?_ f hs hf C hb hr
  intro F hs K hF C hb
  exact bakryEmery_potential_radial_lsi_lipschitz n hn ρ hρ hV hrot hc F hs hF C hb

end
end GinibrePoincare
