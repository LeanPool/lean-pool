/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexRadialProductLipschitzLSI.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexRadialProductLSI
public import LeanPool.GinibrePoincare.Analysis.StrongConvexBoundedLipschitzLSIExtension
public import LeanPool.GinibrePoincare.Analysis.FinitePiDensity

/-!
# Strong convex radial product lipschitz LSI

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `rhoConvex_radiusProduct_lsi_lipschitz`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ContDiff NNReal
namespace GinibrePoincare
noncomputable section

theorem rhoConvex_radiusProduct_absolutelyContinuous (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    potentialRadiusProduct n V ≪ volume := by
  let p := fun i : Fin n => radialConfinementProbabilityDensity n i.val (fun r => V (r : ℂ))
  have hi (i : Fin n) := rhoConvexPotential_radial_density_integrable n i.val hn ρ hρ hV hrot hc
  have he (i : Fin n) := radialConfinementProbabilityDensity_eq_sqrt_map n i.val V hV.continuous (hi
      i)
  have hp (i : Fin n) : Continuous (p i) :=
    radialConfinementProbabilityDensity_continuous n i.val (hV.continuous.comp
        Complex.continuous_ofReal)
  let (i : Fin n) : IsProbabilityMeasure (volume.withDensity (fun r => ENNReal.ofReal (p i r))) :=
    radialConfinementProbabilityDensity_isProbability n i.val _
      (hV.continuous.comp Complex.continuous_ofReal) (hi i)
  have heq : potentialRadiusProduct n V =
      Measure.pi (fun i : Fin n => volume.withDensity (fun r => ENNReal.ofReal (p i r))) := by
    unfold potentialRadiusProduct
    congr 1
    funext i
    exact (he i).symm
  rw [heq, Measure.pi_withDensity (fun _ : Fin n => volume)
    (fun i r => ENNReal.ofReal (p i r)) (fun i => (hp i).measurable.ennreal_ofReal)]
  exact withDensity_absolutelyContinuous _ _

/-- Full bounded Lipschitz LSI for the actual independent nonquadratic radii. -/
theorem rhoConvex_radiusProduct_lsi_lipschitz (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : (Fin n → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (C : ℝ) (hb : ∀ r, |f r| ≤ C) :
    squareEntropy (potentialRadiusProduct n V) f ≤ (2 / ((n : ℝ) * ρ)) *
      ∫ r, directionalEnergy (fun i : Fin n => Pi.single i 1) f r ∂potentialRadiusProduct n V := by
  have hi (i : Fin n) := rhoConvexPotential_radial_density_integrable n i.val hn ρ hρ hV hrot hc
  let (i : Fin n) : IsProbabilityMeasure ((potentialSquaredRadiusLaw n i.val V).map Real.sqrt) := by
    rw [← radialConfinementProbabilityDensity_eq_sqrt_map n i.val V hV.continuous (hi i)]
    exact radialConfinementProbabilityDensity_isProbability n i.val _
      (hV.continuous.comp Complex.continuous_ofReal) (hi i)
  let : IsProbabilityMeasure (potentialRadiusProduct n V) := by
    unfold potentialRadiusProduct
    infer_instance
  apply boundedLipschitz_lsi_of_C1 volume (potentialRadiusProduct n V)
    (rhoConvex_radiusProduct_absolutelyContinuous n hn ρ hρ hV hrot hc)
    (fun i : Fin n => Pi.single i 1) (2 / ((n : ℝ) * ρ)) _ f hf C
    (by intro r; simpa only [Real.norm_eq_abs] using hb r)
  intro g hg L hgL D hgD
  have hD : 0 ≤ D := (norm_nonneg (g 0)).trans (hgD 0)
  exact rhoConvex_radiusProduct_lsi n hn ρ hρ hV hrot hc g hg hgL D hD
    (by intro r; simpa only [Real.norm_eq_abs] using hgD r)

end
end GinibrePoincare
