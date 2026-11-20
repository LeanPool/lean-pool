/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexRadialProductLSI.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexProductLSI
public import LeanPool.GinibrePoincare.Analysis.StrongConvexRadialLaw

/-!
# Strong convex radial product LSI

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `rhoConvex_radiusProduct_lsi`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ContDiff NNReal
namespace GinibrePoincare
noncomputable section

/-- The actual independent positive-radius Kostlan product. -/
def potentialRadiusProduct (n : ℕ) (V : Potential) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i : Fin n => (potentialSquaredRadiusLaw n i.val V).map Real.sqrt)

/-- Logarithmic Sobolev inequality for the n-fold nonquadratic radius product, derived by
coordinate quantile transports from the actual finite Gaussian product. -/
theorem rhoConvex_radiusProduct_lsi (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) {K : ℝ≥0}
    (hfLip : LipschitzWith K f) (C : ℝ) (hC : 0 ≤ C) (hfBound : ∀ x, |f x| ≤ C) :
    squareEntropy (potentialRadiusProduct n V) f ≤
      (2 / ((n : ℝ) * ρ)) * ∫ r,
        directionalEnergy (fun i : Fin n => Pi.single i 1) f r ∂potentialRadiusProduct n V := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let ν := fun i : Fin n => (potentialSquaredRadiusLaw n i.val V).map Real.sqrt
  have hi (i : Fin n) := rhoConvexPotential_radial_density_integrable n i.val hn ρ hρ hV hrot hc
  have he (i : Fin n) := radialConfinementProbabilityDensity_eq_sqrt_map n i.val V hV.continuous (hi
      i)
  let (i : Fin n) : IsProbabilityMeasure (ν i) := by
    change IsProbabilityMeasure ((potentialSquaredRadiusLaw n i.val V).map Real.sqrt)
    rw [← he i]
    exact radialConfinementProbabilityDensity_isProbability n i.val _
      (hV.continuous.comp Complex.continuous_ofReal) (hi i)
  choose T hTc hmap hb using fun i : Fin n =>
    rhoConvex_radial_gaussian_transport n i.val hn ρ hρ hV hrot hc
  have hmap' (i : Fin n) : (gaussianReal 0 1).map (T i) = ν i := by
    rw [hmap i, he i]
  have hκ : 0 < (n : ℝ) * ρ := mul_pos (Nat.cast_pos.mpr hn) hρ
  let L : ℝ≥0 := ⟨(Real.sqrt ((n : ℝ) * ρ))⁻¹, inv_nonneg.mpr (Real.sqrt_nonneg _)⟩
  have h := coordinateGaussianTransport_product_lsi ν T hTc hmap' L hb f hf hfLip C hC hfBound
  change squareEntropy (potentialRadiusProduct n V) f ≤
    (2 * (Real.sqrt ((n : ℝ) * ρ))⁻¹ ^ 2) * ∫ r,
      directionalEnergy (fun i : Fin n => Pi.single i 1) f r ∂potentialRadiusProduct n V at h
  calc
    _ ≤ _ := h
    _ = _ := by rw [inv_pow, Real.sq_sqrt hκ.le]; ring

end
end GinibrePoincare
