/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexPotentialRadialLSI.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexRadialGradientTransfer
public import LeanPool.GinibrePoincare.Analysis.StrongConvexPotentialPartition

/-!
# Strong convex potential radial LSI

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `rhoConvex_potential_smooth_radial_lsi`, and the route-independent reductions
`potential_radial_lsi_of_radiusProduct_lsi` and `potential_smooth_radial_lsi_of_profile_lsi`
shared with the Bakry–Émery route.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff NNReal
namespace GinibrePoincare
noncomputable section

/-- Transfer of a radius-product LSI to the actual interacting nonquadratic log gas: an LSI
with constant `c` for bounded Lipschitz `C¹` profiles under the radius product gives the same
LSI for the corresponding symmetric magnitude observables. -/
theorem potential_radial_lsi_of_radiusProduct_lsi (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) {c : ℝ}
    (hlsi : ∀ F : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 F → ∀ {K : ℝ≥0}, LipschitzWith K F →
      ∀ C : ℝ, 0 ≤ C → (∀ r, |F r| ≤ C) →
      squareEntropy (potentialRadiusProduct n V) F ≤ c *
        ∫ r, directionalEnergy (fun i : Fin n => Pi.single i 1) F r ∂potentialRadiusProduct n V)
    (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ 1 F)
    (hs : IsSymmetricRadiusTest n F) {K : ℝ≥0} (hLip : LipschitzWith K F)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ r, |F r| ≤ C) :
    squareEntropy (potentialMeasure n V) (fun z => F (magnitudeVector z)) ≤
      c * potentialGradientEnergy n V (fun z => F (magnitudeVector z)) := by
  have hfin := rhoConvex_potentialPartition_lt_top n hn ρ hρ hV hrot hc
  rw [potential_magnitude_entropy_eq_radiusProduct n hn hV.continuous hrot hfin
    F hF.continuous hs C hb,
    potential_magnitude_gradient_energy_eq_radiusProduct n hn hV.continuous hrot hfin
      F hF hs hLip]
  exact hlsi F hF hLip C hC hb

/-- Reduction of the paper's smooth compact radial observables to their magnitude profiles:
an LSI with constant `c` for bounded Lipschitz `C¹` symmetric magnitude profiles gives the same
LSI for every smooth compact symmetric radial observable, with all profile regularity and
boundedness derived from the observable itself. -/
theorem potential_smooth_radial_lsi_of_profile_lsi (n : ℕ) {V : Potential} {c : ℝ}
    (hlsi : ∀ F : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 F → IsSymmetricRadiusTest n F →
      ∀ {K : ℝ≥0}, LipschitzWith K F → ∀ C : ℝ, 0 ≤ C → (∀ r, |F r| ≤ C) →
      squareEntropy (potentialMeasure n V) (fun z => F (magnitudeVector z)) ≤
        c * potentialGradientEnergy n V (fun z => F (magnitudeVector z)))
    (f : Configuration n → ℝ) (hf : IsSmoothCompactSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    squareEntropy (potentialMeasure n V) f ≤ c * potentialGradientEnergy n V f := by
  have hF := contDiff_magnitudeProfile f hf.1
  have hsupp := compactSupport_magnitudeProfile f hf.2.1
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsupp hF (by simp)
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hF.continuous
  have he : f = (fun z => magnitudeProfile f (magnitudeVector z)) := by
    funext z
    exact radial_eq_magnitudeProfile f hr z
  have hb : ∀ r, |magnitudeProfile f r| ≤ max C 0 := by
    intro r
    have hh : |magnitudeProfile f r| ≤ C := by simpa only [Real.norm_eq_abs] using hC r
    exact hh.trans (le_max_left _ _)
  have ht := hlsi (magnitudeProfile f) (hF.of_le (by simp)) (magnitudeProfile_symmetric f hf.2.2)
    hK (max C 0) (le_max_right _ _) hb
  rwa [← he] at ht

/-- Radial LSI for the interacting nonquadratic log gas, obtained from its
Kostlan law and the derived contracting Gaussian quantiles. -/
theorem rhoConvex_potential_radial_lsi (n : ℕ) (hn : 0 < n)
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
  exact rhoConvex_radiusProduct_lsi n hn ρ hρ hV hrot hc F hF hLip C hC hb

/-- The paper's smooth compact radial observables, with all profile regularity
and boundedness derived from the observable itself. -/
theorem rhoConvex_potential_smooth_radial_lsi (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : Configuration n → ℝ) (hf : IsSmoothCompactSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    squareEntropy (potentialMeasure n V) f ≤
      (2 / ((n : ℝ) * ρ)) * potentialGradientEnergy n V f := by
  refine potential_smooth_radial_lsi_of_profile_lsi n ?_ f hf hr
  intro F hF hs K hLip C hC hb
  exact rhoConvex_potential_radial_lsi n hn ρ hρ hV hrot hc F hF hs hLip C hC hb

end
end GinibrePoincare
