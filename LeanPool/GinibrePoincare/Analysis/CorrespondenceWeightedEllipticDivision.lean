/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticDivision.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticProduct
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticDensity
/-!
# Correspondence weighted elliptic division

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceWeightedElliptic_divide_density`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Actual localized density H¹ regularity gives actual localized ordinary
H¹ regularity, even when the positive density is only C¹. -/
theorem correspondenceWeightedElliptic_divide_density
    {ι : Type*} [Finite ι] (v : ι → E) (ρ : E → ℝ) (hρ : ContDiff ℝ 1 ρ)
    (hp : ∀ x, 0 < ρ x) (f η : E → ℝ) (_ : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (u : Lp ℝ 2 (volume : Measure E))
    (hu : (u : E → ℝ) =ᵐ[volume] (fun x => η x * (ρ x * f x)))
    (g : ι → Lp ℝ 2 (volume : Measure E))
    (hg : ∀ i (θ : E → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, θ x * g i x) = -(∫ x, fderiv ℝ θ x (v i) * u x)) :
    ∃G : ι→Lp ℝ 2 (volume : Measure E),
      ∀i (θ : E→ℝ), ContDiff ℝ ∞ θ→HasCompactSupport θ→
        (∫x, θ x*G i x)= -(∫x, fderiv ℝ θ x (v i)*(η x*f x)) := by
  have := Fintype.ofFinite ι
  obtain ⟨χ, hχ, hχc, hχone⟩ := ginibreLocalRegularity_exists_compact_cutoff (tsupport η) hc
  let q : E→ℝ := fun x=>χ x/(ρ x)
  have hq : ContDiff ℝ 1 q := (hχ.of_le (by norm_num)).div hρ (fun x=>(hp x).ne')
  have hqc : HasCompactSupport q := by
    change HasCompactSupport (χ*(fun x=>(ρ x)⁻¹))
    exact hχc.mul_right
  have hrep (U : Lp ℝ 2 (volume : Measure E))
      (hU : (U : E→ℝ)=ᵐ[volume](fun x=>q x*u x)) :
      (U : E→ℝ)=ᵐ[volume](fun x=>η x*f x) := by
    filter_upwards [hU, hu] with x hUx hux
    rw [hUx, hux]
    dsimp [q]
    by_cases hx : x∈tsupport η
    · rw [(hχone x hx).eq_of_nhds]
      field_simp [(hp x).ne']
      simp
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have hex (i) : ∃G : Lp ℝ 2 (volume : Measure E),
      ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
        (∫x, θ x*G x)= -(∫x, fderiv ℝ θ x (v i)*(η x*f x)) := by
    obtain ⟨U, G, hU, hG, hweak⟩ := correspondenceWeightedElliptic_compact_C1_product u (g i) (v i)
      (hg i) q hq hqc
    refine ⟨G,?_⟩
    intro θ hθ hθc
    rw [hweak θ hθ hθc]
    congr 1
    apply integral_congr_ae
    filter_upwards [hrep U hU] with x hx
    rw [hx]
  choose G hG using hex
  exact ⟨G, hG⟩
end
end GinibrePoincare
