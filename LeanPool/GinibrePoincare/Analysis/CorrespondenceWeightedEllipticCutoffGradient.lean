/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticCutoffGradient.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticLocalSobolev
/-!
# Correspondence weighted elliptic cutoff gradient

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceWeightedElliptic_cutoff_gradient`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem correspondenceWeightedElliptic_cutoff_gradient
    {ι : Type*} [Finite ι] (v : ι → E) (f χ η : E → ℝ)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hχ : ∀ x ∈ tsupport η, χ x = 1)
    (u : Lp ℝ 2 (volume : Measure E)) (hu : (u : E → ℝ) =ᵐ[volume] (fun x => χ x * f x))
    (J : ι → Lp ℝ 2 (volume : Measure E))
    (hJ : ∀ i (θ : E → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, θ x * J i x) = -(∫ x, fderiv ℝ θ x (v i) * u x)) :
    ∀i, MemLp (fun x=>η x*J i x+fderiv ℝ η x (v i)*f x) 2 volume ∧
      HasCompactSupport (fun x=>η x*J i x+fderiv ℝ η x (v i)*f x) ∧
      ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
        (∫x, θ x*(η x*J i x+fderiv ℝ η x (v i)*f x))=
          -(∫x, fderiv ℝ θ x (v i)*(η x*f x)) := by
  have := Fintype.ofFinite ι
  intro i
  obtain ⟨U, G, hU, hG, hw⟩ := correspondenceWeightedElliptic_compact_C1_product u (J i) (v i) (hJ
      i)
    η (hη.of_le (by norm_num)) hc
  have hV : (U : E→ℝ)=ᵐ[volume](fun x=>η x*f x) := by
    filter_upwards [hU, hu] with x hUx hux
    rw [hUx, hux]
    by_cases hx : x∈tsupport η
    · rw [hχ x hx]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hR : (G : E→ℝ)=ᵐ[volume](fun x=>η x*J i x+fderiv ℝ η x (v i)*f x) := by
    filter_upwards [hG, hu] with x hGx hux
    rw [hGx, hux]
    by_cases hx : x∈tsupport η
    · rw [hχ x hx]
      ring
    · have hd : fderiv ℝ η x (v i)=0 := by
        rw [fderiv_of_notMem_tsupport (𝕜:=ℝ) hx]
        rfl
      simp [hd]
  refine ⟨(Lp.memLp G).ae_eq hR,?_,?_⟩
  · exact (hc.mul_right).add ((hc.fderiv_apply ℝ (v i)).mul_right)
  · intro θ hθ hθc
    have he := hw θ hθ hθc
    have hl : (∫x, θ x*G x)=∫x, θ x*(η x*J i x+fderiv ℝ η x (v i)*f x) := by
      apply integral_congr_ae
      filter_upwards [hR] with x hx
      rw [hx]
    have hr : (∫x, fderiv ℝ θ x (v i)*U x)=∫x, fderiv ℝ θ x (v i)*(η x*f x) := by
      apply integral_congr_ae
      filter_upwards [hV] with x hx
      rw [hx]
    rwa [hl, hr] at he
end
end GinibrePoincare
