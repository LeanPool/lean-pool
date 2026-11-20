/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticSobolevApproximation.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticC1Tests
/-!
# Correspondence weighted elliptic Sobolev approximation

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceWeightedElliptic_mollified_derivative_tendsto`.
-/

@[expose] public section
open MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Convolution Topology
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem correspondenceWeightedElliptic_mollified_derivative
    (f g : E → ℝ) (hf : MemLp f 2 (volume : Measure E)) (v : E)
    (hw : ∀ θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*g x)= -(∫x, fderiv ℝ θ x v*f x))
    (φ : ContDiffBump (0 : E)) (x : E) :
    fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x v=
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) x := by
  apply weakDirectionalDerivative_convolution volume f g _ v (hf.locallyIntegrable (by norm_num))
    (φ.contDiff_normed (n:=⊤)) φ.hasCompactSupport_normed
  intro θ hθ hc
  have he := hw θ hθ hc
  simpa only [mul_comm] using he

theorem correspondenceWeightedElliptic_mollified_derivative_memLp
    (f g : E → ℝ) (hf : MemLp f 2 (volume : Measure E))
    (hg : MemLp g 2 (volume : Measure E)) (hc : HasCompactSupport g) (v : E)
    (hw : ∀ θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*g x)= -(∫x, fderiv ℝ θ x v*f x)) (φ : ContDiffBump (0 : E)) :
    MemLp (fun x=>fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x v) 2 volume := by
  have he : (fun x=>fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x v)=
      φ.normed volume ⋆[lsmul ℝ ℝ, volume] g := by
    funext x
    exact correspondenceWeightedElliptic_mollified_derivative f g hf v hw φ x
  rw [he]
  exact correspondenceWeighted_memLp_bump_convolution_compact φ g hg hc

theorem correspondenceWeightedElliptic_mollified_derivative_toLp
    (f g : E → ℝ) (hf : MemLp f 2 (volume : Measure E))
    (hg : MemLp g 2 (volume : Measure E)) (hc : HasCompactSupport g) (v : E)
    (hw : ∀ θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*g x)= -(∫x, fderiv ℝ θ x v*f x)) (φ : ContDiffBump (0 : E)) :
    (correspondenceWeightedElliptic_mollified_derivative_memLp f g hf hg hc v hw φ).toLp
      (fun x=>fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x v)=
      correspondenceWeightedLebesgueSmoothCompactMollification φ g hg hc := by
  unfold correspondenceWeightedLebesgueSmoothCompactMollification l2SmoothCompactMollification
  apply Lp.ext
  filter_upwards [(correspondenceWeightedElliptic_mollified_derivative_memLp f g hf hg hc v hw
      φ).coeFn_toLp,
    (correspondenceWeighted_memLp_bump_convolution_compact φ g hg hc).coeFn_toLp] with x hx hy
  rw [hx, hy]
  exact correspondenceWeightedElliptic_mollified_derivative f g hf v hw φ x

theorem correspondenceWeightedElliptic_mollified_derivative_tendsto
    (f g : E → ℝ) (hf : MemLp f 2 (volume : Measure E))
    (hg : MemLp g 2 (volume : Measure E)) (hc : HasCompactSupport g) (v : E)
    (hw : ∀ θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*g x)= -(∫x, fderiv ℝ θ x v*f x)) :
    Tendsto (fun m=>(correspondenceWeightedElliptic_mollified_derivative_memLp f g hf hg hc v hw
        (lsiMollifier E m)).toLp
      (fun x=>fderiv ℝ ((lsiMollifier E m).normed volume ⋆[lsmul ℝ ℝ, volume] f) x v)) atTop (𝓝
          (hg.toLp g)) := by
  have hh := correspondenceWeighted_lebesgueSmoothCompactMollification_tendsto _
      (lsiMollifier_radius_tendsto E) g hg hc
  apply hh.congr
  intro m
  exact (correspondenceWeightedElliptic_mollified_derivative_toLp f g hf hg hc v hw (lsiMollifier E
      m)).symm
end
end GinibrePoincare
