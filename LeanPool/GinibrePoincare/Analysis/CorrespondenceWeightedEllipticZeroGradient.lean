/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticZeroGradient.lean.
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
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.MeanValue
/-!
# Correspondence weighted elliptic zero gradient

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceWeightedElliptic_zero_gradient_constant`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Convolution Topology
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A locally integrable function with every genuine ordinary directional
weak derivative zero is a.e. constant on the full real Euclidean space. -/
theorem correspondenceWeightedElliptic_zero_gradient_constant
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (u : E → ℝ)
    (hu : LocallyIntegrable u (volume : Measure E))
    (hw : ∀ i (θ : E → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, u x * fderiv ℝ θ x (b i)) = 0) :
    ∃c : ℝ, u=ᵐ[volume](fun _=>c) := by
  let φ := lsiMollifier E
  let U := fun m=>(φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u
  have hUs (m) : ContDiff ℝ ∞ (U m) := (φ m).hasCompactSupport_normed.contDiff_convolution_left
    _ ((φ m).contDiff_normed (n:=⊤)) hu
  have hUd (m) (x : E) : fderiv ℝ (U m) x=0 := by
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro i
    have hh := weakDirectionalDerivative_convolution volume u (fun _=>(0 : ℝ))
      ((φ m).normed volume) (b i) hu ((φ m).contDiff_normed (n:=⊤))
      (φ m).hasCompactSupport_normed
      (by intro θ hθ hc; rw [hw i θ hθ hc]; simp) x
    have hh0 : (fun _ : E=>(0 : ℝ))=(0 : E→ℝ) := rfl
    rw [hh0, convolution_zero] at hh
    simpa [U] using hh
  have hconst (m) (x y : E) : U m x=U m y :=
    is_const_of_fderiv_eq_zero ((hUs m).differentiable (by simp)) (hUd m) x y
  have hlim := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ:=(volume : Measure E)) (lsiMollifier_radius_tendsto E)
    (K:=2) (Filter.Eventually.of_forall (fun m=>by dsimp [lsiMollifier]; linarith)) hu
  obtain ⟨x, hx⟩ := Filter.Eventually.exists hlim
  refine ⟨u x,?_⟩
  filter_upwards [hlim] with y hy
  have he : Tendsto (fun m=>U m y) atTop (𝓝 (u x)) := hx.congr (fun m=>hconst m x y)
  exact tendsto_nhds_unique hy he
end
end GinibrePoincare
