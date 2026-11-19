/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianTiltFreshLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianTiltJointLaw
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGirsanovMeasure

/-!
# Brownian integral Gaussian tilt fresh law

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `gaussianVectorPredictableTilt_centered_fresh`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- The actual normalized predictable tilt preserves the past marginal and
makes the drift-corrected innovation a fresh centered Gaussian vector. -/
theorem gaussianVectorPredictableTilt_centered_fresh {Ω α ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → α) (X : Ω → ι → ℝ)
    (hY : Measurable Y) (hXm : Measurable X) (v : ℝ≥0)
    (hX : HasLaw X (Measure.pi (fun _ : ι => gaussianReal 0 v)) P)
    (hind : IndepFun Y X P) (H : α → ι → ℝ) (Z : α → ℝ≥0∞)
    (hH : Measurable H) (hZ : Measurable Z) (hZn : (∫⁻ ω, Z (Y ω) ∂P)=1) :
    let Q := P.withDensity (fun ω => Z (Y ω)*
      ENNReal.ofReal (gaussianVectorExponentialTilt (H (Y ω)) v (X ω)))
    let W := fun ω i => X ω i-H (Y ω) i*(v : ℝ)
    HasLaw Y ((P.map Y).withDensity Z) Q ∧
      HasLaw W (Measure.pi (fun _ : ι => gaussianReal 0 v)) Q ∧ IndepFun Y W Q := by
  classical
  dsimp only
  let Q := P.withDensity (fun ω => Z (Y ω)*
    ENNReal.ofReal (gaussianVectorExponentialTilt (H (Y ω)) v (X ω)))
  let ν := (P.map Y).withDensity Z
  let γ := Measure.pi (fun _ : ι => gaussianReal 0 v)
  let W := fun ω i => X ω i-H (Y ω) i*(v : ℝ)
  have hW : Measurable W := by fun_prop
  have hνn : ν Set.univ=1 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_map hZ hY]
    exact hZn
  let : IsProbabilityMeasure ν := ⟨hνn⟩
  have hQn : Q Set.univ=1 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (gaussianVectorPredictableTilt_lintegral P Y X hY.aemeasurable v hX hind H Z hH hZ).trans
        hZn
  let : IsProbabilityMeasure Q := ⟨hQn⟩
  have hPair : HasLaw (fun ω => (Y ω, W ω)) (ν.prod γ) Q :=
    ⟨(hY.prodMk hW).aemeasurable,
      gaussianVectorPredictableTilt_centered_map P Y X hY hXm v hX hind H Z hH hZ⟩
  have hfst : HasLaw (Prod.fst : α×(ι→ℝ) → α) ν (ν.prod γ) := ⟨by fun_prop, by simp [γ]⟩
  have hsnd : HasLaw (Prod.snd : α×(ι→ℝ) → (ι→ℝ)) γ (ν.prod γ) := ⟨by fun_prop, by simp⟩
  have hYL : HasLaw Y ν Q := hfst.fun_comp hPair
  have hWL : HasLaw W γ Q := hsnd.fun_comp hPair
  exact ⟨hYL, hWL, (indepFun_iff_hasLaw_prodMk_prod hYL hWL).mpr hPair⟩

end
end GinibrePoincare
