/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalFreshIncrement.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalPiGaussianLaw
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyPast

/-!
# Brownian orthogonal fresh increment

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianFamily_past_orthogonal_fresh_increment`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- An orthogonal rotation selected from any finite block of the genuine joint
Brownian past preserves the fresh full Gaussian increment and its independence. -/
theorem brownianFamily_past_orthogonal_fresh_increment {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (B : ι → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0)
    (m : ℕ) (τ : Fin m → ℝ≥0) (hτ : ∀ j, τ j ≤ s)
    (U : (ι × Fin m → ℝ) → EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hU : Measurable (fun p : (ι × Fin m → ℝ) × EuclideanSpace ℝ ι => U p.1 p.2)) :
    let Y := fun ω (q : ι × Fin m) => B q.1 (τ q.2) ω
    let X := fun ω => WithLp.toLp 2 (fun i => B i (s+t) ω - B i s ω)
    HasLaw (fun ω => U (Y ω) (X ω)) (scaledStandardGaussian (EuclideanSpace ℝ ι) t) P ∧
      IndepFun Y (fun ω => U (Y ω) (X ω)) P := by
  classical
  dsimp only
  let Y := fun ω (q : ι × Fin m) => B q.1 (τ q.2) ω
  let X := fun ω => WithLp.toLp 2 (fun i => B i (s+t) ω - B i s ω)
  have hy : AEMeasurable Y P := AEMeasurable.of_eval
    (fun q => (hB q.1).aemeasurable (τ q.2))
  let ν := P.map Y
  let : IsProbabilityMeasure ν := (by infer_instance)
  have hyl : HasLaw Y ν P := ⟨hy, rfl⟩
  have hxl : HasLaw X (scaledStandardGaussian (EuclideanSpace ℝ ι) t) P := by
    exact (show HasLaw (WithLp.toLp 2)
      (scaledStandardGaussian (EuclideanSpace ℝ ι) t)
      (Measure.pi (fun _ : ι => gaussianReal 0 t)) from
        ⟨by fun_prop, piGaussianReal_map_toLp_scaledStandard ι t⟩).fun_comp
      (ginibreBrownian_family_increment_hasLaw B P hB hind s t)
  have hi : IndepFun Y X P := by
    have hp := (ginibreBrownian_family_increment_independent_past B P hB hind s t).symm
    exact hp.comp
      (show Measurable (fun p : (ι × Set.Iic s → ℝ) =>
        fun q : ι × Fin m => p (q.1, ⟨τ q.2, hτ q.2⟩)) by fun_prop)
      (show Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) by fun_prop)
  exact independent_past_orthogonal_gaussian_transform (EuclideanSpace ℝ ι) P ν t Y X hyl hxl hi U
      hU

end
end GinibrePoincare
