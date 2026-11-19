/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianOrthogonalGlobalPathFactorization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalFreeInitial
public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalOUPathElement

/-! # Factorization as continuous path elements

`ginibrePathCenter` and `ginibrePathRecenter` apply the two linear projections
to entire continuous configuration paths. Their measurability follows from
continuous postcomposition on the continuous-map spaces.

On the full-measure event of infinite lifetime, the canonical global path
agrees pointwise with the maximal process. The already-proved center OU and
relative canonical factorization identities then identify the projected
continuous path elements by extensionality. Negative real times are evaluated
through `Real.toNNReal`, consistently with the canonical path construction.
This path-space formulation is what later allows independence to concern
whole paths, rather than only their values at fixed times. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance (n : ℕ) : MeasurableSpace C(ℝ, Configuration n) := borel _
local instance (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
/-- The Borel σ-algebra on continuous complex paths `C(ℝ, ℂ)`. -/
local instance instBorelBrownianOrthogonalGlobalPathFactorization63 :
    MeasurableSpace C(ℝ, ℂ) := borel _
local instance : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩

/-- The complex path `t ↦ ∑ j, X t j` of coordinate sums along the configuration path `X`. -/
def ginibrePathCenter (n : ℕ) (X : C(ℝ, Configuration n)) : C(ℝ, ℂ) :=
  (⟨coordinateSumCLM n, (coordinateSumCLM n).continuous⟩ : C(Configuration n, ℂ)).comp X

/-- The configuration path obtained by applying the recentering projection `recenteredCLM n`
to `X` at every time. -/
def ginibrePathRecenter (n : ℕ) (X : C(ℝ, Configuration n)) : C(ℝ, Configuration n) :=
  (⟨recenteredCLM n, (recenteredCLM n).continuous⟩ : C(Configuration n, Configuration n)).comp X

theorem ginibrePathCenter_measurable (n : ℕ) : Measurable (ginibrePathCenter n) :=
  (⟨coordinateSumCLM n, (coordinateSumCLM n).continuous⟩ : C(Configuration n,
      ℂ)).continuous_postcomp.measurable

theorem ginibrePathRecenter_measurable (n : ℕ) : Measurable (ginibrePathRecenter n) :=
  (⟨recenteredCLM n, (recenteredCLM n).continuous⟩ : C(Configuration n, Configuration
      n)).continuous_postcomp.measurable

theorem ginibreBrownian_global_path_center {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ginibrePathCenter n (ginibreDrivenGlobalPathElement α
      (⟨z, hz⟩, ginibreBrownianFullContinuousNoise n B α ω)) =
      ginibreOUPathElement n α (coordinateSum z,
        ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω)) := by
  filter_upwards [ginibreBrownianMaximalLifetime_top_ae hn α z hz B P hB hind,
    ginibreBrownian_center_OU_factorization hn α z hz B P hB hind] with ω hL hS
  have hL' : ginibreDrivenMaximalLifetime n α
      (ginibreBrownianFullContinuousNoise n B α ω).val z = ⊤ := hL
  apply ContinuousMap.ext
  intro t
  simp only [ginibrePathCenter, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    ginibreDrivenGlobalPathElement, dite_eq_left hL', coordinateSumCLM_apply,
    ginibreOUPathElement]
  exact hS (Real.toNNReal t)

theorem ginibreBrownian_global_path_recenter {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ginibrePathRecenter n (ginibreDrivenGlobalPathElement α
      (⟨z, hz⟩, ginibreBrownianFullContinuousNoise n B α ω)) =
      ginibreDrivenGlobalPathElement α (⟨recenteredConfiguration n z, collisionFree_recentered hz⟩,
        ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α ω)) := by
  filter_upwards [ginibreBrownianMaximalLifetime_top_ae hn α z hz B P hB hind,
    ginibreBrownian_recentered_canonical_factorization hn α z hz B P hB hind] with ω hL hW
  have hL' : ginibreDrivenMaximalLifetime n α
      (ginibreBrownianFullContinuousNoise n B α ω).val z = ⊤ := hL
  apply ContinuousMap.ext
  intro t
  simp only [ginibrePathRecenter, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    ginibreDrivenGlobalPathElement, dite_eq_left hL', dite_eq_left hW.1, recenteredCLM_apply]
  exact hW.2 (Real.toNNReal t)

end
end GinibrePoincare
