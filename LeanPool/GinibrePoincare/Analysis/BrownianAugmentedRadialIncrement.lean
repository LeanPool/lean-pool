/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianAugmentedRadialIncrement.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalRadialFrame
public import LeanPool.GinibrePoincare.Analysis.BrownianAugmentedOrthogonalIncrement
public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalCoordinateLaw

/-!
# Brownian augmented radial increment

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianFamily_augmented_radial_fresh_increment`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
attribute [local irreducible] brownianRadialFrame brownianHouseholder

theorem brownianFamily_augmented_radial_fresh_increment {Ω ι A : Type*}
    [mAmbient : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [MeasurableSpace A]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0)
    (Y : Ω → A)
    (hY : @Measurable Ω A (ginibreBrownianAugmentedFiltration B P hB s) _ Y)
    (Φ : A → EuclideanSpace ℝ ι) (hΦ : Measurable Φ) (i : ι) :
    let X := fun ω => WithLp.toLp 2 (fun j => B j (s+t) ω - B j s ω)
    let e := EuclideanSpace.single i (1 : ℝ)
    let Z := fun ω => brownianRadialFrame (Φ (Y ω)) e (X ω)
    HasLaw Z (scaledStandardGaussian (EuclideanSpace ℝ ι) t) P ∧
      IndepFun Y Z P ∧
      (∀ j, HasLaw (fun ω => Z ω j) (gaussianReal 0 t) P) ∧
      iIndepFun (fun j ω => Z ω j) P ∧
      ∀ ω, Z ω i = inner ℝ (brownianRadialUnitVector (Φ (Y ω)) e) (X ω) := by
  classical
  dsimp only
  let e := EuclideanSpace.single i (1 : ℝ)
  let U := fun y => brownianRadialFrame (Φ y) e
  have hU : Measurable (fun p : A × EuclideanSpace ℝ ι => U p.1 p.2) :=
    (brownianRadialFrame_measurable e).comp ((hΦ.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨hl, hi⟩ := brownianFamily_augmented_orthogonal_fresh_increment B P hB hind s t Y hY U hU
  obtain ⟨hcoord, hindcoord⟩ := isotropicGaussian_coordinates_independent P t _ hl
  refine ⟨hl, hi, hcoord, hindcoord, ?_⟩
  intro ω
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have hh := brownianRadialFrame_radial_coordinate
    (Φ (Y ω)) e
    (WithLp.toLp 2 (fun j => B j (s+t) ω - B j s ω)) he
  simpa only [e, EuclideanSpace.inner_single_left, map_one, one_mul] using hh

end
end GinibrePoincare
