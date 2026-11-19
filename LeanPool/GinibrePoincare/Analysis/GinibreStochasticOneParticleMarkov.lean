/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticOneParticleMarkov.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOUPlanarMarkov
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOneParticleLaw

/-! # Whole-past Markov property of the actual one-particle Ginibre solution -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreOneParticleBrownianPath_whole_past_markov {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P)
    (α s t : ℝ≥0) (z : Configuration 1)
    (f : Configuration 1 → ℝ) (hf : Measurable f) (C : ℝ) (hbound : ∀ y, ‖f y‖ ≤ C) :
    P[(fun ω => f (ginibreOneParticleBrownianPath Br Bi α z (s+t) ω)) |
      ginibrePlanarBrownianPastMeasurableSpace Br Bi s] =ᵐ[P]
      (fun ω => ∫ y, f y ∂ginibreOneParticleOUTransition α t
        (ginibreOneParticleBrownianPath Br Bi α z s ω)) := by
  let F : ℝ × ℝ → Configuration 1 := fun p _ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)
  let rate : ℝ≥0 := 2 * α
  have hF : Measurable F := by fun_prop
  have h := ginibreBrownianOU_planar_whole_past_markov Br Bi P hBr hBi hind rate s t
    (z 0).re (z 0).im (f ∘ F) (hf.comp hF) C (fun y => hbound (F y))
  have hproj := ginibreOneParticleBrownianPath_projections Br Bi P hBr hBi α z
  have he : (fun ω => f (ginibreOneParticleBrownianPath Br Bi α z (s+t) ω)) =ᵐ[P]
      (fun ω => (f ∘ F) (ginibreBrownianOU Br rate (Real.sqrt (rate : ℝ)) (z 0).re (s+t) ω,
        ginibreBrownianOU Bi rate (Real.sqrt (rate : ℝ)) (z 0).im (s+t) ω)) := by
    filter_upwards [hproj] with ω hω
    congr 1
    ext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    apply Complex.ext
    · simpa [F, rate] using (hω (s+t)).1
    · simpa [F, rate] using (hω (s+t)).2
  apply ((condExp_congr_ae (m := ginibrePlanarBrownianPastMeasurableSpace Br Bi s) he).trans
      h).trans
  filter_upwards [hproj] with ω hω
  unfold ginibreOneParticleOUTransition
  rw [integral_map hF.aemeasurable hf.stronglyMeasurable.aestronglyMeasurable]
  have hr := (hω s).1
  have hi := (hω s).2
  simp only [Function.comp_apply]
  simp only [rate, NNReal.coe_mul, NNReal.coe_ofNat, hr, hi]

end
end GinibrePoincare
