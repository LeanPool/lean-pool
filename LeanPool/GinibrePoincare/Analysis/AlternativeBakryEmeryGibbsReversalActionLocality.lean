/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsReversalActionLocality.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalSurvival
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOUActionLocality
/-!
# Alternative Bakry Emery Gibbs reversal action locality

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryGibbsOUReference_action_of_prefix`.
-/

@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem bakryEmeryGibbs_gradient_action_congr {E : Type*} (T : ℝ) (hT : 0 ≤ T)
    (V A : E → ℝ) (x y : ℝ → E) (hxy : EqOn x y (Icc 0 T)) :
    gradientPathReversalWeight T V A x = gradientPathReversalWeight T V A y := by
  have hi : (∫ s in (0 : ℝ)..T, A (x s)) = ∫ s in (0 : ℝ)..T, A (y s) :=
    intervalIntegral.integral_congr (fun s hs => congrArg A (hxy (by simpa [uIcc_of_le hT] using
                                                                       hs)))
  simp only [gradientPathReversalWeight,
    hxy (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩),
    hxy (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩), hi]

theorem bakryEmeryGibbsOUAction_of_agrees {n : ℕ} (W : Configuration n → ℝ)
    (T : ℝ) (hT : 0 ≤ T) (x : C(Icc (0 : ℝ) T, Configuration n))
    (y : ℝ → Configuration n) (hy : ∀ s (hs : s ∈ Icc 0 T), y s = x ⟨s, hs⟩) :
    bakryEmeryGibbsOUAction W T hT x = gradientPathReversalWeight T
      (bakryEmeryGibbsRelativePotential W) (bakryEmeryGibbsOUActionIntegrand W) y := by
  let : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  have he : EqOn (ContinuousMap.IccExtendCM x) y (Icc 0 T) := by
    intro s hs
    rw [hy s hs, ContinuousMap.IccExtendCM_of_mem hs]
  exact bakryEmeryGibbs_gradient_action_congr T hT _ _ _ _ he

theorem bakryEmeryGibbsOUReference_action_of_prefix {Ω : Type*} {n : ℕ}
    (W : Configuration n → ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (sample : Ω)
    (Y : ℝ≥0 → Ω → Configuration n)
    (hY : ∀ t ≤ T, Y t sample = ginibreHamiltonianOUReferenceProcess n ((n : ℝ) ^ 2) z B t sample) :
    bakryEmeryGibbsOUAction W T T.property
      (ginibreHamiltonianOUReferenceHorizon n ((n : ℝ)^2) z B T sample) =
      gradientPathReversalWeight T (bakryEmeryGibbsRelativePotential W)
        (bakryEmeryGibbsOUActionIntegrand W) (fun s => Y s.toNNReal sample) := by
  apply bakryEmeryGibbsOUAction_of_agrees
  intro s hs
  exact hY s.toNNReal (by simpa using Real.toNNReal_le_toNNReal hs.2)

end
end GinibrePoincare
