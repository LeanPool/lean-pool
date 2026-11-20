/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsReversalExhaustion.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianReversalMarginals
/-!
# Alternative Bakry Emery Gibbs reversal exhaustion

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryGibbs_full_reverse_of_killed_reversals`.
-/

@[expose] public section
open Set MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(Icc 0 T, Configuration n)`. -/
local instance bakryGibbsExhaustionPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance bakryGibbsExhaustion_pathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- Countable compact-ball exhaustion passes actual killed reversals to full
path reversal. This integration lemma requires the killed identities; the
concrete stochastic proof supplies them separately. -/
theorem bakryEmeryGibbs_full_reverse_of_killed_reversals (n : ℕ) (T : ℝ≥0)
    (μ : Measure C(Icc (0 : ℝ) (T : ℝ), Configuration n))
    (hKilled : ∀ k : ℕ,
      (μ.restrict (bakryEmeryGibbsCompactSurvival n T (k : ℝ))).map
        (fun x => x.comp (ginibreHamiltonianCompactReverseTime T T.property)) =
      μ.restrict (bakryEmeryGibbsCompactSurvival n T (k : ℝ))) :
    μ.map (fun x => x.comp (ginibreHamiltonianCompactReverseTime T T.property)) = μ := by
  let r : C(Icc (0 : ℝ) (T : ℝ), Configuration n) → C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
    fun x => x.comp (ginibreHamiltonianCompactReverseTime T T.property)
  have hr : Measurable r :=
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime T
        T.property)).measurable
  have hi : Function.Involutive r := by
    intro x
    ext t j
    change x ((ginibreHamiltonianCompactReverseTime T T.property)
      ((ginibreHamiltonianCompactReverseTime T T.property) t)) j = x t j
    have he : (ginibreHamiltonianCompactReverseTime T T.property)
        ((ginibreHamiltonianCompactReverseTime T T.property) t) = t := by
      apply Subtype.ext
      change (T : ℝ)-((T : ℝ)-t.val)=t.val
      ring
    rw [he]
  let e := MeasurableEquiv.ofInvolutive r hi hr
  let S : ℕ → Set C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
    fun k => bakryEmeryGibbsCompactSurvival n T (k : ℝ)
  have hpre (k : ℕ) : e ⁻¹' S k = S k := by
    ext x
    exact bakryEmeryGibbsCompactSurvival_reverse n T k x
  have hCov : (⋃ k, S k) = univ := bakryEmeryGibbsCompactSurvival_exhaustion n T
  have hEq : (μ.map e).restrict (⋃ k, S k) = μ.restrict (⋃ k, S k) := by
    apply Measure.restrict_iUnion_congr.mpr
    intro k
    rw [e.restrict_map, hpre]
    exact hKilled k
  rw [hCov, Measure.restrict_univ, Measure.restrict_univ] at hEq
  exact hEq

end
end GinibrePoincare
