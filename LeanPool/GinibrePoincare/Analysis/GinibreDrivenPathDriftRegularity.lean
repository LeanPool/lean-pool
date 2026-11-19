/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathDriftRegularity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDynamicsDrift
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.ODE.ExistUnique

/-! # Smoothness of the actual singular drift away from collisions -/

@[expose] public section
open scoped BigOperators ContDiff NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreCoulombInteraction_contDiffAt (n : ℕ) (z : Configuration n)
    (hz : CollisionFree z) : ContDiffAt ℝ ∞ (ginibreCoulombInteraction n) z := by
  classical
  apply contDiffAt_pi.mpr
  intro j
  unfold ginibreCoulombInteraction
  apply ContDiffAt.sum
  intro k hk
  by_cases hjk : j = k
  · subst k
    simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Configuration n => (0 : ℂ)) z)
  · have hdiff : ContDiff ℝ ∞ (fun w : Configuration n => w j - w k) :=
      (ContinuousLinearMap.proj j : Configuration n →L[ℝ] ℂ).contDiff.sub
        (ContinuousLinearMap.proj k : Configuration n →L[ℝ] ℂ).contDiff
    have hnorm : ContDiff ℝ ∞ (fun w : Configuration n => Complex.normSq (w j - w k)) := by
      have hr := Complex.reCLM.contDiff.comp hdiff
      have hi := Complex.imCLM.contDiff.comp hdiff
      convert! (hr.mul hr).add (hi.mul hi) using 1
    have hne : (Complex.normSq (z j - z k) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr
        (fun h => hjk (hz (sub_eq_zero.mp (Complex.normSq_eq_zero.mp h))))
    convert! hdiff.contDiffAt.mul
      ((Complex.ofRealCLM.contDiff.comp hnorm).contDiffAt.inv hne) using 1

theorem ginibreLangevinDrift_contDiffAt (n : ℕ) (α : ℝ) (z : Configuration n)
    (hz : CollisionFree z) : ContDiffAt ℝ ∞ (ginibreLangevinDrift n α) z := by
  apply contDiffAt_pi.mpr
  intro j
  exact ((ContinuousLinearMap.proj j : Configuration n →L[ℝ] ℂ).contDiff.contDiffAt.const_smul
      _).add
    (((ContinuousLinearMap.proj j : Configuration n →L[ℝ] ℂ).contDiff.contDiffAt.comp z
      (ginibreCoulombInteraction_contDiffAt n z hz)).const_smul _)

theorem ginibreLangevinDrift_local_lipschitz (n : ℕ) (α : ℝ) (z : Configuration n)
    (hz : CollisionFree z) : ∃ K : ℝ≥0, ∃ s ∈ nhds z,
      LipschitzOnWith K (ginibreLangevinDrift n α) s := by
  exact ((ginibreLangevinDrift_contDiffAt n α z hz).of_le (by norm_num)).exists_lipschitzOnWith

theorem ginibreLangevinDrift_local_integral_curve (n : ℕ) (α : ℝ) (z : Configuration n)
    (hz : CollisionFree z) (t₀ : ℝ) :
    ∃ X : ℝ → Configuration n, X t₀ = z ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioo (t₀-ε) (t₀+ε), HasDerivAt X (ginibreLangevinDrift n α (X t)) t := by
  exact ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
    ((ginibreLangevinDrift_contDiffAt n α z hz).of_le (by norm_num)) t₀

end
end GinibrePoincare
