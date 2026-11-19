/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticWeakCore.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorVariational
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCoreIdentification
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroup
public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-! Compact test equations suffice to identify the actual closed weak generator.
The passage to all weak tests uses the concrete collision-free form-core density. -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreTransitionAnalyticWeakCore_graph_iff {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u.val g)
    (hs : IsGinibreSymmetricWeakPair (u.val, g)) :
    (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
        (ginibreFullGenerator n hn).graph ↔
      ∀ (φ : Configuration n → ℝ) (hφ : IsTheoremOneNineCore φ),
        (1 / (n : ℝ)) * inner ℝ g (ginibreFullCoreGradient hn φ hφ) =
          -inner ℝ v.val (ginibreFullCoreValue hn φ hφ) := by
  rw [ginibreFullGenerator_ofReal_variational_iff hn u v g hu hs]
  constructor
  · intro heq φ hφ
    exact heq _ _ (ginibreFullCorePair hn φ hφ).property.1
      (ginibreFullCorePair hn φ hφ).property.2
  · intro heq w h hw hsw
    obtain ⟨q, hq, hlim⟩ := ginibreSymmetricWeakPair_exists_core_sequence hn w h hw hsw
    have hm (m : ℕ) :
        (1 / (n : ℝ)) * inner ℝ g (q m).2 = -inner ℝ v.val (q m).1 := by
      obtain ⟨φ, hφ, hvalue, hgradient⟩ := hq m
      have hg : (q m).2 = ginibreFullCoreGradient hn φ hφ := by
        apply Lp.ext
        exact hgradient.trans (ginibreFullCoreGradient_ae hn φ hφ).symm
      have hv : (q m).1 = ginibreFullCoreValue hn φ hφ := by
        apply Lp.ext
        exact hvalue.trans (ginibreFullCoreValue_ae hn φ hφ).symm
      rw [hg, hv]
      exact heq φ hφ
    have hl : Tendsto (fun p : GinibreFullValueL2 n × GinibreFullGradientL2 n =>
        (1 / (n : ℝ)) * inner ℝ g p.2) (𝓝 (w, h))
        (𝓝 ((1 / (n : ℝ)) * inner ℝ g h)) :=
      (continuous_const.mul (continuous_const.inner continuous_snd)).tendsto (w, h)
    have hr : Tendsto (fun p : GinibreFullValueL2 n × GinibreFullGradientL2 n =>
        -inner ℝ v.val p.1) (𝓝 (w, h)) (𝓝 (-inner ℝ v.val w)) :=
      (continuous_const.inner continuous_fst).neg.tendsto (w, h)
    exact tendsto_nhds_unique (hl.comp hlim)
      ((hr.comp hlim).congr (fun m => (hm m).symm))

/-- A genuine weak solution tested only against the original compact core is
the concrete analytic resolvent; no extra equation on the completed domain is
required. -/
theorem ginibreTransitionAnalyticWeakCore_resolvent {n : ℕ} (hn : 0 < n)
    (f u : ginibreFullSymmetricValues n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u.val g)
    (hs : IsGinibreSymmetricWeakPair (u.val, g))
    (heq : ∀ (φ : Configuration n → ℝ) (hφ : IsTheoremOneNineCore φ),
      inner ℝ u.val (ginibreFullCoreValue hn φ hφ) +
        (1 / (n : ℝ)) * inner ℝ g (ginibreFullCoreGradient hn φ hφ) =
          inner ℝ f.val (ginibreFullCoreValue hn φ hφ)) :
    ginibreFullSymmetricResolvent n hn f = u := by
  have hg := (ginibreTransitionAnalyticWeakCore_graph_iff hn u (u - f) g hu hs).mpr
    (by
      intro φ hφ
      change (1 / (n : ℝ)) * inner ℝ g (ginibreFullCoreGradient hn φ hφ) =
        -inner ℝ (u.val - f.val) (ginibreFullCoreValue hn φ hφ)
      rw [inner_sub_left]
      have ht := heq φ hφ
      linarith)
  have hr := (ginibreFullGenerator_graph_iff n hn _ _).mp hg
  rw [← map_sub, sub_sub_cancel, ginibreFullComplexResolvent_ofReal] at hr
  have hh := congrArg (ginibreFullSymmetricRe n) hr
  simpa using hh

end
end GinibrePoincare
