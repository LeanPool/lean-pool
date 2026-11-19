/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticGraphUniqueness.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticDissipativeUniqueness
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorEnergy

/-!
# Ginibre transition analytic graph uniqueness

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreFullGenerator_real_orbit_unique`,
`ginibreFullGenerator_real_scaled_orbit_unique`,
`ginibreFullSymmetric_operators_eq_on_resolvent_range`.
-/

@[expose] public section

noncomputable section
open Set
namespace GinibrePoincare

/-- Dissipation for differences in the actual real full generator graph. -/
theorem ginibreFullGenerator_real_difference_dissipative {n : ℕ} (hn : 0 < n)
    (u v a b : ginibreFullSymmetricValues n)
    (hu : ginibreFullSymmetricResolvent n hn (u - a) = u)
    (hv : ginibreFullSymmetricResolvent n hn (v - b) = v) :
    inner ℝ (u-v) (a-b) ≤ 0 := by
  have heq : ginibreFullSymmetricResolvent n hn ((u-v)-(a-b))=u-v := by
    have hsub : (u-v)-(a-b)=(u-a)-(v-b) := by abel
    rw [hsub, map_sub, hu, hv]
  have hg : (ginibreFullSymmetricOfReal n (u-v),
      ginibreFullSymmetricOfReal n (a-b)) ∈ (ginibreFullGenerator n hn).graph := by
    rw [ginibreFullGenerator_graph_iff, ← map_sub, ginibreFullComplexResolvent_ofReal, heq]
  obtain ⟨g, _, _, he⟩ := ginibreFullGenerator_real_energy_identity hn _ _ hg
  have hp : 0 ≤ ginibreWeakEnergy n g := mul_nonneg (by positivity) (sq_nonneg _)
  have hi : inner ℝ (u-v) (a-b)=inner ℝ (a-b).val (u-v).val := by
    exact real_inner_comm _ _
  rw [hi]
  linarith

/-- Actual differentiable real generator orbits with the same initial value
coincide, without any assumed identification of semigroups. -/
theorem ginibreFullGenerator_real_orbit_unique {n : ℕ} (hn : 0 < n)
    (x y vx vy : ℝ → ginibreFullSymmetricValues n) (T : ℝ) (hT : 0 ≤ T)
    (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    (hdx : ∀ s ∈ Ioo 0 T, HasDerivAt x (vx s) s)
    (hdy : ∀ s ∈ Ioo 0 T, HasDerivAt y (vy s) s)
    (hgx : ∀ s ∈ Ioo 0 T, ginibreFullSymmetricResolvent n hn (x s - vx s) = x s)
    (hgy : ∀ s ∈ Ioo 0 T, ginibreFullSymmetricResolvent n hn (y s - vy s) = y s)
    (hinit : x 0 = y 0) : ∀ s ∈ Icc 0 T, x s=y s := by
  apply realHilbert_orbit_unique_of_dissipative_derivative x y vx vy T hT hx hy hdx hdy
  · intro s hs
    exact ginibreFullGenerator_real_difference_dissipative hn _ _ _ _ (hgx s hs) (hgy s hs)
  · exact hinit

/-- Orbit uniqueness with the genuine nonnegative paper-speed scaling. -/
theorem ginibreFullGenerator_real_scaled_orbit_unique {n : ℕ} (hn : 0 < n)
    (x y ax ay : ℝ → ginibreFullSymmetricValues n) (c T : ℝ)
    (hc : 0 ≤ c) (hT : 0 ≤ T)
    (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    (hdx : ∀ s ∈ Ioo 0 T, HasDerivAt x (c • ax s) s)
    (hdy : ∀ s ∈ Ioo 0 T, HasDerivAt y (c • ay s) s)
    (hgx : ∀ s ∈ Ioo 0 T, ginibreFullSymmetricResolvent n hn (x s - ax s) = x s)
    (hgy : ∀ s ∈ Ioo 0 T, ginibreFullSymmetricResolvent n hn (y s - ay s) = y s)
    (hinit : x 0 = y 0) : ∀ s ∈ Icc 0 T, x s=y s := by
  apply realHilbert_orbit_unique_of_dissipative_derivative x y
    (fun s => c • ax s) (fun s => c • ay s) T hT hx hy hdx hdy
  · intro s hs
    rw [← smul_sub c (ax s) (ay s), real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos hc
      (ginibreFullGenerator_real_difference_dissipative hn _ _ _ _ (hgx s hs) (hgy s hs))
  · exact hinit

/-- Equality on the true full resolvent range extends to all symmetric L². -/
theorem ginibreFullSymmetric_operators_eq_on_resolvent_range {n : ℕ} (hn : 0 < n)
    (P Q : ginibreFullSymmetricValues n →L[ℝ] ginibreFullSymmetricValues n)
    (heq : ∀ u, P (ginibreFullSymmetricResolvent n hn u) =
      Q (ginibreFullSymmetricResolvent n hn u)) : P=Q := by
  apply ContinuousLinearMap.ext
  exact congrFun ((ginibreFullSymmetricResolvent_denseRange n hn).equalizer
    P.continuous Q.continuous (funext heq))

end GinibrePoincare
