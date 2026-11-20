/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorOrbits.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorRealEvolution
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorSmoothIdentification
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticDissipativeUniqueness
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupDynamics
/-!
# Correspondence operator orbits

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorGenerator_real_scaled_orbit_unique`,
`correspondenceOperator_operators_eq_on_resolvent_range`,
`correspondenceOperatorRealEvolution_graph_derivative`,
`correspondenceOperatorRealEvolution_preserves_graph`.
-/

@[expose] public section
open Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem correspondenceOperatorEvolution_hasDerivAt (n : ℕ) (hn : 0 < n)
    (u v : GinibreFullComplexL2 n) (hp : (u, v) ∈ (correspondenceOperatorGenerator n hn).graph)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => correspondenceOperatorEvolution n hn s.toNNReal u)
      (correspondenceOperatorEvolution n hn t.toNNReal v) t :=
  resolventGenerator_orbit_hasDerivAt _ (correspondenceOperatorComplexResolvent_isSelfAdjoint n hn)
    (correspondenceOperatorComplexResolvent_injective n hn)
        (correspondenceOperatorComplexResolvent_spectrum n hn)
    (correspondenceOperatorComplexResolvent_denseRange n hn) u v hp ht

theorem correspondenceOperatorGenerator_real_difference_dissipative {n : ℕ} (hn : 0 < n)
    (u v a b : GinibreFullValueL2 n)
    (hu : correspondenceOperatorValueResolvent n hn (u - a) = u)
    (hv : correspondenceOperatorValueResolvent n hn (v - b) = v) :
    inner ℝ (u-v) (a-b) ≤ 0 := by
  have heq : correspondenceOperatorValueResolvent n hn ((u-v)-(a-b))=u-v := by
    have hsub : (u-v)-(a-b)=(u-a)-(v-b) := by abel
    rw [hsub, map_sub, hu, hv]
  let r := correspondenceOperatorFormResolvent n hn ((u-v)-(a-b))
  have hv : correspondenceOperatorFormValue n hn r = u-v := heq
  have he := correspondenceOperatorFormResolvent_riesz n hn ((u-v)-(a-b)) r
  rw [correspondenceOperatorFormSpace_inner, hv, inner_sub_left] at he
  have hp : 0 ≤ (1/(n : ℝ))*inner ℝ (correspondenceOperatorFormGradient n hn r)
      (correspondenceOperatorFormGradient n hn r) := by
    rw [real_inner_self_eq_norm_sq]
    positivity
  have hcomm : inner ℝ (u-v) (a-b)=inner ℝ (a-b) (u-v) := real_inner_comm _ _
  rw [hcomm]
  simp only [inner_sub_left] at he ⊢
  linarith

/-- Actual differentiable real generator orbits with the same initial value
coincide, without any assumed identification of semigroups. -/
theorem correspondenceOperatorGenerator_real_orbit_unique {n : ℕ} (hn : 0 < n)
    (x y vx vy : ℝ → GinibreFullValueL2 n) (T : ℝ) (hT : 0 ≤ T)
    (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    (hdx : ∀ s ∈ Ioo 0 T, HasDerivAt x (vx s) s)
    (hdy : ∀ s ∈ Ioo 0 T, HasDerivAt y (vy s) s)
    (hgx : ∀ s ∈ Ioo 0 T, correspondenceOperatorValueResolvent n hn (x s - vx s) = x s)
    (hgy : ∀ s ∈ Ioo 0 T, correspondenceOperatorValueResolvent n hn (y s - vy s) = y s)
    (hinit : x 0 = y 0) : ∀ s ∈ Icc 0 T, x s=y s := by
  apply realHilbert_orbit_unique_of_dissipative_derivative x y vx vy T hT hx hy hdx hdy
  · intro s hs
    exact correspondenceOperatorGenerator_real_difference_dissipative hn _ _ _ _ (hgx s hs) (hgy s
        hs)
  · exact hinit

/-- Orbit uniqueness with the genuine nonnegative paper-speed scaling. -/
theorem correspondenceOperatorGenerator_real_scaled_orbit_unique {n : ℕ} (hn : 0 < n)
    (x y ax ay : ℝ → GinibreFullValueL2 n) (c T : ℝ)
    (hc : 0 ≤ c) (hT : 0 ≤ T)
    (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    (hdx : ∀ s ∈ Ioo 0 T, HasDerivAt x (c • ax s) s)
    (hdy : ∀ s ∈ Ioo 0 T, HasDerivAt y (c • ay s) s)
    (hgx : ∀ s ∈ Ioo 0 T, correspondenceOperatorValueResolvent n hn (x s - ax s) = x s)
    (hgy : ∀ s ∈ Ioo 0 T, correspondenceOperatorValueResolvent n hn (y s - ay s) = y s)
    (hinit : x 0 = y 0) : ∀ s ∈ Icc 0 T, x s=y s := by
  apply realHilbert_orbit_unique_of_dissipative_derivative x y
    (fun s => c • ax s) (fun s => c • ay s) T hT hx hy hdx hdy
  · intro s hs
    rw [← smul_sub c (ax s) (ay s), real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos hc
      (correspondenceOperatorGenerator_real_difference_dissipative hn _ _ _ _ (hgx s hs) (hgy s hs))
  · exact hinit

/-- Equality on the true full resolvent range extends to all symmetric L². -/
theorem correspondenceOperator_operators_eq_on_resolvent_range {n : ℕ} (hn : 0 < n)
    (P Q : GinibreFullValueL2 n →L[ℝ] GinibreFullValueL2 n)
    (heq : ∀ u, P (correspondenceOperatorValueResolvent n hn u) =
      Q (correspondenceOperatorValueResolvent n hn u)) : P=Q := by
  apply ContinuousLinearMap.ext
  exact congrFun ((correspondenceOperatorValueResolvent_denseRange n hn).equalizer
    P.continuous Q.continuous (funext heq))

theorem correspondenceOperatorRealEvolution_graph_derivative {n : ℕ} (hn : 0 < n)
    (u v : GinibreFullValueL2 n)
    (hg : correspondenceOperatorValueResolvent n hn (u - v) = u)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => correspondenceOperatorRealEvolution n hn s.toNNReal u)
      (correspondenceOperatorRealEvolution n hn t.toNNReal v) t := by
  have hgraph : (ginibreFullComplexOfReal n u, ginibreFullComplexOfReal n v) ∈
      (correspondenceOperatorGenerator n hn).graph := by
    rw [correspondenceOperatorGenerator_graph_iff,← map_sub,
        correspondenceOperatorComplexResolvent_ofReal, hg]
  have hd := correspondenceOperatorEvolution_hasDerivAt n hn _ _ hgraph ht
  exact (ginibreFullComplexRe n).hasFDerivAt.comp_hasDerivAt t hd

/-- The actual real semigroup preserves the full real weak generator graph. -/
theorem correspondenceOperatorRealEvolution_preserves_graph {n : ℕ} (hn : 0 < n)
    (u v : GinibreFullValueL2 n)
    (hg : correspondenceOperatorValueResolvent n hn (u - v) = u) (t : ℝ≥0) :
    correspondenceOperatorValueResolvent n hn
      (correspondenceOperatorRealEvolution n hn t u-correspondenceOperatorRealEvolution n hn t v)=
      correspondenceOperatorRealEvolution n hn t u := by
  have hgraph : (ginibreFullComplexOfReal n u, ginibreFullComplexOfReal n v) ∈
      (correspondenceOperatorGenerator n hn).graph := by
    rw [correspondenceOperatorGenerator_graph_iff,← map_sub,
        correspondenceOperatorComplexResolvent_ofReal, hg]
  have hh := resolventCfcEvolution_preserves_generator_graph (correspondenceOperatorComplexResolvent
      n hn)
    (correspondenceOperatorComplexResolvent_isSelfAdjoint n hn)
        (correspondenceOperatorComplexResolvent_injective n hn)
    t _ _ hgraph
  exact ((correspondenceOperatorGenerator_graph_iff_real_imag n hn _ _).mp hh).1

end
end GinibrePoincare
