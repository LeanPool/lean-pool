/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiDbarClosure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiDbar
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Non quadratic pi dbar closure

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `rhoSubharmonicPotential_pi_closed_graph_gap`.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff InnerProductSpace
namespace GinibrePoincare
noncomputable section

/-- The graph space of the `∂̄` operator on `L²(ℂ^d)`: a value together with one `L²` component
for each coordinate derivative. -/
abbrev PlanarPiDbarGraphSpace (d : ℕ) := PlanarPiLebesgueL2 d × (Fin d → PlanarPiLebesgueL2 d)

/-- The weighted `∂̄`-graph of a pure tensor of tests: its weighted value and all its weighted
coordinate `∂̄` derivatives. -/
def planarPiPureDbarGraph {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (f : Fin (m + 1) → PlanarComplexCompactTest) : PlanarPiDbarGraphSpace (m+1) :=
  (planarPiPureWeightedValue n V hV f, planarPiPureWeightedDbar n V hV f)

/-- The linear extension of `planarPiPureDbarGraph` to finitely supported linear combinations
of families of tests. -/
def planarPiDbarGraphMap {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    ((Fin (m+1) → PlanarComplexCompactTest) →₀ ℂ) →ₗ[ℂ] PlanarPiDbarGraphSpace (m+1) :=
  Finsupp.linearCombination ℂ (planarPiPureDbarGraph n V hV)

/-- The closed weighted `∂̄`-graph: the topological closure of the range of
`planarPiDbarGraphMap`. -/
def planarPiDbarClosedGraph {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    Submodule ℂ (PlanarPiDbarGraphSpace (m+1)) :=
  (planarPiDbarGraphMap (m := m) n V hV).range.topologicalClosure

theorem planarPiClosedGraph_inverse_action {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (T : PlanarLebesgueL2 →L[ℂ] PlanarLebesgueL2)
    (hT : ∀ f : PlanarComplexCompactTest,
      T (planarComplexWeightedDbarL2 n V hV.continuous f) =
        planarComplexWeightedValueL2 n V hV.continuous f -
          planarBergmanProjection n V hV (planarComplexWeightedValueL2 n V hV.continuous f))
    (x : PlanarPiDbarGraphSpace (m+1)) (hx : x ∈ planarPiDbarClosedGraph n V hV.continuous)
    (i : Fin (m+1)) :
    l2PiCoordinateOperator (fun _ => (volume : Measure ℂ)) i T (x.2 i) =
      x.1 - planarPiBergmanCoordinate n V hV i x.1 := by
  let E : PlanarPiDbarGraphSpace (m+1) →L[ℂ] PlanarPiLebesgueL2 (m+1) :=
    (l2PiCoordinateOperator (fun _ : Fin (m+1) => (volume : Measure ℂ)) i T).comp
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ _ _)) -
      (ContinuousLinearMap.id ℂ _ - planarPiBergmanCoordinate n V hV i).comp
        (ContinuousLinearMap.fst ℂ _ _)
  have hp (f : Fin (m+1) → PlanarComplexCompactTest) : E (planarPiPureDbarGraph n V hV.continuous f)
      = 0 := by
    simp only [E, planarPiPureDbarGraph, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, 
      ContinuousLinearMap.id_apply]
    exact sub_eq_zero.mpr (planarPiPure_inverse_action n V hV T hT f i)
  have hr : ((planarPiDbarGraphMap (m := m) n V hV.continuous).range : Set _) ⊆ {x | E x = 0} := by
    rintro _ ⟨f, rfl⟩
    change E (Finsupp.linearCombination ℂ (planarPiPureDbarGraph n V hV.continuous) f) = 0
    change E.toLinearMap (Finsupp.linearCombination ℂ (planarPiPureDbarGraph n V hV.continuous) f) =
        0
    rw [Finsupp.apply_linearCombination ℂ E.toLinearMap]
    simp only [Function.comp_def]
    simp [Finsupp.linearCombination_apply, hp]
  have he : E x = 0 :=
    (isClosed_eq E.continuous continuous_const).closure_subset_iff.mpr hr hx
  simp only [E, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, 
    ContinuousLinearMap.id_apply] at he
  exact sub_eq_zero.mp he

/-- The actual n-coordinate graph completion preserves the sharp scalar
constant. Every derivative component is retained in the closure. -/
theorem rhoSubharmonicPotential_pi_closed_graph_gap {m : ℕ}
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (x : PlanarPiDbarGraphSpace (m + 1)) (hx : x ∈ planarPiDbarClosedGraph n V hV.continuous) :
    ‖x.1 - planarPiBergmanProjection n V hV x.1‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) * ((List.finRange (m+1)).map (fun i => ‖x.2 i‖ ^ 2)).sum := by
  obtain ⟨T, hnorm, hT⟩ := rhoSubharmonicPotential_exists_bounded_dbar_inverse n hn V ρ hρpos hV hρ
  let C := 2 / ((n : ℝ) * ρ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs := Real.sq_sqrt hC
  have hb (i : Fin (m+1)) : ‖x.1 - planarPiBergmanCoordinate n V hV i x.1‖ ^ 2 ≤ C * ‖x.2 i‖ ^ 2 :=
      by
    let S := l2PiCoordinateOperator (fun _ : Fin (m+1) => (volume : Measure ℂ)) i T
    have hb : ‖S‖ ≤ Real.sqrt C :=
      (l2PiCoordinateOperator_norm_le (fun _ : Fin (m+1) => (volume : Measure ℂ)) i T).trans hnorm
    have hh := (S.le_opNorm (x.2 i)).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    have hsq := (sq_le_sq₀ (norm_nonneg (S (x.2 i)))
      (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _))).mpr hh
    have he := planarPiClosedGraph_inverse_action n V hV T hT x hx i
    change S (x.2 i) = _ at he
    rw [he] at hsq
    simpa only [mul_pow, hs] using hsq
  have sum_bound (is : List (Fin (m+1))) :
      (is.map (fun i => ‖x.1 - planarPiBergmanCoordinate n V hV i x.1‖ ^ 2)).sum ≤
      C * (is.map (fun i => ‖x.2 i‖ ^ 2)).sum := by
    induction is with
    | nil => simp
    | cons i is ih => simpa only [List.map_cons, List.sum_cons, mul_add] using add_le_add (hb i) ih
  exact (planarPiBergmanProjection_error n V hV x.1).trans (sum_bound _)
end
end GinibrePoincare
