/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiTensorMollification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiDbarClosure
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticProductTensorMollification

/-!
# Non quadratic pi tensor mollification

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `rhoSubharmonicPotential_pi_tensor_convolution_gap`.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff InnerProductSpace
namespace GinibrePoincare
noncomputable section

theorem planarPiTranslatedGraph_continuous {m : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (φ : Fin (m + 1) → PlanarComplexCompactTest) :
    Continuous (fun a : Fin (m+1) → ℂ =>
      planarPiPureDbarGraph n V hV (fun i => planarComplexTestTranslate (φ i) (a i))) := by
  have hv (i : Fin (m+1)) : Continuous (fun a : Fin (m+1) → ℂ =>
      planarComplexWeightedValueL2 n V hV (planarComplexTestTranslate (φ i) (a i))) := by
    simp only [planarComplexTestTranslate_weightedValue]
    exact (planarWeightedTranslateL2_continuous n V hV (φ i)
      (φ i).property.1.continuous (φ i).property.2).comp (continuous_apply i)
  have hd (i : Fin (m+1)) : Continuous (fun a : Fin (m+1) → ℂ =>
      planarComplexWeightedDbarL2 n V hV (planarComplexTestTranslate (φ i) (a i))) := by
    simp only [planarComplexTestTranslate_weightedDbar]
    exact (planarWeightedTranslateL2_continuous n V hV _
      (planarComplexCompactTest_dbar_continuous (φ i))
      (planarComplexCompactTest_dbar_compact (φ i))).comp (continuous_apply i)
  have h1 : Continuous (fun a : Fin (m+1) → ℂ =>
      planarPiPureWeightedValue n V hV (fun i => planarComplexTestTranslate (φ i) (a i))) :=
    (continuous_l2PiProductVector (m+1) (fun _ => (volume : Measure ℂ))).comp (continuous_pi hv)
  have h2 (i : Fin (m+1)) : Continuous (fun a : Fin (m+1) → ℂ =>
      planarPiPureWeightedDbar n V hV (fun j => planarComplexTestTranslate (φ j) (a j)) i) := by
    apply (continuous_l2PiProductVector (m+1) (fun _ => (volume : Measure ℂ))).comp
    apply continuous_pi
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using hd i
    · simpa only [Function.update_of_ne hji] using hv j
  exact h1.prodMk (continuous_pi h2)

theorem planarPiTranslatedGraph_integrable {m : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (φ : Fin (m + 1) → PlanarComplexCompactTest)
    (f : (Fin (m + 1) → ℂ) → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun a => f a • planarPiPureDbarGraph n V hV
      (fun i => planarComplexTestTranslate (φ i) (a i))) (Measure.pi (fun _ => (volume : Measure
          ℂ))) :=
  (hf.smul (planarPiTranslatedGraph_continuous n V hV φ)).integrable_of_hasCompactSupport
      hc.smul_right

theorem planarPiTranslatedGraph_integral_mem {m : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (φ : Fin (m + 1) → PlanarComplexCompactTest)
    (f : (Fin (m + 1) → ℂ) → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    (∫ a, f a • planarPiPureDbarGraph n V hV
      (fun i => planarComplexTestTranslate (φ i) (a i))
      ∂Measure.pi (fun _ => (volume : Measure ℂ))) ∈ planarPiDbarClosedGraph (m := m) n V hV := by
  apply bochner_integral_mem_closed_submodule ((planarPiDbarClosedGraph (m := m) n V
      hV).restrictScalars ℝ)
    (planarPiDbarGraphMap (m := m) n V hV).range.isClosed_topologicalClosure
  · exact planarPiTranslatedGraph_integrable n V hV φ f hf hc
  · intro a
    apply (planarPiDbarClosedGraph (m := m) n V hV).smul_mem
    apply (planarPiDbarGraphMap (m := m) n V hV).range.le_topologicalClosure
    refine ⟨Finsupp.single (fun i => planarComplexTestTranslate (φ i) (a i)) 1, ?_⟩
    simp [planarPiDbarGraphMap, Finsupp.linearCombination_single]

theorem rhoSubharmonicPotential_pi_tensor_convolution_gap {m : ℕ}
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (φ : Fin (m + 1) → PlanarComplexCompactTest)
    (f : (Fin (m + 1) → ℂ) → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    let x := ∫ a, f a • planarPiPureDbarGraph n V hV.continuous
      (fun i => planarComplexTestTranslate (φ i) (a i)) ∂Measure.pi (fun _ => (volume : Measure ℂ))
    ‖x.1 - planarPiBergmanProjection n V hV x.1‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) * ((List.finRange (m+1)).map (fun i => ‖x.2 i‖ ^ 2)).sum :=
  rhoSubharmonicPotential_pi_closed_graph_gap n hn V ρ hρpos hV hρ _
    (planarPiTranslatedGraph_integral_mem n V hV.continuous φ f hf hc)
end
end GinibrePoincare
