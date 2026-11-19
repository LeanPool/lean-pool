/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianIndependenceLimit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianLawLimit

/-!
# Brownian integral Gaussian independence limit

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `actualConstantLaw_independent_of_limit`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- Constant-law actual probability limits preserve independence of an
arbitrary actual measurable past variable. The past codomain need not be
metrizable or countable: indicator tests reduce it to real-valued laws. -/
theorem actualConstantLaw_independent_of_limit
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (S : ℕ → Ω → ℝ) (hS : ∀ n, HasLaw (S n) μ P)
    (L : Ω → ℝ) (hL : TendstoInMeasure P S atTop L)
    (Y : Ω → A) (hY : Measurable Y) (hInd : ∀ n, IndepFun Y (S n) P) :
    IndepFun Y L P := by
  classical
  have hlaw := actualConstantLaw_of_tendstoInMeasure P μ S hS L hL
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro Aset C hA hC
  let φ : A → ℝ := Aset.indicator (fun _ => 1)
  let V : Ω → ℝ := fun ω => φ (Y ω)
  have hφ : Measurable φ := measurable_const.indicator hA
  have hV : Measurable V := hφ.comp hY
  let ν := P.map V
  let : IsProbabilityMeasure ν := (by infer_instance)
  have hVlaw : HasLaw V ν P := ⟨hV.aemeasurable, rfl⟩
  have hi : ∀ n, IndepFun V (S n) P := by
    intro n
    exact (hInd n).comp hφ measurable_id
  have hp : TendstoInMeasure P (fun n ω => (V ω, S n ω)) atTop (fun ω => (V ω, L ω)) := by
    intro ε hε
    simpa only [Prod.edist_eq, edist_self, zero_max] using hL ε hε
  have hj := actualConstantLaw_of_tendstoInMeasure P (ν.prod μ)
    (fun n ω => (V ω, S n ω)) (fun n => IndepFun.hasLaw_prod hVlaw (hS n) (hi n))
    (fun ω => (V ω, L ω)) hp
  have hiL : IndepFun V L P := by
    apply (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hlaw.aemeasurable).mpr
    rw [hj.map_eq, hlaw.map_eq]
  have he : V ⁻¹' ({1} : Set ℝ) = Y ⁻¹' Aset := by
    ext ω
    by_cases hω : Y ω ∈ Aset <;> simp [V, φ, hω]
  have hh := hiL.measure_inter_preimage_eq_mul ({1} : Set ℝ) C (measurableSet_singleton 1) hC
  rwa [he] at hh

end
end GinibrePoincare
