/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDynamicsConstantLawLimit.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDynamicsNoiseShift
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
/-!
# Correspondence dynamics constant law limit

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `correspondence_constantLaw_ae_limit`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Constant finite laws pass to almost surely convergent measurable random elements. -/
theorem correspondence_constantLaw_ae_limit {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [HasOuterApproxClosed E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsFiniteMeasure P] (X : ℕ → Ω → E) (x : Ω → E)
    (hX : ∀ m, Measurable (X m)) (hx : Measurable x)
    (hl : ∀ᵐ ω ∂P, Tendsto (fun m => X m ω) atTop (𝓝 (x ω)))
    (ν : Measure E) [IsFiniteMeasure ν] (he : ∀ m, P.map (X m) = ν) :
    P.map x = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro b
  rw [integral_map hx.aemeasurable b.continuous.aestronglyMeasurable]
  have ht : Tendsto (fun m => ∫ ω, b (X m ω) ∂P) atTop (𝓝 (∫ ω, b (x ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖b‖)
    · intro m
      exact (b.continuous.measurable.comp (hX m)).aestronglyMeasurable
    · exact integrable_const _
    · intro m
      exact Eventually.of_forall (fun ω => b.norm_coe_le_norm _)
    · filter_upwards [hl] with ω hω
      exact b.continuous.continuousAt.tendsto.comp hω
  have he' (m : ℕ) : (∫ ω, b (X m ω) ∂P) = ∫ y, b y ∂ν := by
    rw [← he m, integral_map (hX m).aemeasurable b.continuous.aestronglyMeasurable]
  exact (tendsto_nhds_unique ht (by simpa only [he'] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ y, b y ∂ν) atTop (𝓝 (∫ y, b y ∂ν)))))

end
end GinibrePoincare
