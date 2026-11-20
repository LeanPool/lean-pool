/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDynamicsLocalization.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticProbabilityRestriction
public import Mathlib.MeasureTheory.Measure.Continuity
/-!
# Correspondence dynamics localization

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `correspondence_tendstoInMeasure_of_exhaustion`,
`correspondence_measure_compl_of_ae_exhaustion`.
-/

@[expose] public section
open Set MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Convergence in probability can be checked on events whose complements
have vanishing probability. This supplies the localization-to-global bridge. -/
theorem correspondence_tendstoInMeasure_of_exhaustion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (E : ℕ → Set Ω) (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hE : Tendsto (fun k => P.real (E k)ᶜ) atTop (𝓝 0))
    (hlocal : ∀ k, TendstoInMeasure P (fun j => (E k).indicator (f j))
      atTop ((E k).indicator g)) : TendstoInMeasure P f atTop g := by
  classical
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  · intro b hb
    obtain ⟨k, hk⟩ := (hE.eventually (gt_mem_nhds (half_pos hb))).exists
    have hl := (tendstoInMeasure_iff_measureReal_norm.mp (hlocal k)) ε hε
    filter_upwards [hl.eventually (gt_mem_nhds (half_pos hb))] with j hj
    have hsub : {ω | ε ≤ ‖f j ω-g ω‖} ⊆
        (E k)ᶜ ∪ {ω | ε ≤ ‖(E k).indicator (f j) ω-(E k).indicator g ω‖} := by
      intro ω hω
      by_cases he : ω ∈ E k
      · exact Or.inr (by simpa only [Set.mem_ofPred_eq, indicator_of_mem he] using hω)
      · exact Or.inl he
    have hh := (measureReal_mono (μ := P) hsub).trans (measureReal_union_le (μ := P) _ _)
    linarith

/-- Almost-sure exhaustion of measurable events implies vanishing exceptional
probability, without requiring monotonicity of the events. -/
theorem correspondence_measure_compl_of_ae_exhaustion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (E : ℕ → Set Ω) (hE : ∀ k, MeasurableSet (E k))
    (hex : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∈ E k) :
    Tendsto (fun k => P.real (E k)ᶜ) atTop (𝓝 0) := by
  classical
  let f := fun k => (E k)ᶜ.indicator (fun _ : Ω => (1 : ℝ))
  have hf : ∀ k, AEStronglyMeasurable (f k) P := fun k =>
    (stronglyMeasurable_const.indicator (hE k).compl).aestronglyMeasurable
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun k => f k ω) atTop (𝓝 0) := by
    filter_upwards [hex] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with k hk
    simp [f, hk]
  have hp := tendstoInMeasure_of_tendsto_ae hf hlim
  have hh := tendstoInMeasure_iff_measureReal_norm.mp hp 1 (by norm_num)
  convert hh using 1
  funext k
  congr 1
  ext ω
  by_cases hω : ω ∈ E k <;> simp [f, hω]

end
end GinibrePoincare
