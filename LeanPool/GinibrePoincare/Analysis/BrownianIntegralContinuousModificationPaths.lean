/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralContinuousModificationPaths.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralContinuousModificationSubsequence

/-!
# Brownian integral continuous modification paths

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `continuousIntervalPathVersion_probability_cauchy`,
`continuousIntervalPathVersion_sequence_eq_ae`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Turn the actual restriction of a continuous sample path into a continuous
map on the compact time interval; use the zero path on exceptional samples. -/
def continuousIntervalPathVersion {Ω : Type*} (F : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (ω : Ω) : C(Set.Icc 0 T, ℝ) := by
  classical
  exact if h : ContinuousOn (fun t => F t ω) (Set.Icc 0 T) then
    ⟨fun t => F t ω, h.domRestrict⟩ else 0

theorem continuousIntervalPathVersion_eq_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => F t ω) (Set.Icc 0 T)) :
    ∀ᵐ ω ∂P, ∀ t : Set.Icc 0 T, continuousIntervalPathVersion F T ω t = F t ω := by
  filter_upwards [hc] with ω hω
  intro t
  simp only [continuousIntervalPathVersion, dite_eq_left hω]
  rfl

/-- Genuine continuous martingales with terminal mean-square Cauchy estimates
have uniformly probability-Cauchy actual continuous path versions. -/
theorem continuousIntervalPathVersion_probability_cauchy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (F : ℕ → ℝ≥0 → Ω → ℝ)
    (hF : ∀ n, Martingale (F n) ℱ P) (T : ℝ≥0)
    (hT : ∀ n, MemLp (F n T) 2 P)
    (hc : ∀ n, ∀ᵐ ω ∂P, ContinuousOn (fun t => F n t ω) (Set.Icc 0 T))
    (hterm : Tendsto (fun q : ℕ × ℕ =>
      ∫ ω, (F q.2 T ω-F q.1 T ω)^2 ∂P) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun q : ℕ × ℕ => P {ω | ∃ t : Set.Icc 0 T,
      ε < |continuousIntervalPathVersion (F q.2) T ω t -
        continuousIntervalPathVersion (F q.1) T ω t|}) atTop (𝓝 0) := by
  intro ε hε
  let e : ℝ≥0 := ⟨ε, hε.le⟩
  have he : 0 < e := hε
  have ht := realMartingale_uniform_probability_cauchy P ℱ
    (fun q : ℕ × ℕ => F q.2) (fun q : ℕ × ℕ => F q.1)
    (fun q => hF q.2) (fun q => hF q.1) T (fun q => hT q.2) (fun q => hT q.1)
    (fun q => hc q.2) (fun q => hc q.1) atTop hterm e he
  convert ht using 1
  ext q
  apply measure_congr
  filter_upwards [continuousIntervalPathVersion_eq_ae P (F q.2) T (hc q.2),
    continuousIntervalPathVersion_eq_ae P (F q.1) T (hc q.1)] with ω h2 h1
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, t.property,?_⟩
    change ε < ‖F q.2 t ω - F q.1 t ω‖
    simpa [h2 t, h1 t, Real.norm_eq_abs, e, NNReal.coe_mk] using ht
  · rintro ⟨t, ht, hh⟩
    refine ⟨⟨t, ht⟩,?_⟩
    change ε < ‖F q.2 t ω - F q.1 t ω‖ at hh
    simpa [h2 ⟨t, ht⟩, h1 ⟨t, ht⟩, Real.norm_eq_abs, e, NNReal.coe_mk] using hh

/-- The path adapters match the original processes simultaneously at every
index and every time, outside one null set. -/
theorem continuousIntervalPathVersion_sequence_eq_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hc : ∀ n, ∀ᵐ ω ∂P, ContinuousOn (fun t => F n t ω) (Set.Icc 0 T)) :
    ∀ᵐ ω ∂P, ∀ n, ∀ t : Set.Icc 0 T,
      continuousIntervalPathVersion (F n) T ω t = F n t ω := by
  exact ae_all_iff.mpr (fun n => continuousIntervalPathVersion_eq_ae P (F n) T (hc n))

end
end GinibrePoincare
