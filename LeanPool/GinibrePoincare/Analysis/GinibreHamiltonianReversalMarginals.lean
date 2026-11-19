/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianReversalMarginals.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianKilledExhaustionIntegration

/-!
# Ginibre Hamiltonian reversal marginals

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreHamiltonian_reversal_endpoint_marginal`,
`ginibreHamiltonian_reversal_joint_endpoint`.
-/

@[expose] public section

open Set MeasureTheory
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance ginibreReversalMarginalsMeasurable (n : ℕ) (T : ℝ) :
    MeasurableSpace C(Icc (0 : ℝ) T, Configuration n) := borel _
local instance ginibreReversalMarginalsBorel (n : ℕ) (T : ℝ) :
    BorelSpace C(Icc (0 : ℝ) T, Configuration n) := ⟨rfl⟩

/-- Actual reversal of a compact path law gives its stationary endpoint law. -/
theorem ginibreHamiltonian_reversal_endpoint_marginal (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (μ : Measure C(Icc (0 : ℝ) T, Configuration n))
    (hrev : μ.map (fun x => x.comp (ginibreHamiltonianCompactReverseTime T hT)) = μ) :
    μ.map (fun x => x ⟨T, hT, le_rfl⟩)=μ.map (fun x => x ⟨0, le_rfl, hT⟩) := by
  have he : Measurable (fun x : C(Icc (0 : ℝ) T, Configuration n) => x ⟨0, le_rfl, hT⟩) :=
    (continuous_eval_const _).measurable
  have hr : Measurable (fun x : C(Icc (0 : ℝ) T, Configuration n) =>
      x.comp (ginibreHamiltonianCompactReverseTime T hT)) :=
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime T hT)).measurable
  have hh := congrArg (fun ν : Measure C(Icc (0 : ℝ) T, Configuration n) =>
    ν.map (fun x => x ⟨0, le_rfl, hT⟩)) hrev
  rw [Measure.map_map he hr] at hh
  have hf : ((fun x : C(Icc (0 : ℝ) T, Configuration n) => x ⟨0, le_rfl, hT⟩) ∘
      (fun x : C(Icc (0 : ℝ) T, Configuration n) => x.comp (ginibreHamiltonianCompactReverseTime T
          hT))) =
      (fun x : C(Icc (0 : ℝ) T, Configuration n) => x ⟨T, hT, le_rfl⟩) := by
    funext x
    change x ((ginibreHamiltonianCompactReverseTime T hT) ⟨0, le_rfl, hT⟩)=x ⟨T, hT, le_rfl⟩
    have ht : (ginibreHamiltonianCompactReverseTime T hT) ⟨0, le_rfl, hT⟩=⟨T, hT, le_rfl⟩ := by
      apply Subtype.ext
      change T-0=T
      ring
    rw [ht]
  rw [hf] at hh
  exact hh

/-- Reversal also gives the literal symmetry of the joint endpoint measure. -/
theorem ginibreHamiltonian_reversal_joint_endpoint (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (μ : Measure C(Icc (0 : ℝ) T, Configuration n))
    (hrev : μ.map (fun x => x.comp (ginibreHamiltonianCompactReverseTime T hT)) = μ) :
    μ.map (fun x => (x ⟨0, le_rfl, hT⟩, x ⟨T, hT, le_rfl⟩))=
    μ.map (fun x : C(Icc (0 : ℝ) T, Configuration n) => (x ⟨T, hT, le_rfl⟩, x ⟨0, le_rfl, hT⟩)) :=
        by
  have he : Measurable (fun x : C(Icc (0 : ℝ) T, Configuration n) =>
      (x ⟨0, le_rfl, hT⟩, x ⟨T, hT, le_rfl⟩)) :=
    (continuous_eval_const _).measurable.prodMk (continuous_eval_const _).measurable
  have hr : Measurable (fun x : C(Icc (0 : ℝ) T, Configuration n) =>
      x.comp (ginibreHamiltonianCompactReverseTime T hT)) :=
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime T hT)).measurable
  have hh := congrArg (fun ν : Measure C(Icc (0 : ℝ) T, Configuration n) =>
    ν.map (fun x => (x ⟨0, le_rfl, hT⟩, x ⟨T, hT, le_rfl⟩))) hrev
  rw [Measure.map_map he hr] at hh
  have hf : ((fun x : C(Icc (0 : ℝ) T, Configuration n) =>
      (x ⟨0, le_rfl, hT⟩, x ⟨T, hT, le_rfl⟩)) ∘
      (fun x : C(Icc (0 : ℝ) T, Configuration n) => x.comp (ginibreHamiltonianCompactReverseTime T
          hT))) =
      (fun x : C(Icc (0 : ℝ) T, Configuration n) => (x ⟨T, hT, le_rfl⟩, x ⟨0, le_rfl, hT⟩)) := by
    funext x
    have ht : (ginibreHamiltonianCompactReverseTime T hT) ⟨0, le_rfl, hT⟩=⟨T, hT, le_rfl⟩ := by
      apply Subtype.ext
      change T-0=T
      ring
    have hz : (ginibreHamiltonianCompactReverseTime T hT) ⟨T, hT, le_rfl⟩=⟨0, le_rfl, hT⟩ := by
      apply Subtype.ext
      change T-T=0
      ring
    change (x ((ginibreHamiltonianCompactReverseTime T hT) ⟨0, le_rfl, hT⟩),
      x ((ginibreHamiltonianCompactReverseTime T hT) ⟨T, hT, le_rfl⟩)) = _
    rw [ht, hz]
  rw [hf] at hh
  exact hh.symm

end
end GinibrePoincare
