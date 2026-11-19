/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianKilledExhaustionIntegration.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianKilledOUPathMeasure

/-!
# Ginibre Hamiltonian killed exhaustion integration

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `and`, `ginibreHamiltonian_full_reverse_of_actual_killed_reversals`.
-/

@[expose] public section

open Set MeasureTheory
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance ginibreKilledExhaustionMeasurable (n : ℕ) (T : ℝ) :
    MeasurableSpace C(Icc (0 : ℝ) T, Configuration n) := borel _
local instance ginibreKilledExhaustionBorel (n : ℕ) (T : ℝ) :
    BorelSpace C(Icc (0 : ℝ) T, Configuration n) := ⟨rfl⟩

/-- Measure-theoretic passage from actual killed-law reversals to full path
reversal. The stochastic killed identities are hypotheses of this integration
lemma and must be supplied by the actual Girsanov identification. -/
theorem ginibreHamiltonian_full_reverse_of_actual_killed_reversals
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (μ : Measure C(Icc (0 : ℝ) T, Configuration n))
    (hCF : ∀ᵐ x ∂μ, ∀ t, CollisionFree (x t))
    (hKilled : ∀ k : ℕ,
      ((μ.restrict (ginibreHamiltonianCompactSurvival n T (k : ℝ))).map
        (fun x => x.comp (ginibreHamiltonianCompactReverseTime T hT))) =
      μ.restrict (ginibreHamiltonianCompactSurvival n T (k : ℝ))) :
    μ.map (fun x => x.comp (ginibreHamiltonianCompactReverseTime T hT)) = μ := by
  let r : C(Icc (0 : ℝ) T, Configuration n) → C(Icc (0 : ℝ) T, Configuration n) :=
    fun x => x.comp (ginibreHamiltonianCompactReverseTime T hT)
  have hr : Measurable r := (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime
      T hT)).measurable
  have hi : Function.Involutive r := by
    intro x
    ext t j
    change x ((ginibreHamiltonianCompactReverseTime T hT)
      ((ginibreHamiltonianCompactReverseTime T hT) t)) j = x t j
    have he : (ginibreHamiltonianCompactReverseTime T hT)
        ((ginibreHamiltonianCompactReverseTime T hT) t) = t := by
      apply Subtype.ext
      change T-(T-t.val)=t.val
      ring
    rw [he]
  let e := MeasurableEquiv.ofInvolutive r hi hr
  let S : ℕ → Set C(Icc (0 : ℝ) T, Configuration n) :=
    fun k => ginibreHamiltonianCompactSurvival n T (k : ℝ)
  have hpre (k : ℕ) : e ⁻¹' S k = S k := by
    ext x
    exact ginibreHamiltonian_compact_sublevel_survival_reverse T hT k x
  have hCov : ∀ᵐ x ∂μ, x ∈ ⋃ k, S k := by
    filter_upwards [hCF] with x hx
    obtain ⟨k, hk⟩ := ginibreHamiltonian_compact_path_natural_sublevel_exhaustion T x hx
    exact mem_iUnion.mpr ⟨k, hk⟩
  have hCovMap : ∀ᵐ x ∂μ.map e, x ∈ ⋃ k, S k := by
    apply e.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hCov] with x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨k, by change x ∈ e ⁻¹' S k; rw [hpre]; exact hk⟩
  have hEq : (μ.map e).restrict (⋃ k, S k) = μ.restrict (⋃ k, S k) := by
    apply Measure.restrict_iUnion_congr.mpr
    intro k
    rw [e.restrict_map, hpre]
    exact hKilled k
  rw [Measure.restrict_eq_self_of_ae_mem hCovMap, Measure.restrict_eq_self_of_ae_mem hCov] at hEq
  exact hEq

end
end GinibrePoincare
