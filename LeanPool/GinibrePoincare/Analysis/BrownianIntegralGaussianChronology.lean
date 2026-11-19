/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianChronology.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianPrefix
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralContinuousModificationSquare

/-!
# Brownian integral Gaussian chronology

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianUnitGridInnovation_iIndepFun`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Chronological fresh independence implies genuine joint independence.
The proof uses arbitrary finite event intersections, rather than pairwise
independence or a Gaussian independence certificate. -/
theorem chronologicalFresh_iIndepFun {Ω : Type*} [MeasurableSpace Ω]
    {β : ℕ → Type*} [∀ n, MeasurableSpace (β n)]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (Z : ∀ n, Ω → β n)
    (hZ : ∀ n, @Measurable Ω (β n) (ℱ (n + 1)) _ (Z n))
    (hFresh : ∀ n (Y : Ω → ℝ), @Measurable Ω ℝ (ℱ n) _ Y → IndepFun Y (Z n) P) :
    iIndepFun Z P := by
  classical
  have claim : ∀ n (S : Finset ℕ), (∀ j ∈ S, j < n) →
      ∀ sets : ∀ n, Set (β n), (∀ j ∈ S, MeasurableSet (sets j)) →
      P (⋂ j ∈ S, Z j ⁻¹' sets j) = ∏ j ∈ S, P (Z j ⁻¹' sets j) := by
    intro n
    induction n with
    | zero =>
        intro S hb sets hm
        have hS : S = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro j hj
          exact Nat.not_lt_zero j (hb j hj)
        simp [hS]
    | succ n ih =>
        intro S hb sets hm
        by_cases hn : n ∈ S
        · let R := S.erase n
          have hR : ∀ j ∈ R, j < n := by
            intro j hj
            have hjs := Finset.mem_of_mem_erase hj
            have hjn := (Finset.mem_erase.mp hj).1
            have hh := hb j hjs
            omega
          let A : Set Ω := ⋂ j ∈ R, Z j ⁻¹' sets j
          have hA : @MeasurableSet Ω (ℱ n) A := by
            apply Finset.measurableSet_biInter R
            intro j hj
            have hz := (hZ j).mono (ℱ.mono (Nat.succ_le_of_lt (hR j hj))) le_rfl
            exact hz (hm j (Finset.mem_of_mem_erase hj))
          let Y : Ω → ℝ := A.indicator (fun _ => 1)
          have hY : @Measurable Ω ℝ (ℱ n) _ Y := measurable_const.indicator hA
          have hi := hFresh n Y hY
          have hp : Y ⁻¹' ({1} : Set ℝ) = A := by
            ext ω
            by_cases hω : ω ∈ A <;> simp [Y, hω]
          have hprob := hi.measure_inter_preimage_eq_mul ({1} : Set ℝ) (sets n)
            (measurableSet_singleton 1) (hm n hn)
          rw [hp] at hprob
          have hS : S = insert n R := (Finset.insert_erase hn).symm
          have hprior := ih R hR sets (fun j hj => hm j (Finset.mem_of_mem_erase hj))
          rw [hS]
          have hbi : (⋂ j ∈ insert n R, Z j ⁻¹' sets j) = (Z n ⁻¹' sets n) ∩ A := by
            ext ω
            simp [A]
          rw [hbi, Finset.prod_insert (Finset.notMem_erase n S), Set.inter_comm]
          calc
            _ = P A * P (Z n ⁻¹' sets n) := hprob
            _ = (∏ j ∈ R, P (Z j ⁻¹' sets j)) * P (Z n ⁻¹' sets n) := by rw [hprior]
            _ = _ := mul_comm _ _
        · apply ih S _ sets hm
          intro j hj
          have hh := hb j hj
          have hjn : j ≠ n := by intro he; exact hn (he ▸ hj)
          omega
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S sets hm
  apply claim (S.sup id+1) S _ sets hm
  intro j hj
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)

/-- Actual adaptive unit-field innovations on any monotone Brownian time grid
are jointly independent, with no assumed innovation independence. -/
theorem brownianUnitGridInnovation_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℕ → Ω → EuclideanSpace ℝ ι) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hu : ∀ k, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (u k))
    (hunit : ∀ k ω, ‖u k ω‖ = 1) (i : ι) :
    iIndepFun (brownianUnitGridInnovation B u τ) P := by
  classical
  apply chronologicalFresh_iIndepFun P
    (sampledMartingaleFiltration (ginibreBrownianAugmentedFiltration B P hB) τ hτ)
    (brownianUnitGridInnovation B u τ)
    (brownianUnitGridInnovation_measurable_at_end B P hB u τ hτ hu)
  intro k Y hY
  exact (brownianUnitGridInnovation_gaussian_independent B P hB hind u τ hu hunit k Y hY i).2

end
end GinibrePoincare
