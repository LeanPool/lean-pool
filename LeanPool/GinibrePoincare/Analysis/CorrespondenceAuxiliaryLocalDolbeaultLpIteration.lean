/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultLpIteration.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultBoundaryIteration
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungMultiplierComposition

/-!
# Correspondence auxiliary local Dolbeault lp iteration

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeaultPrimitiveLp_tendsto`.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

theorem dolbeault_compact_continuous_bound (χ : ℂ → ℂ) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) : ∃ C : ℝ, ∀ z, ‖χ z‖ ≤ C := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hχ.continuousOn
  refine ⟨max C 0, fun z => ?_⟩
  by_cases hz : z ∈ tsupport χ
  · exact (hC z hz).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
    exact le_max_right _ _

/-- A chosen uniform bound on `‖χ z‖` for a continuous compactly supported `χ`. -/
def dolbeaultCompactBound (χ : ℂ → ℂ) (hχ : Continuous χ) (hc : HasCompactSupport χ) : ℝ :=
  Classical.choose (dolbeault_compact_continuous_bound χ hχ hc)

theorem dolbeaultCompactBound_spec (χ : ℂ → ℂ) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (z : ℂ) : ‖χ z‖ ≤ dolbeaultCompactBound χ hχ hc :=
  Classical.choose_spec (dolbeault_compact_continuous_bound χ hχ hc) z

/-- Multiplication by the cutoff `p ↦ χ (p j)`, as a bounded operator on ordinary `L²`. -/
def dolbeaultCutoffLpMultiplier {n : ℕ} (j : Fin n) (χ : ℂ → ℂ)
    (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  dolbeaultBoundedMultiplier (fun p => χ (p j))
    ((hχ.comp (continuous_apply j)).aestronglyMeasurable)
    (dolbeaultCompactBound χ hχ hc) (ae_of_all _ (fun p => dolbeaultCompactBound_spec χ hχ hc (p
        j)))

/-- The truncated coordinate-`j` Cauchy–Green operator `dolbeaultCauchyGreenL2 j R` composed with
multiplication by the cutoff `p ↦ χ (p j)`, on ordinary `L²`. -/
def dolbeaultCutoffLpOperator {n : ℕ} (j : Fin n) (R : ℝ) (χ : ℂ → ℂ)
    (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  (dolbeaultCauchyGreenL2 j R).comp (dolbeaultCutoffLpMultiplier j χ hχ hc)

/-- The `L²` boundary operator: `dolbeaultCutoffLpOperator` with the cutoff `planarDbar χ`. -/
def dolbeaultBoundaryLpOperator {n : ℕ} (j : Fin n) (R : ℝ) (χ : ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  dolbeaultCutoffLpOperator j R (planarDbar χ)
    (planarDbar_contDiff_infty χ hχ).continuous (planarDbar_compact χ hc)

/-- The composition of the `L²` boundary operators `dolbeaultBoundaryLpOperator j R (χ j)` along
a list of coordinates. -/
def dolbeaultBoundaryLpComposition {n : ℕ} (R : ℝ) (χ : Fin n → ℂ → ℂ)
    (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (hc : ∀ j, HasCompactSupport (χ j)) :
    List (Fin n) → dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n
  | [] => ContinuousLinearMap.id ℂ _
  | j::l => (dolbeaultBoundaryLpOperator j R (χ j) (hχ j) (hc j)).comp
      (dolbeaultBoundaryLpComposition R χ hχ hc l)

/-- The `L²` Dolbeault primitive along a list of coordinates: for `j :: l`, the primitive for `l`
plus `dolbeaultCutoffLpOperator j R (χ j)` applied to the boundary composition along `l` of
`α j`. -/
def dolbeaultPrimitiveLp {n : ℕ} (R : ℝ) (χ : Fin n → ℂ → ℂ)
    (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (hc : ∀ j, HasCompactSupport (χ j))
    (α : Fin n → dolbeaultOrdinaryL2 n) : List (Fin n) → dolbeaultOrdinaryL2 n
  | [] => 0
  | j::l => dolbeaultPrimitiveLp R χ hχ hc α l +
      dolbeaultCutoffLpOperator j R (χ j) (hχ j).continuous (hc j)
        (dolbeaultBoundaryLpComposition R χ hχ hc l (α j))

/-- Strong ordinary L² convergence survives the actual finite homotopy,
with every cutoff and kernel operator constructed internally. -/
theorem dolbeaultPrimitiveLp_tendsto {n : ℕ} {ι : Type*} {f : Filter ι}
    (R : ℝ) (χ : Fin n → ℂ → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hc : ∀ j, HasCompactSupport (χ j))
    (α : ι → Fin n → dolbeaultOrdinaryL2 n) (a : Fin n → dolbeaultOrdinaryL2 n)
    (ha : ∀ j, Tendsto (fun i => α i j) f (𝓝 (a j))) (l : List (Fin n)) :
    Tendsto (fun i => dolbeaultPrimitiveLp R χ hχ hc (α i) l) f
      (𝓝 (dolbeaultPrimitiveLp R χ hχ hc a l)) := by
  induction l with
  | nil => exact tendsto_const_nhds
  | cons j l ih =>
    exact ih.add (((dolbeaultCutoffLpOperator j R (χ j) (hχ j).continuous (hc j)).continuous.comp
      (dolbeaultBoundaryLpComposition R χ hχ hc l).continuous).continuousAt.tendsto.comp (ha j))

end
end GinibrePoincare
