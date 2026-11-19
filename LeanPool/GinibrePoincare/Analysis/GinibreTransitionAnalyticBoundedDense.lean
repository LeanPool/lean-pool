/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticBoundedDense.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorDensity
public import LeanPool.GinibrePoincare.Analysis.GinibreValueTruncationL2
public import LeanPool.GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-! Genuine bounded symmetric values are dense in the entire actual real
symmetric Ginibre L² space. -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- The truncation `z ↦ sobolevValueTruncation m (u z)` of a permutation-invariant `L²` value,
which is again permutation invariant. -/
def ginibreFullSymmetricBoundedTruncation (n m : ℕ) (u : ginibreFullSymmetricValues n) :
    ginibreFullSymmetricValues n := by
  let h := ginibreValueTruncation_memLp n m u.val (Lp.memLp u.val)
  let v := h.toLp (fun z => sobolevValueTruncation m (u.val z))
  refine ⟨v,?_⟩
  intro σ
  apply Lp.ext
  have hv := h.coeFn_toLp
  have hvc := (ginibre_measurePreserving_permute
      σ).quasiMeasurePreserving.ae_eq_comp hv
  have hup := ginibreRealPermutationL2_ae σ u.val
  rw [u.property σ] at hup
  filter_upwards [ginibreRealPermutationL2_ae σ v, hvc, hv, hup] with z hp hc hz hu
  dsimp only [Function.comp_apply] at hc
  rw [hp, hc, hz,← hu]

theorem ginibreFullSymmetricBoundedTruncation_ae (n m : ℕ) (u : ginibreFullSymmetricValues n) :
    ((ginibreFullSymmetricBoundedTruncation n m u).val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      (fun z => sobolevValueTruncation m (u.val z)) :=
  (ginibreValueTruncation_memLp n m u.val (Lp.memLp u.val)).coeFn_toLp

theorem ginibreFullSymmetricBoundedTruncation_bound (n m : ℕ) (u : ginibreFullSymmetricValues n) :
    ∀ᵐ z ∂ginibreMeasure n, ‖(ginibreFullSymmetricBoundedTruncation n m u).val z‖ ≤ 2*((m : ℝ)+1) :=
  (ginibreFullSymmetricBoundedTruncation_ae n m u).mono fun z hz => by
    rw [hz]
    exact sobolevValueTruncation_bounded m (u.val z)

theorem ginibreFullSymmetricBoundedTruncation_tendsto (n : ℕ) (u : ginibreFullSymmetricValues n) :
    Tendsto (fun m => ginibreFullSymmetricBoundedTruncation n m u) atTop (𝓝 u) := by
  apply tendsto_subtype_rng.mpr
  exact ginibreValueTruncation_L2_tendsto n u.val

/-- The function `f` with every value of norm larger than `A` replaced by `0`. -/
def actualBoundedRealVersion {Ω : Type*} (f : Ω → ℝ) (A : ℝ) : Ω → ℝ :=
  fun x => if ‖f x‖ ≤ A then f x else 0

theorem actualBoundedRealVersion_bound {Ω : Type*} (f : Ω → ℝ) (A : ℝ) (hA : 0 ≤ A) :
    ∀ x, ‖actualBoundedRealVersion f A x‖ ≤ A := by
  intro x
  unfold actualBoundedRealVersion
  split_ifs with h
  · exact h
  · simpa using hA

theorem actualBoundedRealVersion_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (A : ℝ) (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ A) :
    actualBoundedRealVersion f A =ᵐ[μ] f :=
  hb.mono fun _ hx => ite_eq_left hx

theorem actualBoundedRealVersion_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) (A : ℝ)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ A) : MemLp (actualBoundedRealVersion f A) 2 μ :=
  hf.ae_eq (actualBoundedRealVersion_ae μ f A hb).symm

/-- Equality on genuinely bounded values extends to the full symmetric L² source,
with no assumption that either target operator preserves symmetry. -/
theorem ginibreSymmetricSource_operators_eq_of_bounded_values (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R S : ginibreFullSymmetricValues n →L[ℝ] E)
    (heq : ∀ u : ginibreFullSymmetricValues n,
      (∃ A : ℝ, ∀ᵐ z ∂ginibreMeasure n, ‖u.val z‖≤A) → R u=S u) : R=S := by
  apply ContinuousLinearMap.ext
  intro u
  have ht := ginibreFullSymmetricBoundedTruncation_tendsto n u
  have hh (m : ℕ) : R (ginibreFullSymmetricBoundedTruncation n m u)=
      S (ginibreFullSymmetricBoundedTruncation n m u) :=
    heq _ ⟨2*((m : ℝ)+1), ginibreFullSymmetricBoundedTruncation_bound n m u⟩
  exact tendsto_nhds_unique (R.continuous.tendsto u |>.comp ht)
    ((S.continuous.tendsto u |>.comp ht).congr fun m => (hh m).symm)

theorem ginibreFullSymmetric_operators_eq_of_bounded_values (n : ℕ)
    (R S : ginibreFullSymmetricValues n →L[ℝ] ginibreFullSymmetricValues n)
    (heq : ∀ u : ginibreFullSymmetricValues n,
      (∃ A : ℝ, ∀ᵐ z ∂ginibreMeasure n, ‖u.val z‖ ≤ A) → R u=S u) : R=S :=
  ginibreSymmetricSource_operators_eq_of_bounded_values n R S heq

end
end GinibrePoincare
