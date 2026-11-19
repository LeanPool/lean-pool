/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticContinuousFieldIntegral.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticUnitFieldIntegral

/-! Actual continuous martingale integration of a bounded adapted coefficient
family, constructed from the original independent Brownian motions. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBoundedField_continuous_integral_exists
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (A : ι → ℝ≥0 → Ω → ℝ)
    (hA : ∀ i t, @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _ (A i t))
    (T : ℝ≥0) (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun t => A i t ω) (Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ i t ω, ‖A i t ω‖ ≤ C) :
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧
      J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t ≤ T, TendstoInMeasure P (fun k ω =>
        ∑ i, brownianUniformLeftSum (B i) (A i) t (k+1) ω) atTop (J t)) := by
  classical
  classical
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  have hex (i : ι) := brownianContinuousIntegral_exists_all_horizons B P hB hind i (A i)
    (hA i) T (hc i) C hC (hb i)
  choose M hM hMC hML hM0 hMP hMS using hex
  let J : ℝ≥0 → Ω → ℝ := ∑ i, M i
  have hJe (t : ℝ≥0) (ω : Ω) : J t ω=∑ i, M i t ω := by
    simp only [J, Finset.sum_apply]
  have hsum (S : Finset ι) : Martingale (∑ i ∈ S, M i) F P := by
    induction S using Finset.induction_on with
    | empty => simpa using martingale_zero ℝ F P
    | @insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact (hM i).add ih
  have hJ : Martingale J F P := hsum Finset.univ
  have hJC (ω : Ω) : Continuous (fun t => J t ω) := by
    simp_rw [hJe]
    exact continuous_finsetSum Finset.univ (fun i hi => hMC i ω)
  have hJL (t : ℝ≥0) : MemLp (J t) 2 P := by
    rw [show J t=(fun ω => ∑ i, M i t ω) from funext (hJe t)]
    exact memLp_finsetSum Finset.univ (fun i hi => hML i t)
  have hz : J 0 =ᵐ[P] (fun _ => 0) := by
    filter_upwards [ae_all_iff.mpr hM0] with ω hω
    simp [J, hω]
  refine ⟨J, hJ, hJC, hJL, hz,?_⟩
  intro t ht
  have hFi (i : ι) (s : ℝ≥0) : MemLp (A i s) 2 P := MemLp.of_bound
    ((hA i s).mono (F.le s) le_rfl).aestronglyMeasurable
    C (Eventually.of_forall (hb i s))
  have hh := itoTendstoInMeasure_finset_sum P Finset.univ
    (fun i k => brownianUniformLeftSum (B i) (A i) t (k+1)) (fun i => M i t)
    (fun i k => (brownianUniformLeftSum_memLp_two B P (fun i => (hB i).toIsPreBrownianReal)
      hind i (A i) (hA i) (hFi i) t (k+1)).aestronglyMeasurable)
    (fun i => hMS i t ht)
  convert! hh using 1
  funext ω
  exact hJe t ω
end
end GinibrePoincare
