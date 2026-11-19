/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDynamicsStoppingFinite.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianBrownianRestart
public import LeanPool.GinibrePoincare.Analysis.BrownianOrthogonalContinuousPathLaw
/-!
# Correspondence dynamics stopping finite

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrownian_finite_stopping_fresh_noise`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- Fresh continuous Brownian noise after a genuine finite-valued stopping
time has the original noise law conditionally on the stopped past. This is the
first step of the stopping-time, rather than deterministic-time, Markov bridge. -/
theorem correspondenceBrownian_finite_stopping_fresh_noise
    {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (α : ℝ) (τ : Ω → ℝ≥0) (S : Finset ℝ≥0) (hrange : ∀ ω, τ ω ∈ S)
    (hτ : IsStoppingTime (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A)
    (C : Set (GinibreContinuousNoise n)) (hC : MeasurableSet C) :
    P ({ω | ginibreBrownianFullContinuousNoise n (brownianFamilyShift B (τ ω)) α ω ∈ C} ∩ A) =
      (P.map (ginibreBrownianFullContinuousNoise n B α)) C * P A := by
  classical
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  let N := fun s => ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α
  let E := fun s : ℝ≥0 => A ∩ {ω | τ ω=s}
  have hE (s : ℝ≥0) : MeasurableSet[F s] (E s) := by
    have hh := (hτ.measurableSet A).mp hA
    have h1 := hh.2 s
    have h2 := hτ.measurableSet_eq s
    have he : E s = (A ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ s}) ∩
        {ω | (τ ω : WithTop ℝ≥0) = s} := by
      ext ω
      simp only [E, mem_inter_iff, Set.mem_ofPred_eq, WithTop.coe_eq_coe, WithTop.coe_le_coe]
      constructor
      · rintro ⟨hA, hτ⟩
        exact ⟨⟨hA, hτ.le⟩, hτ⟩
      · rintro ⟨⟨hA, _⟩, hτ⟩
        exact ⟨hA, hτ⟩
    rw [he]
    exact h1.inter h2
  have hEambient (s : ℝ≥0) : MeasurableSet (E s) := F.le s _ (hE s)
  have hN (s : ℝ≥0) : Measurable (N s) :=
    ginibreBrownianFullContinuousNoise_measurable n _ P
      (brownianFamilyShift_isBrownian_independent B P hB hind s).1 α
  have hpiece (s : ℝ≥0) : P ((N s) ⁻¹' C ∩ E s) =
      (P.map (ginibreBrownianFullContinuousNoise n B α)) C * P (E s) := by
    let Y := (E s).indicator (fun _ : Ω => (1 : ℝ))
    have hY : @Measurable Ω ℝ (F s) _ Y := (measurable_const.indicator (hE s))
    have hi := brownianFamily_future_continuous_noise_independent_augmented_variable
      n B P hB hind α s Y hY
    have he : Y ⁻¹' ({1} : Set ℝ) = E s := by
      ext ω
      by_cases hω : ω ∈ E s <;> simp [Y, hω]
    have hh := hi.measure_inter_preimage_eq_mul C {1} hC (measurableSet_singleton 1)
    rw [he] at hh
    have hl := brownianFamily_shift_continuous_noise_law_eq n B P hB hind α s
    rw [← hl, Measure.map_apply (hN s) hC]
    exact hh
  have hdisj : Pairwise (fun s t => Disjoint (E s) (E t)) := by
    intro s t hst
    apply Set.disjoint_left.mpr
    intro ω hs ht
    exact hst (hs.2.symm.trans ht.2)
  have hu : A = ⋃ s ∈ S, E s := by
    ext ω
    constructor
    · intro hω
      exact mem_iUnion.mpr ⟨τ ω, mem_iUnion.mpr ⟨hrange ω, ⟨hω, rfl⟩⟩⟩
    · intro hω
      obtain ⟨s, hω⟩ := mem_iUnion.mp hω
      obtain ⟨_, hω⟩ := mem_iUnion.mp hω
      exact hω.1
  have hu2 : {ω | ginibreBrownianFullContinuousNoise n (brownianFamilyShift B (τ ω)) α ω ∈ C} ∩ A =
      ⋃ s ∈ S, (N s) ⁻¹' C ∩ E s := by
    ext ω
    constructor
    · intro hω
      refine mem_iUnion.mpr ⟨τ ω, mem_iUnion.mpr ⟨hrange ω,?_⟩⟩
      exact ⟨hω.1, hω.2, rfl⟩
    · intro hω
      obtain ⟨s, hω⟩ := mem_iUnion.mp hω
      obtain ⟨_, hω⟩ := mem_iUnion.mp hω
      refine ⟨?_, hω.2.1⟩
      change ginibreBrownianFullContinuousNoise n (brownianFamilyShift B (τ ω)) α ω ∈ C
      rw [hω.2.2]
      exact hω.1
  rw [hu2, measure_biUnion_finset]
  · simp_rw [hpiece]
    rw [← Finset.mul_sum, hu, measure_biUnion_finset]
    · exact fun s hs t ht hst => hdisj hst
    · exact fun s hs => hEambient s
  · intro s hs t ht hst
    exact (hdisj hst).mono inter_subset_right inter_subset_right
  · exact fun s hs => (hC.preimage (hN s)).inter (hEambient s)

end
end GinibrePoincare
