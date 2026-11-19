/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDynamicsBrownianStrongMarkov.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDynamicsConstantLawLimit
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDynamicsStoppingCountable
public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitApproximation
public import Mathlib.Topology.Metrizable.ContinuousMap
/-!
# Correspondence dynamics Brownian strong Markov

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrownian_stopping_fresh_noise`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

theorem correspondenceNoiseShift_countable_actual {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (α : ℝ) (τ : Ω → ℝ≥0) (hc : (range τ).Countable) :
    (fun ω => correspondenceNoiseShift n (τ ω) (ginibreBrownianFullContinuousNoise n B α ω)) =ᵐ[P]
      (fun ω => ginibreBrownianFullContinuousNoise n (brownianFamilyShift B (τ ω)) α ω) := by
  let := hc.toEncodable
  have hh : ∀ᵐ ω ∂P, ∀ s : range τ,
      correspondenceNoiseShift n s (ginibreBrownianFullContinuousNoise n B α ω) =
        ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α ω :=
    ae_all_iff.mpr (fun s => correspondenceNoiseShift_actual n B P hB hind α s)
  filter_upwards [hh] with ω hω
  exact hω ⟨τ ω, mem_range_self ω⟩

/-- Genuine Brownian strong Markov noise law at every finite stopping time,
conditionally on every event in the stopped sigma algebra. -/
theorem correspondenceBrownian_stopping_fresh_noise {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (α : ℝ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict A).map (fun ω => correspondenceNoiseShift n (τ ω)
      (ginibreBrownianFullContinuousNoise n B α ω)) =
      (P A) • P.map (ginibreBrownianFullContinuousNoise n B α) := by
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  let N := ginibreBrownianFullContinuousNoise n B α
  let q : ℕ → Ω → ℝ≥0 := fun m ω => stoppingUpperGrid m (τ ω)
  have hq (m : ℕ) : IsStoppingTime F (fun ω => (q m ω : WithTop ℝ≥0)) :=
    stoppingUpperGrid_isStoppingTime hτ m
  have htm : Measurable τ := by
    convert hτ.measurable'.untopD 0 using 1
    rfl
  have hqm (m : ℕ) : Measurable (q m) := by
    convert (hq m).measurable'.untopD 0 using 1
    rfl
  have hN : Measurable N := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  let X : ℕ → Ω → GinibreContinuousNoise n := fun m ω => correspondenceNoiseShift n (q m ω) (N ω)
  let x : Ω → GinibreContinuousNoise n := fun ω => correspondenceNoiseShift n (τ ω) (N ω)
  have hX (m : ℕ) : Measurable (X m) :=
    (correspondenceNoiseShift_continuous n).measurable.comp ((hqm m).prodMk hN)
  have hx : Measurable x :=
    (correspondenceNoiseShift_continuous n).measurable.comp (htm.prodMk hN)
  have hc (m : ℕ) : (range (q m)).Countable := by
    apply (Set.countable_range (fun k : ℕ => (k : ℝ≥0)/((m+1 : ℕ) : ℝ≥0))).mono
    rintro t ⟨ω, rfl⟩
    exact ⟨Nat.ceil (((m+1 : ℕ) : ℝ≥0)*τ ω), rfl⟩
  have hle (m : ℕ) : (fun ω => (τ ω : WithTop ℝ≥0)) ≤ fun ω => (q m ω : WithTop ℝ≥0) := by
    intro ω
    apply WithTop.coe_le_coe.mpr
    apply (le_div_iff₀ (by positivity : 0 < ((m+1 : ℕ) : ℝ≥0))).mpr
    simpa only [mul_comm] using (Nat.le_ceil (((m+1 : ℕ) : ℝ≥0)*τ ω))
  have hlaw (m : ℕ) : (P.restrict A).map (X m) = (P A) • P.map N := by
    ext C hC
    rw [Measure.map_apply (hX m) hC, Measure.restrict_apply ((hX m) hC), Measure.smul_apply]
    have he := correspondenceNoiseShift_countable_actual n B P hB hind α (q m) (hc m)
    have he' : P ((X m) ⁻¹' C ∩ A) =
        P ({ω | ginibreBrownianFullContinuousNoise n (brownianFamilyShift B (q m ω)) α ω ∈ C} ∩ A)
            := by
      apply measure_congr
      filter_upwards [he] with ω hω
      simp only [mem_inter_iff, mem_preimage, Set.mem_ofPred_eq, X, N, hω]
    rw [he']
    simpa only [N, smul_eq_mul, mul_comm] using
        correspondenceBrownian_countable_stopping_fresh_noise n B P hB hind α
      (q m) (range (q m)) (hc m) (fun ω => mem_range_self ω) (hq m) A
      (hτ.measurableSpace_mono (hq m) (hle m) A hA) C hC
  have hl : ∀ᵐ ω ∂P.restrict A, Tendsto (fun m => X m ω) atTop (𝓝 (x ω)) := by
    apply Eventually.of_forall
    intro ω
    exact (correspondenceNoiseShift_continuous n).continuousAt.tendsto.comp
      ((stoppingUpperGrid_tendsto (τ ω)).prodMk_nhds tendsto_const_nhds)
  have hfinite : P A ≠ ∞ := measure_ne_top P A
  let : IsFiniteMeasure ((P A) • P.map N) := (P.map N).smul_finite hfinite
  let : TopologicalSpace.MetrizableSpace (GinibreContinuousNoise n) :=
    Topology.IsEmbedding.subtypeVal.metrizableSpace
  exact correspondence_constantLaw_ae_limit (P.restrict A) X x hX hx hl _ hlaw

end
end GinibrePoincare
