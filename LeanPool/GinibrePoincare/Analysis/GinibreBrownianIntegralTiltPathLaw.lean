/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltPathLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltFiniteLaw
public import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Ginibre Brownian integral tilt path law

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianBoundedVector_girsanov_whole_path_exists`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Actual continuous vector Girsanov whole-path law on the fixed terminal
interval. The tilted likelihood is the literal exponential of the actual
coordinate stochastic integrals minus half their true time energy. -/
theorem brownianVectorExponentialIntegralDensity_whole_path_law
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (F : ι → ℝ≥0 → Ω → ℝ)
    (hF : ∀ i t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal) t) _ (F i t))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ω, (∑ i, (F i t ω) ^ 2) ≤ C ^ 2)
    (T : ℝ≥0) (hT : 0 < T)
    (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun s => F i s ω) (Set.Icc 0 T))
    (hs : ∀ i n, AEStronglyMeasurable (brownianUniformLeftSum (B i) (F i) T (n + 1)) P)
    (I : ι → Ω → ℝ)
    (hI : ∀ i, TendstoInMeasure P
      (fun n => brownianUniformLeftSum (B i) (F i) T (n + 1)) atTop (I i)) :
    let Q := P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity F T I
        ω))
    let X := fun ω (t : Set.Icc (0 : ℝ≥0) T) i => B i t.val ω-B i 0 ω-
      ∫ s in (0 : ℝ)..(t.val : ℝ), F i (Real.toNNReal s) ω
    let Y := fun ω (t : Set.Icc (0 : ℝ≥0) T) i => B i t.val ω-B i 0 ω
    Measurable X ∧ Measurable Y ∧ Q.map X=P.map Y ∧
      ∀ i, ∀ᵐ ω ∂Q, ContinuousOn (fun t : ℝ≥0 => B i t ω-B i 0 ω-
        ∫ s in (0 : ℝ)..(t : ℝ), F i (Real.toNNReal s) ω) (Set.Icc 0 T) := by
  classical
  dsimp only
  let d := brownianVectorExponentialIntegralDensity F T I
  let Q := P.withDensity (fun ω => ENNReal.ofReal (d ω))
  let X := fun ω (t : Set.Icc (0 : ℝ≥0) T) i => B i t.val ω-B i 0 ω-
    ∫ s in (0 : ℝ)..(t.val : ℝ), F i (Real.toNNReal s) ω
  let Y := fun ω (t : Set.Icc (0 : ℝ≥0) T) i => B i t.val ω-B i 0 ω
  have hd := brownianVectorExponentialIntegralDensity_normalized B P
    (fun i => (hB i).toIsPreBrownianReal) hind F hF C hC hb T hc hs I hI
  let : IsProbabilityMeasure Q := gaussianDensity_isProbabilityMeasure_of_integral_one P d hd.1
      hd.2.1 hd.2.2.1
  have hPQ : P ≪ Q := withDensity_absolutelyContinuous'
    (ENNReal.measurable_ofReal.comp_aemeasurable hd.1.aemeasurable)
    (Eventually.of_forall fun ω => by
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
  have hXm : Measurable X := by
    apply Measurable.of_eval
    intro t
    apply Measurable.of_eval
    intro i
    have hl := brownianVectorExponentialIntegralDensity_finite_states_identDistrib B P hB hind
      F hF C hC hb T hT hc hs I hI (fun _ : Unit => t.val) (fun _ => t.property.2)
    have hm := (measurable_pi_apply i).comp_aemeasurable
      ((measurable_pi_apply ()).comp_aemeasurable hl.aemeasurable_fst)
    exact aemeasurable_iff_measurable.mp (hm.mono_ac hPQ)
  have hYm : Measurable Y := by
    apply Measurable.of_eval
    intro t
    apply Measurable.of_eval
    intro i
    exact (aemeasurable_iff_measurable.mp ((hB i).aemeasurable _)).sub
      (aemeasurable_iff_measurable.mp ((hB i).aemeasurable _))
  let ν := fun J : Finset (Set.Icc (0 : ℝ≥0) T) => P.map (fun ω => J.restrict (Y ω))
  let (J : Finset (Set.Icc (0 : ℝ≥0) T)) : IsProbabilityMeasure (ν J) :=
    (by infer_instance)
  have hprojX : IsProjectiveLimit (Q.map X) ν := by
    intro J
    rw [Measure.map_map (show Measurable J.restrict by fun_prop) hXm]
    exact (brownianVectorExponentialIntegralDensity_finite_states_identDistrib B P hB hind
      F hF C hC hb T hT hc hs I hI (fun t : J => t.val.val) (fun t => t.val.property.2)).map_eq
  have hprojY : IsProjectiveLimit (P.map Y) ν := by
    intro J
    rw [Measure.map_map (show Measurable J.restrict by fun_prop) hYm]
    rfl
  refine ⟨hXm, hYm, hprojX.unique hprojY,?_⟩
  intro i
  exact (withDensity_absolutelyContinuous P _).ae_le
    (brownianCorrectedPath_continuousOn B P hB F T hc i)

/-- Genuine continuous vector Girsanov theorem on a finite horizon: all
stochastic integrals, likelihood normalization and the full tilted Brownian
path law are constructed from bounded continuous adapted integrands. -/
theorem brownianBoundedVector_girsanov_whole_path_exists {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (F : ι → ℝ≥0 → Ω → ℝ)
    (hF : ∀ i t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal) t) _ (F i t))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ω, (∑ i, (F i t ω) ^ 2) ≤ C ^ 2)
    (T : ℝ≥0) (hT : 0 < T)
    (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun s => F i s ω) (Set.Icc 0 T)) :
    ∃ M : ι → ℝ≥0 → Ω → ℝ,
      (∀ i, Martingale (M i) (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) P ∧
        (∀ ω, Continuous (fun t => M i t ω)) ∧ (∀ t, MemLp (M i t) 2 P) ∧
        M i 0 =ᵐ[P] (fun _ => 0) ∧
        ∀ t ≤ T, TendstoInMeasure P
          (fun n => brownianUniformLeftSum (B i) (F i) t (n+1)) atTop (M i t)) ∧
      Integrable (brownianVectorExponentialIntegralDensity F T (fun i => M i T)) P ∧
      (∫ ω, brownianVectorExponentialIntegralDensity F T (fun i => M i T) ω ∂P)=1 ∧
      let Q := P.withDensity (fun ω => ENNReal.ofReal
        (brownianVectorExponentialIntegralDensity F T (fun i => M i T) ω))
      let X := fun ω (t : Set.Icc (0 : ℝ≥0) T) i => B i t.val ω-B i 0 ω-
        ∫ s in (0 : ℝ)..(t.val : ℝ), F i (Real.toNNReal s) ω
      let Y := fun ω (t : Set.Icc (0 : ℝ≥0) T) i => B i t.val ω-B i 0 ω
      Measurable X ∧ Measurable Y ∧ Q.map X=P.map Y ∧
        ∀ i, ∀ᵐ ω ∂Q, ContinuousOn (fun t : ℝ≥0 => B i t ω-B i 0 ω-
          ∫ s in (0 : ℝ)..(t : ℝ), F i (Real.toNNReal s) ω) (Set.Icc 0 T) := by
  classical
  obtain ⟨M, hM, hi, hn, hL⟩ := brownianBoundedVector_exponential_integral_exists_normalized
    B P hB hind F hF C hC hb T hc
  refine ⟨M, hM, hi, hn,?_⟩
  have hFi (i : ι) (t : ℝ≥0) : MemLp (F i t) 2 P := by
    apply MemLp.of_bound
      ((hF i t).mono ((ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)).le t) le_rfl).aestronglyMeasurable C
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    apply abs_le_of_sq_le_sq _ hC
    exact (Finset.single_le_sum (fun j _ => sq_nonneg (F j t ω)) (Finset.mem_univ i)).trans (hb t ω)
  apply brownianVectorExponentialIntegralDensity_whole_path_law B P hB hind F hF C hC hb T hT hc
    (fun i n => (brownianUniformLeftSum_memLp_two B P
      (fun i => (hB i).toIsPreBrownianReal) hind i (F i) (hF i) (hFi i) T
          (n+1)).aestronglyMeasurable)
    (fun i => M i T)
    (fun i => (hM i).2.2.2.2 T le_rfl)

end
end GinibrePoincare
