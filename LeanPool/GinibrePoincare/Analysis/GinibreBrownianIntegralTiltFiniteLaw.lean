/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltFiniteLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGirsanovContinuousTime

/-!
# Ginibre Brownian integral tilt finite law

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianVectorExponentialIntegralDensity_finite_states_identDistrib`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Full continuous-time vector Girsanov finite-dimensional laws under one
fixed actual exponential terminal likelihood. Every prescribed time may be
real; all drift corrections are literal ordinary time integrals. -/
theorem brownianVectorExponentialIntegralDensity_finite_states_identDistrib
    {Ω ι α : Type*} [MeasurableSpace Ω] [Fintype ι] [Finite α]
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
      (fun n => brownianUniformLeftSum (B i) (F i) T (n + 1)) atTop (I i))
    (t : α → ℝ≥0) (ht : ∀ a, t a ≤ T) :
    IdentDistrib (fun ω a i => B i (t a) ω-B i 0 ω-
      ∫ s in (0 : ℝ)..(t a : ℝ), F i (Real.toNNReal s) ω)
      (fun ω a i => B i (t a) ω-B i 0 ω)
      (P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity F T I ω))) P
          := by
  have := Fintype.ofFinite α
  classical
  let d := brownianVectorExponentialIntegralDensity F T I
  let Q := P.withDensity (fun ω => ENNReal.ofReal (d ω))
  have hd := brownianVectorExponentialIntegralDensity_normalized B P
    (fun i => (hB i).toIsPreBrownianReal) hind F hF C hC hb T hc hs I hI
  let : IsProbabilityMeasure Q := gaussianDensity_isProbabilityMeasure_of_integral_one P d hd.1
      hd.2.1 hd.2.2.1
  let idx := fun (n : ℕ) (a : α) => (⟨brownianRationalApproxIndex T (t a) n,
    Nat.lt_succ_of_le (brownianRationalApproxIndex_le T (t a) hT (ht a) n)⟩ : Fin (n+2))
  let r := fun n a => T*((idx n a).val : ℝ≥0)/(n+1 : ℕ)
  let X := fun n ω a i => B i (r n a) ω-B i 0 ω-
    ∫ s in (0 : ℝ)..(r n a : ℝ), F i (Real.toNNReal s) ω
  let Y := fun n ω a i => B i (r n a) ω-B i 0 ω
  let x := fun ω a i => B i (t a) ω-B i 0 ω-
    ∫ s in (0 : ℝ)..(t a : ℝ), F i (Real.toNNReal s) ω
  let y := fun ω a i => B i (t a) ω-B i 0 ω
  have hr (n : ℕ) (a : α) : r n a∈Set.Icc 0 T := by
    refine ⟨bot_le,?_⟩
    dsimp only [r]
    rw [mul_div_assoc]
    apply (mul_le_mul_of_nonneg_left ((div_le_one (by positivity : (0 : ℝ≥0)<(n+1 : ℕ))).mpr ?_)
      (show (0 : ℝ≥0)≤T from bot_le)).trans_eq (mul_one T)
    exact_mod_cast brownianRationalApproxIndex_le T (t a) hT (ht a) n
  have hrt (a : α) : Tendsto (fun n => r n a) atTop (𝓝 (t a)) :=
    brownianRationalApproxTime_tendsto T (t a) hT
  have hi (n : ℕ) : IdentDistrib (X n) (Y n) Q P := by
    have hl := brownianVectorExponentialIntegralDensity_rational_states_hasLaw B P
      (fun i => (hB i).toIsPreBrownianReal) hind F hF C hC hb T hc hs I hI (n+1) (Nat.succ_pos n)
    let V := fun ω (p : Fin (n+2)) i => B i (T*(p.val : ℝ≥0)/(n+1 : ℕ)) ω-B i 0 ω
    have hmV : Measurable V := by
      apply Measurable.of_eval
      intro p
      apply Measurable.of_eval
      intro i
      exact (aemeasurable_iff_measurable.mp ((hB i).aemeasurable _)).sub
        (aemeasurable_iff_measurable.mp ((hB i).aemeasurable _))
    have hbase : HasLaw V (P.map V) P := ⟨hmV.aemeasurable, rfl⟩
    have hm : Measurable (fun z : Fin (n+2) → ι→ℝ => fun a => z (idx n a)) := by
      apply Measurable.of_eval
      intro a
      exact measurable_pi_apply _
    exact (hl.identDistrib hbase).comp hm
  have hXae : ∀ᵐ ω ∂Q, Tendsto (fun n => X n ω) atTop (𝓝 (x ω)) := by
    have hp : ∀ᵐ ω ∂P, ∀ i, ContinuousOn (fun s : ℝ≥0 => B i s ω-B i 0 ω-
        ∫ u in (0 : ℝ)..(s : ℝ), F i (Real.toNNReal u) ω) (Set.Icc 0 T) :=
      ae_all_iff.mpr (fun i => brownianCorrectedPath_continuousOn B P hB F T hc i)
    have hpQ : ∀ᵐ ω ∂Q, ∀ i, ContinuousOn (fun s : ℝ≥0 => B i s ω-B i 0 ω-
        ∫ u in (0 : ℝ)..(s : ℝ), F i (Real.toNNReal u) ω) (Set.Icc 0 T) :=
      (withDensity_absolutelyContinuous P _).ae_le hp
    filter_upwards [hpQ] with ω hω
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_pi_nhds.mpr
    intro i
    exact (hω i (t a) ⟨bot_le, ht a⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hrt a, Eventually.of_forall (fun n => hr n a)⟩)
  have hYae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (y ω)) := by
    have hp := ae_all_iff.mpr (fun i => (hB i).cont)
    filter_upwards [hp] with ω hω
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_pi_nhds.mpr
    intro i
    exact ((hω i).tendsto _ |>.comp (hrt a)).sub tendsto_const_nhds
  exact actualIdentDistrib_of_probability_limits Q P X Y x y hi
    (tendstoInMeasure_of_tendsto_ae (fun n => (hi n).aemeasurable_fst.aestronglyMeasurable) hXae)
    (tendstoInMeasure_of_tendsto_ae (fun n => (hi n).aemeasurable_snd.aestronglyMeasurable) hYae)

end
end GinibrePoincare
