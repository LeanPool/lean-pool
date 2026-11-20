/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDynamicsAlmostSureStopping.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDynamicsStrongMarkov
/-!
# Correspondence dynamics almost sure stopping

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `correspondence_ginibre_ae_finite_strongMarkov`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Almost surely finite stopping times may be made everywhere finite without
changing their stopped past or any of their values off a null event. -/
theorem correspondenceBrownian_ae_finite_stopping
    {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)) τ)
    (hf : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∃ hσ : IsStoppingTime (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal))
        (fun ω => ((WithTop.untopD (0 : ℝ≥0) (τ ω) : ℝ≥0) : WithTop ℝ≥0)),
      hτ.measurableSpace ≤ hσ.measurableSpace := by
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  have hnull : P {ω | τ ω=⊤} = 0 := by
    simpa only [ae_iff, not_not] using hf
  have hN (s : ℝ≥0) : MeasurableSet[F s] {ω | τ ω=⊤} :=
    ginibreNullAugmentation_null_measurable P _ _ hnull
  have he (s : ℝ≥0) : {ω | ((WithTop.untopD (0 : ℝ≥0) (τ ω) : ℝ≥0) : WithTop ℝ≥0) ≤ s} =
      {ω | τ ω≤s} ∪ {ω | τ ω=⊤} := by
    ext ω
    cases h : τ ω with
    | top =>
      refine iff_of_true ?_ (Or.inr h)
      change ((WithTop.untopD (0 : ℝ≥0) (τ ω) : ℝ≥0) : WithTop ℝ≥0) ≤ s
      rw [h, WithTop.untopD_top]
      exact WithTop.coe_le_coe.mpr zero_le
    | coe t =>
      simp only [Set.mem_ofPred_eq, mem_union, h]
      rw [WithTop.untopD_coe (0 : ℝ≥0) t]
      simp only [WithTop.coe_ne_top, or_false]
  have hσ : IsStoppingTime F (fun ω => ((WithTop.untopD (0 : ℝ≥0) (τ ω) : ℝ≥0) : WithTop ℝ≥0)) := by
    intro s
    rw [he s]
    exact (hτ s).union (hN s)
  refine ⟨hσ,?_⟩
  intro A hA
  have hh := (hτ.measurableSet A).mp hA
  apply (hσ.measurableSet A).mpr
  refine ⟨hh.1, fun s => ?_⟩
  rw [he s, inter_union_distrib_left]
  have hn : P (A ∩ {ω | τ ω=⊤}) = 0 :=
    measure_mono_null inter_subset_right hnull
  exact (hh.2 s).union (ginibreNullAugmentation_null_measurable P _ _ hn)

theorem correspondence_ginibre_ae_finite_strongMarkov
    {Ω A : Type*} [mAmbient : MeasurableSpace Ω] [MeasurableSpace A]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z : {z : Configuration n // CollisionFree z})
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)) τ)
    (hf : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (t : ℝ≥0) (Y : Ω → A) (hY : @Measurable Ω A hτ.measurableSpace _ Y) :
    P.map (fun ω => (Y ω, ginibreBrownianStateProcess α z B (WithTop.untopD (0 : ℝ≥0) (τ ω)+t) ω)) =
      ((P.map (fun ω => (Y ω, ginibreBrownianStateProcess α z B (WithTop.untopD (0 : ℝ≥0) (τ ω))
          ω))).prod
        (P.map (ginibreBrownianFullContinuousNoise n B α))).map
          (fun p => (p.1.1, ginibreCanonicalStateValue α t (p.1.2, p.2))) := by
  obtain ⟨hσ, hle⟩ := correspondenceBrownian_ae_finite_stopping n B P hB τ hτ hf
  exact correspondence_ginibre_stopping_future_past_joint_law hn α z B P hB hind
    (fun ω => WithTop.untopD (0 : ℝ≥0) (τ ω)) hσ t Y (hY.mono hle le_rfl)

end
end GinibrePoincare
