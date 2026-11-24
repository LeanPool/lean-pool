/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.UscWeightWeakLimits
public import Mathlib.Topology.MetricSpace.Sequences

/-!
# Eventual upper bounds for weighted integrals with decreasing USC weights

If positive measures converge weakly and uniformly bounded upper
semicontinuous weights decrease to `fLim`, then for a nonnegative test the
weighted integrals are eventually at most `∫ φ fLim dμ + ε`. No convergence of
the weighted integrals is assumed: a violating subsequence would have a
further convergent subsequence, contradicting the limit form of the
upper-semicontinuous-weight inequality.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending

variable {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [T2Space X] [BorelSpace X]

theorem uscWeight_eventually_integral_le
    (μs : ℕ → Measure X) (μ : Measure X)
    [∀ k, IsFiniteMeasureOnCompacts (μs k)] [IsFiniteMeasureOnCompacts μ]
    (K : Set X) (hK : IsCompact K) (hKne : K.Nonempty)
    (f : ℕ → X → ℝ) (fLim φ : X → ℝ) (C : ℝ)
    (hfusc : ∀ k, UpperSemicontinuous (f k))
    (hfanti : ∀ x ∈ K, Antitone (fun k => f k x))
    (hflim : ∀ x ∈ K, Tendsto (fun k => f k x) atTop (𝓝 (fLim x)))
    (hfbound : ∀ k x, x ∈ K → |f k x| ≤ C)
    (hφcont : Continuous φ) (hφcompact : HasCompactSupport φ)
    (hφK : Function.support φ ⊆ K) (hφnonneg : ∀ x, 0 ≤ φ x)
    (hμweak : ∀ g : X → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (fun k => ∫ x, g x ∂(μs k)) atTop (𝓝 (∫ x, g x ∂μ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∫ x, φ x * f k x ∂(μs k) ≤ ∫ x, φ x * fLim x ∂μ + ε := by
  set a : ℕ → ℝ := fun k => ∫ x, φ x * f k x ∂(μs k) with ha
  set L := ∫ x, φ x * fLim x ∂μ
  -- the weighted integrals are bounded
  have hC : 0 ≤ C := by
    obtain ⟨x, hx⟩ := hKne
    exact (abs_nonneg _).trans (hfbound 0 x hx)
  have hb := hμweak φ hφcont hφcompact
  obtain ⟨B, hB⟩ := hb.bddAbove_range
  have hbound (k : ℕ) : |a k| ≤ C * B := by
    have hpt : ∀ x, ‖φ x * f k x‖ ≤ C * φ x := by
      intro x
      by_cases hx : x ∈ K
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφnonneg x), mul_comm]
        exact mul_le_mul_of_nonneg_right (hfbound k x hx) (hφnonneg x)
      · have : φ x = 0 := by
          by_contra h
          exact hx (hφK h)
        simp [this]
    have hint : Integrable (fun x => C * φ x) (μs k) :=
      (hφcont.integrable_of_hasCompactSupport hφcompact).const_mul C
    have h1 := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    rw [integral_const_mul, Real.norm_eq_abs] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (hB ⟨k, rfl⟩) hC)
  by_contra hne
  rw [not_eventually] at hne
  obtain ⟨s, hs, hsgt⟩ := extraction_of_frequently_atTop hne
  have hbdd : Bornology.IsBounded (Set.Icc (-(C * B)) (C * B)) := Metric.isBounded_Icc _ _
  obtain ⟨l, -, t, ht, hlim⟩ := tendsto_subseq_of_bounded hbdd
    (x := fun k => a (s k)) fun k => abs_le.mp (hbound (s k))
  have hst : StrictMono (s ∘ t) := hs.comp ht
  have hle := FirstPass.uscWeight_weakLimit_integral_le_of_hasCompactSupport
    (fun k => μs (s (t k))) μ K hK hKne (fun k => f (s (t k))) fLim φ l C
    (fun k => hfusc _) (fun x hx => (hfanti x hx).comp_monotone hst.monotone)
    (fun x hx => (hflim x hx).comp hst.tendsto_atTop) (fun k => hfbound _)
    hφcont hφcompact hφK hφnonneg
    (fun g hg hgc => (hμweak g hg hgc).comp hst.tendsto_atTop) hlim
  have hge : L + ε ≤ l :=
    ge_of_tendsto hlim (Eventually.of_forall fun k => (not_le.mp (hsgt (t k))).le)
  linarith

end SGPT.Foundations.Analysis.Pending
