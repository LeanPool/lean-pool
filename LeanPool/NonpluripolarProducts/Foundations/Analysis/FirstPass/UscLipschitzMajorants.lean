/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lipschitz majorants of upper semicontinuous functions

This file isolates the metric approximation used in the Bedford--Taylor
upper-semicontinuous-weight lemma.  On a nonempty compact set `K`, the
sup-convolution

`sup (y ∈ K), f y - c * dist x y`

is a finite Lipschitz majorant of `f` when `c ≥ 0`.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

variable {X : Type*} [PseudoMetricSpace X]

/-- The metric sup-convolution of `f` over `K`.  The useful theorems below
assume that `K` is nonempty and compact and that `f` is upper
semicontinuous on `K`, so this supremum is finite. -/
def uscLipschitzMajorant (K : Set X) (f : X → ℝ) (c : ℝ) (x : X) : ℝ :=
  sSup ((fun y => f y - c * dist x y) '' K)

private theorem bddAbove_uscLipschitzMajorant_image {K : Set X} {f : X → ℝ}
    (hK : IsCompact K) (hf : UpperSemicontinuousOn f K) {c : ℝ} (hc : 0 ≤ c)
    (x : X) : BddAbove ((fun y => f y - c * dist x y) '' K) := by
  obtain ⟨C, hC⟩ := (hf.bddAbove_of_isCompact hK)
  refine ⟨C, ?_⟩
  rintro _ ⟨y, hyK, rfl⟩
  exact (sub_le_self _ (mul_nonneg hc dist_nonneg)).trans (hC ⟨y, hyK, rfl⟩)

theorem le_uscLipschitzMajorant {K : Set X} {f : X → ℝ}
    (hK : IsCompact K) (hf : UpperSemicontinuousOn f K) {c : ℝ} (hc : 0 ≤ c)
    {x : X} (hx : x ∈ K) :
    f x ≤ uscLipschitzMajorant K f c x := by
  unfold uscLipschitzMajorant
  have hmem : f x - c * dist x x ∈ (fun y => f y - c * dist x y) '' K :=
    ⟨x, hx, rfl⟩
  simpa using le_csSup (bddAbove_uscLipschitzMajorant_image hK hf hc x) hmem

private theorem uscLipschitzMajorant_sub_le {K : Set X} {f : X → ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty) (hf : UpperSemicontinuousOn f K)
    {c : ℝ} (hc : 0 ≤ c) (x x' : X) :
    uscLipschitzMajorant K f c x ≤
      uscLipschitzMajorant K f c x' + c * dist x x' := by
  unfold uscLipschitzMajorant
  apply csSup_le
  · rcases hKne with ⟨y, hy⟩
    exact ⟨f y - c * dist x y, ⟨y, hy, rfl⟩⟩
  · rintro _ ⟨y, hyK, rfl⟩
    have hle : f y - c * dist x' y ≤
        sSup ((fun z => f z - c * dist x' z) '' K) := by
      exact le_csSup (bddAbove_uscLipschitzMajorant_image hK hf hc x') ⟨y, hyK, rfl⟩
    have hdist : dist x' y ≤ dist x x' + dist x y := by
      simpa [dist_comm x x'] using dist_triangle x' x y
    calc
      f y - c * dist x y
          ≤ (f y - c * dist x' y) + c * dist x x' := by
              linarith [mul_le_mul_of_nonneg_left hdist hc]
      _ ≤ sSup ((fun z => f z - c * dist x' z) '' K) + c * dist x x' :=
        by gcongr

theorem lipschitzWith_uscLipschitzMajorant {K : Set X} {f : X → ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty) (hf : UpperSemicontinuousOn f K)
    {c : ℝ} (hc : 0 ≤ c) :
    LipschitzWith c.toNNReal (uscLipschitzMajorant K f c) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x x'
  rw [Real.dist_eq, Real.coe_toNNReal c hc]
  apply abs_le.2
  constructor
  · have h := uscLipschitzMajorant_sub_le hK hKne hf hc x' x
    rw [dist_comm x' x] at h
    linarith
  · linarith [uscLipschitzMajorant_sub_le hK hKne hf hc x x']

theorem continuous_uscLipschitzMajorant {K : Set X} {f : X → ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty) (hf : UpperSemicontinuousOn f K)
    {c : ℝ} (hc : 0 ≤ c) :
    Continuous (uscLipschitzMajorant K f c) :=
  (lipschitzWith_uscLipschitzMajorant hK hKne hf hc).continuous

theorem uscLipschitzMajorant_antitone {K : Set X} {f : X → ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty) (hf : UpperSemicontinuousOn f K)
    {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (x : X) :
    uscLipschitzMajorant K f d x ≤ uscLipschitzMajorant K f c x := by
  unfold uscLipschitzMajorant
  apply csSup_le
  · exact hKne.image _
  · rintro _ ⟨y, hyK, rfl⟩
    refine (sub_le_sub_left (mul_le_mul_of_nonneg_right hcd dist_nonneg) _).trans ?_
    exact le_csSup (bddAbove_uscLipschitzMajorant_image hK hf hc x) ⟨y, hyK, rfl⟩

/-- On the compact set, the integer-slope sup-convolutions decrease pointwise
to the original upper semicontinuous function. -/
theorem tendsto_uscLipschitzMajorant_nat {K : Set X} {f : X → ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty) (hf : UpperSemicontinuousOn f K)
    {x : X} (hx : x ∈ K) :
    Tendsto (fun n : ℕ => uscLipschitzMajorant K f (n : ℝ) x)
      atTop (𝓝 (f x)) := by
  obtain ⟨C, hC⟩ := hf.bddAbove_of_isCompact hK
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hnear := hf x hx (f x + ε / 2) (lt_add_of_pos_right _ hε2)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((C - f x) / δ)
  have hmul : C - f x < (N : ℝ) * δ := by
    exact (div_lt_iff₀ hδ).mp hN
  have hupperN : uscLipschitzMajorant K f (N : ℝ) x ≤ f x + ε / 2 := by
    unfold uscLipschitzMajorant
    apply csSup_le (hKne.image _)
    rintro _ ⟨y, hyK, rfl⟩
    by_cases hy : dist x y < δ
    · have hyball : y ∈ Metric.ball x δ := by
        simpa [Metric.mem_ball, dist_comm] using hy
      have hfy : f y < f x + ε / 2 := hball ⟨hyball, hyK⟩
      exact (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) dist_nonneg)).trans hfy.le
    · have hdist : δ ≤ dist x y := le_of_not_gt hy
      have hfyC : f y ≤ C := hC ⟨y, hyK, rfl⟩
      have hNdist : (N : ℝ) * δ ≤ (N : ℝ) * dist x y :=
        mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg _)
      linarith
  refine ⟨N, fun n hn => ?_⟩
  have hmono : uscLipschitzMajorant K f (n : ℝ) x ≤
      uscLipschitzMajorant K f (N : ℝ) x :=
    uscLipschitzMajorant_antitone hK hKne hf (Nat.cast_nonneg _)
      (by exact_mod_cast hn) x
  have hlower : f x ≤ uscLipschitzMajorant K f (n : ℝ) x :=
    le_uscLipschitzMajorant hK hf (Nat.cast_nonneg _) hx
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlower)]
  calc
    uscLipschitzMajorant K f (n : ℝ) x - f x
        ≤ ε / 2 := by linarith
    _ < ε := half_lt_self hε

end SGPT.Foundations.Analysis.FirstPass
