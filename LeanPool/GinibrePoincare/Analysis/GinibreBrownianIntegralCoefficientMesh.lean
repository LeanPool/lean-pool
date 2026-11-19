/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralCoefficientMesh.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoPathMesh
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Actual finite sampled coefficient oscillations vanish in mean square. -/

@[expose] public section
open MeasureTheory Filter Metric
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The maximum over `i : κ` of `‖F (a i) ω - F (b i) ω‖`, comparing a coefficient process
sampled at two families of times. -/
def brownianCoefficientSampleMesh {Ω κ : Type*} [Fintype κ] [Nonempty κ]
    (F : ℝ≥0 → Ω → ℝ) (a b : κ → ℝ≥0) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ‖F (a i) ω-F (b i) ω‖)

theorem brownianCoefficientSampleMesh_measurable {Ω κ : Type*}
    [MeasurableSpace Ω] [Fintype κ] [Nonempty κ]
    (F : ℝ≥0 → Ω → ℝ) (a b : κ → ℝ≥0) (hF : ∀ t, Measurable (F t)) :
    Measurable (brownianCoefficientSampleMesh F a b) := by
  unfold brownianCoefficientSampleMesh
  have h : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun i ω => ‖F (a i) ω-F (b i) ω‖)) := by
    apply Finset.sup'_induction
    · exact fun f hf g hg => hf.sup hg
    · intro i hi
      exact ((hF (a i)).sub (hF (b i))).norm
  convert h using 1
  funext ω
  exact (Finset.sup'_apply Finset.univ_nonempty (fun i ω => ‖F (a i) ω-F (b i) ω‖) ω).symm

theorem brownianCoefficientSampleMesh_tendsto {Ω α : Type*} {l : Filter α}
    (κ : α → Type*) [∀ n, Fintype (κ n)] [∀ n, Nonempty (κ n)]
    (F : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (a b : (n : α) → κ n → ℝ≥0)
    (ha : ∀ n i, a n i ∈ Set.Icc 0 T) (hb : ∀ n i, b n i ∈ Set.Icc 0 T)
    (δ : α → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hab : ∀ n i, dist (a n i) (b n i) ≤ δ n)
    (ω : Ω) (hc : ContinuousOn (fun t => F t ω) (Set.Icc 0 T)) :
    Tendsto (fun n => brownianCoefficientSampleMesh F (a n) (b n) ω) l (𝓝 0) := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hc
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨d, hd, hdu⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  filter_upwards [hδ.eventually (gt_mem_nhds hd)] with n hn
  have hnonneg : 0 ≤ brownianCoefficientSampleMesh F (a n) (b n) ω := by
    exact (norm_nonneg _).trans (Finset.le_sup' (f := fun i => ‖F (a n i) ω-F (b n i) ω‖)
      (Finset.mem_univ (Classical.arbitrary (κ n))))
  rw [dist_zero_right, Real.norm_of_nonneg hnonneg]
  apply (Finset.sup'_lt_iff Finset.univ_nonempty).mpr
  intro i hi
  simpa only [dist_eq_norm] using hdu _ (ha n i) _ (hb n i) ((hab n i).trans_lt hn)

theorem brownianCoefficientSampleMesh_tendsto_meanSquare {Ω α : Type*}
    [MeasurableSpace Ω] {l : Filter α} [l.IsCountablyGenerated]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : α → Type*) [∀ n, Fintype (κ n)] [∀ n, Nonempty (κ n)]
    (F : ℝ≥0 → Ω → ℝ) (hF : ∀ t, Measurable (F t)) (T : ℝ≥0)
    (a b : (n : α) → κ n → ℝ≥0)
    (ha : ∀ n i, a n i ∈ Set.Icc 0 T) (hb : ∀ n i, b n i ∈ Set.Icc 0 T)
    (δ : α → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hab : ∀ n i, dist (a n i) (b n i) ≤ δ n)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => F t ω) (Set.Icc 0 T))
    (C : ℝ) (_ : 0 ≤ C) (hbound : ∀ t ∈ Set.Icc 0 T, ∀ ω, ‖F t ω‖ ≤ C) :
    Tendsto (fun n => ∫ ω, (brownianCoefficientSampleMesh F (a n) (b n) ω)^2 ∂P)
      l (𝓝 0) := by
  have hm (n : α) : Measurable (fun ω => (brownianCoefficientSampleMesh F (a n) (b n) ω)^2) :=
    (brownianCoefficientSampleMesh_measurable F (a n) (b n) hF).pow_const 2
  have hbnd (n : α) (ω : Ω) : ‖(brownianCoefficientSampleMesh F (a n) (b n) ω)^2‖ ≤ (2*C)^2 := by
    have hnn : 0 ≤ brownianCoefficientSampleMesh F (a n) (b n) ω :=
      (norm_nonneg _).trans (Finset.le_sup' (f := fun i => ‖F (a n i) ω-F (b n i) ω‖)
        (Finset.mem_univ (Classical.arbitrary (κ n))))
    have hle : brownianCoefficientSampleMesh F (a n) (b n) ω ≤ 2*C := by
      apply Finset.sup'_le
      intro i hi
      exact (norm_sub_le _ _).trans (by linarith [hbound _ (ha n i) ω, hbound _ (hb n i) ω])
    rw [norm_pow, Real.norm_of_nonneg hnn]
    exact pow_le_pow_left₀ hnn hle 2
  have hh := tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => (2*C)^2)
    (Eventually.of_forall fun n => (hm n).aestronglyMeasurable)
    (Eventually.of_forall fun n => Eventually.of_forall (hbnd n)) (integrable_const _)
    (hc.mono fun ω hw => (brownianCoefficientSampleMesh_tendsto κ F T a b ha hb δ hδ hab ω hw).pow
        2)
  simpa using hh

/-- Bounded measurable coefficients give an integrable actual finite oscillation. -/
theorem brownianCoefficientSampleMesh_integrable_sq {Ω κ : Type*}
    [MeasurableSpace Ω] [Fintype κ] [Nonempty κ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ≥0 → Ω → ℝ) (hF : ∀ t, Measurable (F t))
    (a b : κ → ℝ≥0) (C : ℝ) (_ : 0 ≤ C)
    (hbound : ∀ t ω, ‖F t ω‖ ≤ C) :
    Integrable (fun ω => (brownianCoefficientSampleMesh F a b ω)^2) P := by
  apply Integrable.mono' (integrable_const ((2*C)^2))
    ((brownianCoefficientSampleMesh_measurable F a b hF).pow_const 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro ω
  have hnn : 0 ≤ brownianCoefficientSampleMesh F a b ω :=
    (norm_nonneg _).trans (Finset.le_sup' (f := fun i => ‖F (a i) ω-F (b i) ω‖)
      (Finset.mem_univ (Classical.arbitrary κ)))
  have hle : brownianCoefficientSampleMesh F a b ω ≤ 2*C := by
    apply Finset.sup'_le
    intro i hi
    exact (norm_sub_le _ _).trans (by linarith [hbound (a i) ω, hbound (b i) ω])
  rw [norm_pow, Real.norm_of_nonneg hnn]
  exact pow_le_pow_left₀ hnn hle 2

end
end GinibrePoincare
