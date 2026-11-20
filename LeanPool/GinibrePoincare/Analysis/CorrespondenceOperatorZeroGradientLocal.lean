/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorZeroGradientLocal.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorZeroGradientMollifier
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityInteriorCutoff
public import Mathlib.Analysis.SpecificLimits.Basic
/-!
# Correspondence operator zero gradient local

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperator_zero_gradient_local_constant`.
-/

@[expose] public section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
/-- A genuine unrestricted weak zero-gradient function is almost everywhere
constant on every ball whose triple-radius closure is collision-free. -/
theorem correspondenceOperator_zero_gradient_local_constant {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (hu : IsGinibreDistributionalGradient n u 0)
    (x : Configuration n) (r : ℝ) (hr : 0 < r)
    (hball : closedBall x (3 * r) ⊆ {z | CollisionFree z}) :
    ∃ c : ℝ,∀ᵐ y ∂(volume : Measure (Configuration n)), y∈ball x r→u y=c := by
  obtain ⟨η, hη, hcη, hsη, hηone⟩ := ginibreLocalRegularity_exists_compact_interior_cutoff
    n hn (closedBall x (3*r)) (isCompact_closedBall _ _) hball
  let v : Configuration n→ℝ := fun y => u y*η y
  have hv : LocallyIntegrable v volume :=
    (integrable_mul_collisionFree_test _ η hu.1 hη.continuous hcη hsη).locallyIntegrable
  let φ : ℕ→ContDiffBump (0 : Configuration n) := fun m =>
    ⟨r/(2*((m : ℝ)+1)), r/((m : ℝ)+1), by positivity, by
      have hm : 0<(m : ℝ)+1 := by positivity
      apply (div_lt_div_iff₀ (by positivity) hm).mpr
      nlinarith⟩
  let V : ℕ→Configuration n→ℝ := fun m =>
    v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ m).normed volume
  have hrad (m : ℕ) : (φ m).rOut≤r := by
    change r/((m : ℝ)+1)≤r
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hVs (m : ℕ) : ContDiff ℝ ∞ (V m) :=
    (φ m).hasCompactSupport_normed.contDiff_convolution_right _ hv (φ m).contDiff_normed
  have hVd (m : ℕ) (a : Configuration n) (ha : a∈ball x r) : fderiv ℝ (V m) a=0 := by
    have hsupport : tsupport (fun y => (φ m).normed volume (a-y))⊆closedBall x (3*r) := by
      have he : tsupport (fun y => (φ m).normed volume (a-y))=
          (Homeomorph.subLeft a) ⁻¹' tsupport ((φ m).normed volume) :=
        by simpa only [Function.comp_def, Homeomorph.subLeft_apply] using
          tsupport_comp_eq_preimage ((φ m).normed volume) (Homeomorph.subLeft a)
      rw [he, (φ m).tsupport_normed_eq]
      intro y hy
      have hy' : dist a y≤(φ m).rOut := by
        simpa only [mem_preimage, Homeomorph.subLeft_apply, mem_closedBall, dist_zero_right,
          ← dist_eq_norm] using hy
      have hax : dist a x<r := ha
      have hdist := dist_triangle y a x
      have hya : dist y a≤r := by rw [dist_comm]; exact hy'.trans (hrad m)
      change dist y x≤3*r
      linarith
    apply correspondenceOperator_zero_gradient_mollification_fderiv hn u hu η hη hcη hsη
      ((φ m).normed volume) (φ m).contDiff_normed (φ m).hasCompactSupport_normed a
      (hsupport.trans hball)
    intro y hy
    exact (hηone y (hsupport hy)).eq_of_nhds
  have hconst (m : ℕ) (a b : Configuration n) (ha : a∈ball x r) (hb : b∈ball x r) :
      V m a=V m b :=
    isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball x r).isPreconnected
      ((hVs m).differentiable (by simp)).differentiableOn (hVd m) ha hb
  have hradlim : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul r
    simpa only [φ, mul_one_div, mul_zero] using hh
  have hratio : ∀ᶠ m in atTop, (φ m).rOut≤2*(φ m).rIn := by
    apply Eventually.of_forall
    intro m
    dsimp [φ]
    have hm : (m : ℝ)+1≠0 := by positivity
    field_simp
   ; linarith
  have hconv : ∀ᵐ y ∂(volume : Measure (Configuration n)),
      Tendsto (fun m => V m y) atTop (𝓝 (v y)) := by
    have hh := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hradlim hratio hv
    have hflip : (ContinuousLinearMap.lsmul ℝ ℝ).flip=ContinuousLinearMap.lsmul ℝ ℝ := by
      ext
      simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    simpa only [V, convolution_symm (ContinuousLinearMap.lsmul ℝ ℝ) hflip] using hh
  obtain ⟨a, ha, hconvA⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (measure_ball_pos (volume : Measure (Configuration n)) x hr).ne'
    (ae_restrict_of_ae hconv)
  refine ⟨v a,?_⟩
  filter_upwards [hconv] with y hy hxy
  have hlim : Tendsto (fun m => V m y) atTop (𝓝 (v a)) := by
    exact hconvA.congr (fun m => (hconst m y a hxy ha).symm)
  have hvy : v y=v a := tendsto_nhds_unique hy hlim
  have hηy : η y=1 := (hηone y (ball_subset_closedBall (show y∈ball x (3*r) from
    ball_subset_ball (by linarith) hxy))).eq_of_nhds
  simpa only [v, hηy, mul_one] using hvy
end
end GinibrePoincare
