/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionL2Continuity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionL2Pullback
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Sequences

/-!
# Ginibre stochastic transition L 2 continuity

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `stationaryEndpointL2Operator_continuous`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Strong convergence of genuine contractions extends from a dense family. -/
theorem contractions_tendsto_on_dense_range {E F D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℕ → E →L[ℝ] F) (R : E →L[ℝ] F) (v : D → E)
    (hv : DenseRange v) (hA : ∀ k u, ‖A k u‖ ≤ ‖u‖) (hR : ∀ u, ‖R u‖ ≤ ‖u‖)
    (ht : ∀ d, Tendsto (fun k => A k (v d)) atTop (𝓝 (R (v d)))) :
    ∀ u, Tendsto (fun k => A k u) atTop (𝓝 (R u)) := by
  intro u
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨d, hd⟩ := hv.exists_dist_lt u (by positivity : 0<ε/4)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (ht d) (ε/2) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have hmiddle := hN k hk
  rw [dist_eq_norm] at hd hmiddle ⊢
  have hdecomp : A k u-R u = A k (u-v d)+(A k (v d)-R (v d))+R (v d-u) := by
    simp only [map_sub]
    abel
  rw [hdecomp]
  calc
    _ ≤ ‖A k (u-v d)‖+‖A k (v d)-R (v d)‖+‖R (v d-u)‖ :=
      (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ‖u-v d‖+‖A k (v d)-R (v d)‖+‖v d-u‖ := by
      gcongr
      · exact hA k _
      · exact hR _
    _ < ε := by rw [norm_sub_rev (v d) u]; linarith

/-- Stationary endpoint pullbacks converge strongly when their actual random
endpoints converge almost surely. -/
theorem stationaryEndpointL2Pullback_tendsto {Ω E : Type*}
    [MeasurableSpace Ω] [TopologicalSpace E] [NormalSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure E) [IsFiniteMeasure μ]
    [μ.WeaklyRegular] (X : ℕ → Ω → E) (Y : Ω → E)
    (hX : ∀ k, MeasurePreserving (X k) P μ) (hY : MeasurePreserving Y P μ)
    (hpoint : ∀ᵐ ω ∂P, Tendsto (fun k => X k ω) atTop (𝓝 (Y ω))) :
    ∀ u : Lp ℝ 2 μ, Tendsto (fun k => stationaryEndpointL2Pullback P μ (X k) (hX k) u)
      atTop (𝓝 (stationaryEndpointL2Pullback P μ Y hY u)) := by
  let A := fun k => (stationaryEndpointL2Pullback P μ (X k) (hX k)).toContinuousLinearMap
  let R := (stationaryEndpointL2Pullback P μ Y hY).toContinuousLinearMap
  apply contractions_tendsto_on_dense_range A R (BoundedContinuousFunction.toLp 2 μ ℝ)
    (BoundedContinuousFunction.toLp_denseRange ℝ μ ℝ (by norm_num))
    (fun k u => by exact le_of_eq ((stationaryEndpointL2Pullback P μ (X k) (hX k)).norm_map u))
    (fun u => by exact le_of_eq ((stationaryEndpointL2Pullback P μ Y hY).norm_map u))
  intro f
  let u := BoundedContinuousFunction.toLp 2 μ ℝ f
  have hrep := BoundedContinuousFunction.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℝ) f
  have hnorm (k : ℕ) : ‖A k u-R u‖^2 = ∫ ω, (f (X k ω)-f (Y ω))^2 ∂P := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    have hrX := (hX k).quasiMeasurePreserving.ae_eq_comp hrep
    have hrY := hY.quasiMeasurePreserving.ae_eq_comp hrep
    filter_upwards [Lp.coeFn_sub (A k u) (R u), Lp.coeFn_compMeasurePreserving u (hX k),
      Lp.coeFn_compMeasurePreserving u hY, hrX, hrY] with ω hsub hx hy hfx hfy
    change (A k u-R u) ω*(A k u-R u) ω=_
    rw [hsub]
    change (Lp.compMeasurePreserving (X k) (hX k) u ω-Lp.compMeasurePreserving Y hY u ω)*
      (Lp.compMeasurePreserving (X k) (hX k) u ω-Lp.compMeasurePreserving Y hY u ω)=_
    rw [hx, hy]
    change (u (X k ω)-u (Y ω))*(u (X k ω)-u (Y ω))=_
    change u (X k ω)=f (X k ω) at hfx
    change u (Y ω)=f (Y ω) at hfy
    rw [hfx, hfy]
    ring
  have ht : Tendsto (fun k => ∫ ω, (f (X k ω)-f (Y ω))^2 ∂P) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun k ω => (f (X k ω)-f (Y ω))^2) (f := fun _ => (0 : ℝ))
      (fun _ => (2*‖f‖)^2)
      (fun k => (((f.continuous.measurable.comp (hX k).measurable).sub
        (f.continuous.measurable.comp hY.measurable)).pow_const 2).aestronglyMeasurable)
      (integrable_const _) ?_ ?_
    · simpa using hh
    · intro k
      exact ae_of_all P fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hb : ‖f (X k ω)-f (Y ω)‖ ≤ 2*‖f‖ :=
          (norm_sub_le _ _).trans (by linarith [f.norm_coe_le_norm (X k ω), f.norm_coe_le_norm (Y
                                        ω)])
        simpa [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hb 2
    · filter_upwards [hpoint] with ω hω
      have hf := f.continuous.continuousAt.tendsto.comp hω
      simpa using (hf.sub (tendsto_const_nhds (x := f (Y ω)))).pow 2
  have hsq : Tendsto (fun k => ‖A k u-R u‖^2) atTop (𝓝 0) := by
    simpa only [hnorm] using ht
  have hnormlim : Tendsto (fun k => ‖A k u-R u‖) atTop (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
        Real.sqrt_zero] using hh
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnormlim

/-- Genuine endpoint operators inherit strong continuity from stationary
almost-surely converging terminal endpoints on one actual probability space. -/
theorem stationaryEndpointL2Operator_tendsto {Ω E : Type*}
    [MeasurableSpace Ω] [TopologicalSpace E] [NormalSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure E) [IsFiniteMeasure μ]
    [μ.WeaklyRegular] (Z : Ω → E) (hZ : MeasurePreserving Z P μ)
    (X : ℕ → Ω → E) (Y : Ω → E)
    (hX : ∀ k, MeasurePreserving (X k) P μ) (hY : MeasurePreserving Y P μ)
    (hpoint : ∀ᵐ ω ∂P, Tendsto (fun k => X k ω) atTop (𝓝 (Y ω))) :
    ∀ u : Lp ℝ 2 μ,
      Tendsto (fun k => stationaryEndpointL2Operator P μ Z (X k) hZ (hX k) u)
        atTop (𝓝 (stationaryEndpointL2Operator P μ Z Y hZ hY u)) := by
  intro u
  exact (stationaryEndpointL2Pullback P μ Z hZ).toContinuousLinearMap.adjoint.continuous.tendsto
    (stationaryEndpointL2Pullback P μ Y hY u) |>.comp
      (stationaryEndpointL2Pullback_tendsto P μ X Y hX hY hpoint u)

/-- Actual continuous stationary sample paths yield a strongly continuous
endpoint family on every L² observable. -/
theorem stationaryEndpointL2Operator_continuous {Ω E J : Type*}
    [MeasurableSpace Ω] [TopologicalSpace E] [NormalSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace J] [SequentialSpace J]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure E) [IsFiniteMeasure μ]
    [μ.WeaklyRegular] (Z : Ω → E) (hZ : MeasurePreserving Z P μ)
    (X : J → Ω → E) (hX : ∀ t, MeasurePreserving (X t) P μ)
    (hpath : ∀ᵐ ω ∂P, Continuous (fun t => X t ω)) (u : Lp ℝ 2 μ) :
    Continuous (fun t => stationaryEndpointL2Operator P μ Z (X t) hZ (hX t) u) := by
  apply continuous_iff_seqContinuous.mpr
  intro a t ht
  apply stationaryEndpointL2Operator_tendsto P μ Z hZ
    (fun k => X (a k)) (X t) (fun k => hX (a k)) (hX t) _ u
  filter_upwards [hpath] with ω hω
  exact hω.continuousAt.tendsto.comp ht

end
end GinibrePoincare
