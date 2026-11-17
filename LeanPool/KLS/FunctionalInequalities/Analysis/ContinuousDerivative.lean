/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Mollification.Basic
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Classical derivatives from continuous a.e. derivatives

A Lipschitz map between finite-dimensional real inner product spaces whose a.e. derivative agrees
a.e. with a continuous
field is differentiable everywhere with that derivative, hence `C¹`. The proof mollifies by
shrinking bumps
(`hasFDerivAt_convolution_normed_of_lipschitz`) and passes to the locally uniform limit of the
derivatives.
-/

@[expose] public section

/-! ## Lipschitz maps with a continuous a.e. derivative -/

section ContinuousAEDerivative

open MeasureTheory Set Filter
open scoped NNReal Convolution Topology

namespace FunctionalInequalities.Analysis

/--
A Lipschitz map whose derivative (which exists a.e.) agrees a.e. with a continuous field `B` is
differentiable
everywhere with derivative `B`, hence `C¹`. Proof: shrinking bump mollifications converge pointwise,
their derivatives are
the mollified `B` (`hasFDerivAt_convolution_normed_of_lipschitz`), which converge locally uniformly,
and the locally uniform
derivative-limit theorem applies. -/
theorem hasFDerivAt_of_lipschitz_continuous_ae_fderiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {F : E → E} {L : ℝ≥0} (hF : LipschitzWith L F) (B : E → E →L[ℝ] E) (hB : Continuous B)
    (hAE : fderiv ℝ F =ᵐ[(volume : Measure E)] B) :
    (∀ x, HasFDerivAt F (B x) x) ∧ ContDiff ℝ 1 F := by
  classical
  let φ : ℕ → ContDiffBump (0 : E) := fun k =>
    ContDiffBump.mk (1 / (2 * ((k : ℝ) + 1))) (1 / ((k : ℝ) + 1)) (by positivity)
      (by
        have hk : 0 < (k : ℝ) + 1 := by positivity
        apply (div_lt_div_iff₀ (by positivity) hk).2
        nlinarith)
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := by
    dsimp [φ]
    have hnat : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop := by
      rw [tendsto_atTop]
      intro a
      obtain ⟨m, hm⟩ := exists_nat_gt a
      filter_upwards [eventually_ge_atTop m] with k hk
      have hmk : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    convert tendsto_inv_atTop_zero.comp hnat using 1
    funext k
    simp only [Function.comp_apply, one_div]
  let A := fun m =>
    convolution ((φ m).normed (volume : Measure E)) F (ContinuousLinearMap.lsmul ℝ ℝ)
      (volume : Measure E)
  let D := fun m =>
    convolution ((φ m).normed (volume : Measure E)) B (ContinuousLinearMap.lsmul ℝ ℝ)
      (volume : Measure E)
  have hDeriv (m : ℕ) (x : E) : HasFDerivAt (A m) (D m x) x := by
    have hEq :
      convolution ((φ m).normed (volume : Measure E)) (fderiv ℝ F)
          (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E) =
        convolution ((φ m).normed (volume : Measure E)) B (ContinuousLinearMap.lsmul ℝ ℝ)
          (volume : Measure E) :=
      convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) Filter.EventuallyEq.rfl hAE
    exact (hasFDerivAt_convolution_normed_of_lipschitz hF (φ m) x).congr_fderiv (congrFun hEq x)
  have hLocal : TendstoLocallyUniformly D B atTop := by
    rw [tendstoLocallyUniformly_iff_forall_tendsto]
    intro x
    have hConv : Tendsto (fun p : ℕ × E => D p.1 p.2) (atTop ×ˢ 𝓝 x) (𝓝 (B x)) :=
      ContDiffBump.convolution_tendsto_right (μ := (volume : Measure E)) (φ := fun p : ℕ × E =>
        φ p.1) (g := fun _ : ℕ × E => B) (k := Prod.snd) (hφ.comp tendsto_fst)
        (Eventually.of_forall fun _ => hB.aestronglyMeasurable)
        ((hB.tendsto x).comp tendsto_snd) tendsto_snd
    exact
      (((hB.tendsto x).comp tendsto_snd).prodMk_nhds hConv).mono_right
        (nhds_le_uniformity (B x))
  have hPoint (x : E) : Tendsto (fun m => A m x) atTop (𝓝 (F x)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous hφ hF.continuous x
  have hAll (x : E) : HasFDerivAt F (B x) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      (tendstoLocallyUniformlyOn_univ.mpr hLocal) (fun m y _ => hDeriv m y)
      (fun y _ => hPoint y) (mem_univ x)
  exact ⟨hAll, contDiff_one_iff_hasFDerivAt.mpr ⟨B, hB, hAll⟩⟩

end FunctionalInequalities.Analysis

end ContinuousAEDerivative
