/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Lipschitz bounds for total gradients and composed exponents

A finite-dimensional Lipschitz potential with a Lipschitz total gradient gives a globally
Lipschitz exponent `-u + V ∘ gradient u` when `V` is continuously differentiable. The separate
gradient/derivative identification retains its complete-inner-product-space assumptions.
Directional Fréchet-derivative bounds require only a real normed space.
-/

@[expose] public section

section
open Set Metric
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- Produce the global Lipschitz exponent from the actual bounded total gradient. -/
theorem exists_lipschitzWith_neg_add_comp_gradient {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) :
    ∃ LF : NNReal, LipschitzWith LF (fun x => -u x + V (gradient u x)) := by
  have hgrad_bound (x : EuclideanSpace ℝ (Fin n)) :
      ‖gradient u x‖ ≤ (L : ℝ) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (norm_fderiv_le_of_lipschitz (x₀ := x) ℝ hL)
  obtain ⟨C, hC⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ))
      hV.locallyLipschitz.locallyLipschitzOn
  have hmaps : MapsTo (gradient u) univ
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ)) := by
    intro x _
    simpa only [mem_closedBall, dist_zero_right] using hgrad_bound x
  have hcomp : LipschitzWith (C * G) (V ∘ gradient u) :=
    lipschitzOnWith_univ.mp (hC.comp hG.lipschitzOnWith hmaps)
  exact ⟨L + C * G, hL.neg.add hcomp⟩

end FunctionalInequalities.Analysis

section

open Filter Topology
open scoped ContDiff ENNReal

namespace FunctionalInequalities.Energy.Euclidean.LipschitzApproximation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Gradient

variable [CompleteSpace E]

theorem norm_gradient_eq_norm_fderiv (f : E → ℝ) (x : E) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  LinearIsometryEquiv.norm_map _ _

theorem norm_gradient_le_of_lipschitz {K : NNReal} {f : E → ℝ} (hf : LipschitzWith K f) (x : E) :
    ‖gradient f x‖ ≤ K := by
  rw [norm_gradient_eq_norm_fderiv]; exact norm_fderiv_le_of_lipschitz ℝ hf

theorem gradient_eq_of_hasFDerivAt {f : E → ℝ} {L : E →L[ℝ] ℝ} {x : E} (h : HasFDerivAt f L x) :
    gradient f x = (InnerProductSpace.toDual ℝ E).symm L :=
  (hasFDerivAt_iff_hasGradientAt.mp h).gradient

end Gradient

end FunctionalInequalities.Energy.Euclidean.LipschitzApproximation

namespace FunctionalInequalities.Analysis
/-- A Lipschitz bound controls the total directional Frechet derivative. -/
theorem norm_fderiv_apply_le_of_lipschitz {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {f : E → ℝ} {L : NNReal} (hf : LipschitzWith L f) (v x : E) :
    ‖fderiv ℝ f x v‖ ≤ (L : ℝ) * ‖v‖ :=
  (fderiv ℝ f x).le_opNorm v |>.trans
    (mul_le_mul_of_nonneg_right
      (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))


end FunctionalInequalities.Analysis
