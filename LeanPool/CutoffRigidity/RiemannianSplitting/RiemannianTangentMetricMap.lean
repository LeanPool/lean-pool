/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! # Path length under a tangent contraction

A map with a nonexpanding differential contracts the length of every smooth path.
-/

@[expose] public section
open Bundle Set Filter MeasureTheory Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [EMetricSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

theorem pathELength_comp_le_of_norm_mfderiv_le_between
    {φ : M → N} (hφ : ContMDiff I J 1 φ)
    (hNorm : ∀ x (v : TangentSpace I x), ‖(mfderiv I J φ x) v‖ ≤ ‖v‖)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) :
    pathELength J (φ ∘ γ) a b ≤ pathELength I γ a b := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_mono
  intro t
  dsimp only
  rw [mfderiv_comp t ((hφ.mdifferentiable one_ne_zero) _) ((hγ.mdifferentiable one_ne_zero) _)]
  change ‖(mfderiv I J φ (γ t)) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)‖ₑ ≤
    ‖(mfderiv 𝓘(ℝ, ℝ) I γ t) 1‖ₑ
  change (‖(mfderiv I J φ (γ t)) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)‖₊ : ℝ≥0∞) ≤
    (‖(mfderiv 𝓘(ℝ, ℝ) I γ t) 1‖₊ : ℝ≥0∞)
  exact_mod_cast hNorm (γ t) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)

end CutoffRigidity
