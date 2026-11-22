/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedInterface
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-! # Small helpers on `mgrad` and `mvfderiv` -/

@[expose] public section

open Bundle MeasureTheory Filter Set Manifold
open scoped Manifold ContDiff ENNReal Topology


namespace CutCur

section GradHelpers

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

include F

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mgrad_inner (f : M → ℝ) (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    inner ℝ (mgrad F f x) v = mvfderiv 𝓘(ℝ, F) f x v :=
  CutoffRigidity.inner_manifoldGradient 𝓘(ℝ, F) f x v

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem abs_mvfderiv_le_norm_mgrad (f : M → ℝ) (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    |mvfderiv 𝓘(ℝ, F) f x v| ≤ ‖mgrad F f x‖ * ‖v‖ := by
  rw [← mgrad_inner F]
  exact abs_real_inner_le_norm _ _

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem norm_mgrad_le_of {f : M → ℝ} {x : M} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ v : TangentSpace 𝓘(ℝ, F) x, |mvfderiv 𝓘(ℝ, F) f x v| ≤ B * ‖v‖) :
    ‖mgrad F f x‖ ≤ B := by
  have h1 := h (mgrad F f x)
  rw [← mgrad_inner F, real_inner_self_eq_norm_sq] at h1
  rcases (norm_nonneg (mgrad F f x)).eq_or_lt with h0 | h0
  · rw [← h0]; exact hB
  · rw [abs_of_nonneg (by positivity)] at h1
    nlinarith

theorem continuous_norm_mgrad {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f) :
    Continuous (fun x => ‖mgrad F f x‖) := by
  let : IsContinuousRiemannianBundle F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := 𝓘(ℝ, F)) (n := ∞)
  change Continuous (fun x => ‖CutoffRigidity.manifoldGradient 𝓘(ℝ, F) f x‖)
  rw [CutoffRigidity.manifoldGradient_eq_mgradient]
  exact TauCeti.Manifold.continuous_norm_mgradient (hf.of_le (by simp))

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mvfderiv_congr_ev {g₁ g₂ : M → ℝ} {x : M} (h : g₁ =ᶠ[nhds x] g₂) :
    mvfderiv 𝓘(ℝ, F) g₁ x = mvfderiv 𝓘(ℝ, F) g₂ x := by
  exact h.mvfderiv_eq

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mvfderiv_finset_sum {ι : Type*} (S : Finset ι) (u : ι → M → ℝ) {x : M}
    (hu : ∀ i ∈ S, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (u i) x) :
    mvfderiv 𝓘(ℝ, F) (fun y => ∑ i ∈ S, u i y) x = ∑ i ∈ S, mvfderiv 𝓘(ℝ, F) (u i) x := by
  exact TauCeti.mvfderiv_fun_sum hu

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mvfderiv_comp_real (φ : ℝ → ℝ) (ψ : M → ℝ) {x : M} (hφ : DifferentiableAt ℝ φ (ψ x))
    (hψ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ψ x) (v : TangentSpace 𝓘(ℝ, F) x) :
    mvfderiv 𝓘(ℝ, F) (φ ∘ ψ) x v = deriv φ (ψ x) * mvfderiv 𝓘(ℝ, F) ψ x v := by
  rw [TauCeti.mvfderiv_scalar_comp hψ hφ]
  rfl

end GradHelpers

end CutCur
