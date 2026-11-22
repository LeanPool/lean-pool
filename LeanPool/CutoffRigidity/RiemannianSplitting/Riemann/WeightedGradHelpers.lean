/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedProper
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianCoordinateGradient

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
  have := isContinuousRiemannianBundle_tangent (F := F) (M := M)
  have hsm := CutoffRigidity.contMDiff_manifoldGradient (I := 𝓘(ℝ, F)) (M := M)
    (f := f) (hf.of_le (by norm_num))
  have hc := hsm.continuous
  have h2 : Continuous (fun x => inner ℝ (mgrad F f x) (mgrad F f x)) :=
    Continuous.inner_bundle (E := fun x : M => TangentSpace 𝓘(ℝ, F) x) hc hc
  have h3 : Continuous (fun x => Real.sqrt (inner ℝ (mgrad F f x) (mgrad F f x))) :=
    Real.continuous_sqrt.comp h2
  refine h3.congr (fun x => ?_)
  rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mvfderiv_congr_ev {g₁ g₂ : M → ℝ} {x : M} (h : g₁ =ᶠ[nhds x] g₂) :
    mvfderiv 𝓘(ℝ, F) g₁ x = mvfderiv 𝓘(ℝ, F) g₂ x := by
  simp only [mvfderiv, h.mfderiv_eq]
  ext v
  rfl

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mdiffAt_finset_sum {ι : Type*} (S : Finset ι) (u : ι → M → ℝ) {x : M}
    (hu : ∀ i ∈ S, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (u i) x) :
    MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fun y => ∑ i ∈ S, u i y) x := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using mdifferentiableAt_const
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hu a (Finset.mem_insert_self _ _)).add (ih (fun i hi => hu i (Finset.mem_insert_of_mem
        hi)))

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mvfderiv_finset_sum {ι : Type*} (S : Finset ι) (u : ι → M → ℝ) {x : M}
    (hu : ∀ i ∈ S, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (u i) x) :
    mvfderiv 𝓘(ℝ, F) (fun y => ∑ i ∈ S, u i y) x = ∑ i ∈ S, mvfderiv 𝓘(ℝ, F) (u i) x := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using mvfderiv_const (I := 𝓘(ℝ, F)) (0:ℝ) (x := x)
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    rw [mvfderiv_fun_add (hu a (Finset.mem_insert_self _ _))
      (mdiffAt_finset_sum F S u (fun i hi => hu i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mvfderiv_comp_real (φ : ℝ → ℝ) (ψ : M → ℝ) {x : M} (hφ : DifferentiableAt ℝ φ (ψ x))
    (hψ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ψ x) (v : TangentSpace 𝓘(ℝ, F) x) :
    mvfderiv 𝓘(ℝ, F) (φ ∘ ψ) x v = deriv φ (ψ x) * mvfderiv 𝓘(ℝ, F) ψ x v := by
  have hg : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ (ψ x) := hφ.mdifferentiableAt
  rw [mvfderiv_comp_apply x hg hψ v, mvfderiv_eq_fderiv]
  have : mvfderiv 𝓘(ℝ, F) ψ x v = mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ψ x v := rfl
  rw [this]
  simp only [ContinuousLinearMap.comp_apply]
  have key : ∀ t : ℝ, fderiv ℝ φ (ψ x) t = deriv φ (ψ x) * t := fun t => by
    rw [fderiv_eq_smul_deriv, smul_eq_mul, mul_comm]
  exact key _

end GradHelpers

end CutCur
