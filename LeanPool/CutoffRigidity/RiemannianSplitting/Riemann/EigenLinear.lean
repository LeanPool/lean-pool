/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedRigidity

/-! # Linearity of `mgrad`, `mlaplacian`, `mgenerator` on smooth functions

Hence smooth `L²` eigenfunctions of `-𝓛` form a vector space.
-/

@[expose] public section

open Bundle MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace CutCur

section EigenLinear

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mgrad_add' {f g : M → ℝ} (hf : MSmooth F f) (hg : MSmooth F g) (x : M) :
    mgrad F (fun y => f y + g y) x = mgrad F f x + mgrad F g x := by
  unfold mgrad
  rw [← map_add]
  congr 1
  exact mvfderiv_add (mdiffAt_of_smooth F hf x) (mdiffAt_of_smooth F hg x)

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mgrad_zero' (x : M) : mgrad F (fun _ : M => (0 : ℝ)) x = 0 := mgrad_const F 0 x

theorem mlaplacian_add {f g : M → ℝ} (hf : MSmooth F f) (hg : MSmooth F g) (x : M) :
    mlaplacian F (fun y => f y + g y) x = mlaplacian F f x + mlaplacian F g x := by
  have e : mgrad F (fun y => f y + g y) = mgrad F f + mgrad F g := funext (mgrad_add' F hf hg)
  unfold mlaplacian
  rw [e, ← Finset.sum_add_distrib]
  have := (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M).isCovariantDerivativeOn (s :=
      Set.univ) |>.add
    (mgrad_mdiffAt F hf x) (mgrad_mdiffAt F hg x) (hx := Set.mem_univ x)
  rw [this]
  simp [inner_add_left]

theorem mlaplacian_const_mul {f : M → ℝ} (c : ℝ) (hf : MSmooth F f) (x : M) :
    mlaplacian F (fun y => c * f y) x = c * mlaplacian F f x := by
  have e : mgrad F (fun y => c * f y) = c • mgrad F f := funext (mgrad_const_mul F c hf)
  unfold mlaplacian
  rw [e, Finset.mul_sum]
  have := (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M).isCovariantDerivativeOn (s :=
      Set.univ) |>.smul_const
    (σ := mgrad F f) (x := x) c (mgrad_mdiffAt F hf x) (hx := Set.mem_univ x)
  rw [this]
  simp [inner_smul_left]

theorem mlaplacian_zero (x : M) : mlaplacian F (fun _ : M => (0 : ℝ)) x = 0 := by
  have e : mgrad F (fun _ : M => (0 : ℝ)) = 0 := funext (mgrad_const F 0)
  unfold mlaplacian
  rw [e, CovariantDerivative.zero]
  simp

theorem mgenerator_add {V f g : M → ℝ} (hf : MSmooth F f) (hg : MSmooth F g) (x : M) :
    mgenerator F V (fun y => f y + g y) x = mgenerator F V f x + mgenerator F V g x := by
  unfold mgenerator
  rw [mlaplacian_add F hf hg, mgrad_add' F hf hg, inner_add_right]; ring

theorem mgenerator_const_mul {V f : M → ℝ} (c : ℝ) (hf : MSmooth F f) (x : M) :
    mgenerator F V (fun y => c * f y) x = c * mgenerator F V f x := by
  unfold mgenerator
  rw [mlaplacian_const_mul F c hf, mgrad_const_mul F c hf, inner_smul_right]; ring

theorem mgenerator_zero {V : M → ℝ} (x : M) : mgenerator F V (fun _ : M => (0 : ℝ)) x = 0 := by
  unfold mgenerator
  rw [mlaplacian_zero, mgrad_zero']; simp

end EigenLinear

end CutCur
