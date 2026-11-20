/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticL2ProductDensity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticL2Product
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Density of actual product L² tensors for finite measures -/

@[expose] public section
open MeasureTheory MeasureTheory.Measure Set
open scoped InnerProductSpace TensorProduct
namespace GinibrePoincare
noncomputable section
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Genuine indicator vectors in a finite-measure L² space. -/
def l2IndicatorVector (s : Set X) (hs : MeasurableSet s) : Lp ℂ 2 μ :=
  (MemLp.indicator hs.nullMeasurableSet (memLp_const (μ := μ) (p := 2) (1 : ℂ))).toLp _

theorem l2IndicatorVector_coeFn (s : Set X) (hs : MeasurableSet s) :
    l2IndicatorVector (μ := μ) s hs =ᵐ[μ] s.indicator (fun _ => (1 : ℂ)) :=
  (MemLp.indicator hs.nullMeasurableSet (memLp_const (μ := μ) (p := 2) (1 : ℂ))).coeFn_toLp

/-- Actual rectangle indicators are genuine pure tensors. -/
theorem l2Product_indicator_rectangle (s : Set X) (t : Set Y)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    l2ProductVector (l2IndicatorVector (μ := μ) s hs) (l2IndicatorVector (μ := ν) t ht) =ᵐ[μ.prod ν]
      (s ×ˢ t).indicator (fun _ => (1 : ℂ)) := by
  have hsu := (quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp (l2IndicatorVector_coeFn s
      hs)
  have htv := (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp (l2IndicatorVector_coeFn t
      ht)
  filter_upwards [l2ProductVector_coeFn (l2IndicatorVector (μ := μ) s hs) (l2IndicatorVector (μ :=
      ν) t ht), hsu, htv]
    with z hz hz1 hz2
  change (l2IndicatorVector (μ := μ) s hs) z.1 = s.indicator (fun _ => (1 : ℂ)) z.1 at hz1
  change (l2IndicatorVector (μ := ν) t ht) z.2 = t.indicator (fun _ => (1 : ℂ)) z.2 at hz2
  rw [hz, hz1, hz2]
  by_cases hx : z.1 ∈ s <;> by_cases hy : z.2 ∈ t <;> simp [hx, hy]

/-- Product tensors separate every vector of the actual finite-product L²
space. The proof uses rectangle uniqueness of the actual vector measure. -/
theorem l2Product_eq_zero_of_inner_pure_tensors (F : Lp ℂ 2 (μ.prod ν))
    (horth : ∀ u : Lp ℂ 2 μ, ∀ v : Lp ℂ 2 ν, ⟪l2ProductVector u v, F⟫_ℂ = 0) : F = 0 := by
  have hFi : Integrable (fun z => F z) (μ.prod ν) := (Lp.memLp F).integrable (by norm_num)
  have hrect (s : Set X) (t : Set Y) (hs : MeasurableSet s) (ht : MeasurableSet t) :
      (∫ z in s ×ˢ t, F z ∂μ.prod ν) = 0 := by
    have hi := horth (l2IndicatorVector s hs) (l2IndicatorVector t ht)
    rw [L2.inner_def] at hi
    have he : (∫ z, ⟪l2ProductVector (l2IndicatorVector (μ := μ) s hs)
        (l2IndicatorVector (μ := ν) t ht) z, F z⟫_ℂ ∂μ.prod ν) =
        ∫ z, (s ×ˢ t).indicator (fun z => F z) z ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [l2Product_indicator_rectangle s t hs ht] with z hz
      rw [hz]
      by_cases hzst : z ∈ s ×ˢ t <;> simp [hzst, RCLike.inner_apply]
    rw [he, integral_indicator (hs.prod ht)] at hi
    exact hi
  have hvm : (μ.prod ν).withDensityᵥ (fun z => F z) = (0 : VectorMeasure (X × Y) ℂ) := by
    apply VectorMeasure.ext_of_generateFrom _ _ generateFrom_prod.symm isPiSystem_prod
    · rw [withDensityᵥ_apply hFi MeasurableSet.univ]
      simpa only [univ_prod_univ, setIntegral_univ, zero_apply] using hrect univ univ
          MeasurableSet.univ MeasurableSet.univ
    · rintro _ ⟨s, hs, t, ht, rfl⟩
      rw [withDensityᵥ_apply hFi (hs.prod ht), hrect s t hs ht]
      rfl
  have hzero : (fun z => F z) =ᵐ[μ.prod ν] (fun _ => (0 : ℂ)) := by
    apply hFi.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ (μ.prod ν))
    change (μ.prod ν).withDensityᵥ (fun z => F z) = (μ.prod ν).withDensityᵥ (0 : X × Y → ℂ)
    rw [withDensityᵥ_zero]
    exact hvm
  apply Lp.ext
  exact hzero.trans (Lp.coeFn_zero ℂ 2 (μ.prod ν)).symm

/-- The completed Hilbert tensor fills the actual finite-product L² space.
Surjectivity follows from proved rectangle separation, not a density axiom. -/
theorem l2ProductCompletedTensorIsometry_surjective :
    Function.Surjective (l2ProductCompletedTensorIsometry (μ := μ) (ν := ν)) := by
  let e := l2ProductCompletedTensorIsometry (μ := μ) (ν := ν)
  let K : ClosedSubmodule ℂ (Lp ℂ 2 (μ.prod ν)) :=
    ⟨e.toLinearMap.range, e.isometry.isClosedEmbedding.isClosed_range⟩
  have hKo : K.toSubmoduleᗮ = ⊥ := by
    apply le_antisymm
    · intro F hF
      change F = 0
      apply l2Product_eq_zero_of_inner_pure_tensors
      intro u v
      have hp : l2ProductVector u v ∈ K := by
        refine ⟨((u ⊗ₜ[ℂ] v : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
          UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)), ?_⟩
        change l2ProductTensorIsometry.toContinuousLinearMap.fromCompletion
          ((u ⊗ₜ[ℂ] v : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
            UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)) = _
        rw [ContinuousLinearMap.fromCompletion_apply_coe]
        rfl
      exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal' _ _).mp hF _ hp)
    · exact bot_le
  let : CompleteSpace (Lp ℂ 2 (μ.prod ν)) := inferInstance
  let : CompleteSpace K.toSubmodule := K.isClosed'.completeSpace_coe
  let : K.toSubmodule.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace
      K.toSubmodule
  have hKt : K.toSubmodule = ⊤ := (Submodule.orthogonal_eq_bot_iff).mp hKo
  intro F
  have hF : F ∈ K.toSubmodule := by rw [hKt]; trivial
  exact hF

/-- Actual product-measure L² is isometrically equivalent to the completed
complex Hilbert tensor for arbitrary finite factors. -/
def l2ProductCompletedTensorEquiv :
    UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) ≃ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearIsometryEquiv.ofSurjective l2ProductCompletedTensorIsometry
    l2ProductCompletedTensorIsometry_surjective

end
end GinibrePoincare
