/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.VectorL2Triangle

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Cube

/-! Vector L2 triangle inequality with a narrow analysis import. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section5.RelativeError

theorem RelativeVectorTriangle.quadratic_cross_bound {A B R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hp : ∀ t : ℝ, 0 ≤ t ^ 2 * A - 2 * t * R + B) :
    R ≤ Real.sqrt A * Real.sqrt B := by
  exact AVenhance.Infra.VectorL2Triangle.quadratic_cross_bound hA hB hp

/-- The integral L2 triangle inequality for the actual `Vec 2` carrier. -/
theorem relative_vector_integral_L2_add {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → Vec 2}
    (hf : Integrable (fun x => vecNormSq (f x)) μ)
    (hg : Integrable (fun x => vecNormSq (g x)) μ)
    (hfg : Integrable (fun x => vecDot (f x) (g x)) μ) :
    Real.sqrt (∫ x, vecNormSq (f x + g x) ∂μ) ≤
      Real.sqrt (∫ x, vecNormSq (f x) ∂μ) + Real.sqrt (∫ x, vecNormSq (g x) ∂μ) := by
  exact AVenhance.Infra.VectorL2Triangle.vector_integral_L2_add hf hg hfg

end AVenhance.Infra.Section5.RelativeError
