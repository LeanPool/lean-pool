/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-
Ported from RegularityStructures-dev, commit 852e51c64f977a7cdd3eacab66e0188bc0ed75a2.
Modified for EhrhardGaussian, 2026.
-/
module

public import LeanPool.EhrhardGaussian.Gaussian.Poincare
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Independence.Basic

/-!
# The product standard Gaussian is jointly Gaussian

The coordinate product measure is identified as a jointly Gaussian law using the independent
Gaussian-coordinate theorem from Mathlib.  This keeps the ambient point type as `Fin n → ℝ`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace EhrhardGaussian.Gaussian

/-- The product of finitely many independent standard Gaussian laws is Gaussian. -/
theorem isGaussian_standardGaussianMeasure (n : ℕ) :
    IsGaussian (standardGaussianMeasure n) := by
  let μ : (i : Fin n) → Measure ℝ := fun _ => gaussianReal 0 1
  have hcoord : ∀ i : Fin n,
      HasGaussianLaw (fun x : Fin n → ℝ => x i) (Measure.pi μ) := by
    intro i
    refine ⟨Measurable.aemeasurable (by fun_prop), ?_⟩
    rw [(measurePreserving_eval μ i).map_eq]
    simpa [μ] using (inferInstance : IsGaussian (gaussianReal 0 1))
  have hindep : iIndepFun (fun i (x : Fin n → ℝ) => x i) (Measure.pi μ) := by
    exact iIndepFun_pi (fun _ => aemeasurable_id)
  have hjoint : HasGaussianLaw (fun x : (i : Fin n) → ℝ => fun i => x i)
      (Measure.pi μ) := hindep.hasGaussianLaw hcoord
  have hfun : (fun x : (i : Fin n) → ℝ => fun i => id (x i)) = id := by
    funext x
    rfl
  simpa [standardGaussianMeasure, μ, hfun] using hjoint.isGaussian_map

end EhrhardGaussian.Gaussian

end
