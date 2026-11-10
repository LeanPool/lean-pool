/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.EhrhardType.GaussianImages
public import LeanPool.EhrhardGaussian.EhrhardType.WeakClosure
public import LeanPool.EhrhardGaussian.EhrhardType.Moments
public import LeanPool.EhrhardGaussian.GaussianConvexity.EhrhardMomentBounds

/-! # Characterization of Ehrhard-type laws

The characterization in Lemma 3.6 and the moment consequences in Remark 3.7 of the paper follow from
Ehrhard’s inequality, monotone convex Gaussian representations and weak closure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace EhrhardGaussian.Provider

/-- A probability law is of Ehrhard type if and only if it is the image of the standard Gaussian law
under a monotone convex function. -/
theorem ehrhardType_representation (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) :
    IsEhrhardType ν ↔ ∃ h : ℝ → ℝ, Monotone h ∧ ConvexOn ℝ Set.univ h ∧
      ν = (gaussianReal 0 1).map h :=
  EhrhardType.isEhrhardType_iff_exists_monotone_convex ν hν

/-- Weak limits of Ehrhard-type probability laws are of Ehrhard type, including constant limits. -/
theorem ehrhardType_weakClosure
    (ν : ℕ → ProbabilityMeasure ℝ) (ν' : ProbabilityMeasure ℝ)
    (hlim : Tendsto ν atTop (nhds ν')) (hν : ∀ k, IsEhrhardType (ν k : Measure ℝ)) :
    IsEhrhardType (ν' : Measure ℝ) :=
  EhrhardType.isEhrhardType_of_tendsto ν ν' hlim hν


/-- An Ehrhard-type law with unit exponential mean has an integrable square and satisfies the
variance and negative-moment bounds of Remark 3.7 of the paper. -/
theorem ehrhardType_momentBounds (ν : Measure ℝ) (hν : IsEhrhardType ν)
    (hexp : Integrable (fun x => Real.exp x) ν) (hnorm : ∫ x, Real.exp x ∂ν = 1) :
    Integrable (fun x => x ^ 2) ν ∧ Var[id; ν] ≤ -2 * ∫ x, x ∂ν ∧
      (∀ p : ℝ, 0 ≤ p → Real.log (∫ x, Real.exp (-p * x) ∂ν) ≤
        -p * (∫ x, x ∂ν) + p ^ 2 / 2 * Var[id; ν]) ∧
      (Integrable (fun x => Real.exp (2 * x)) ν →
        -(∫ x, x ∂ν) ≤ Real.log (∫ x, Real.exp (2 * x) ∂ν) / 2 ∧
        ∀ p : ℝ, 0 ≤ p → ∫ x, Real.exp (-p * x) ∂ν ≤
          (∫ x, Real.exp (2 * x) ∂ν) ^ (p * (p + 1) / 2)) :=
  GaussianConvexity.ehrhardType_moment_bounds ν hν hexp hnorm

/-- Every finite convex function of a Gaussian vector has an Ehrhard-type law. -/
theorem ehrhardType_convexGaussianImage {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ConvexOn ℝ Set.univ F) :
    IsEhrhardType (μ.map F) :=
  EhrhardType.isEhrhardType_map_of_convex μ F hF

/-- Ehrhard-type laws include convex Gaussian images, admit monotone convex Gaussian
representations, are closed under weak convergence and satisfy the normalized moment bounds of Lemma
3.6 and Remark 3.7 of the paper. -/
theorem ehrhardType_characterization :
    (∀ {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsGaussian μ]
      (F : EuclideanSpace ℝ (Fin n) → ℝ), ConvexOn ℝ Set.univ F → IsEhrhardType (μ.map F)) ∧
    (∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      (IsEhrhardType ν ↔ ∃ h : ℝ → ℝ, Monotone h ∧ ConvexOn ℝ Set.univ h ∧
        ν = (gaussianReal 0 1).map h)) ∧
    (∀ (ν : ℕ → ProbabilityMeasure ℝ) (ν' : ProbabilityMeasure ℝ), Tendsto ν atTop (nhds ν') →
      (∀ k, IsEhrhardType (ν k : Measure ℝ)) → IsEhrhardType (ν' : Measure ℝ)) ∧
    (∀ ν : Measure ℝ, IsEhrhardType ν → Integrable (fun x => Real.exp x) ν →
      ∫ x, Real.exp x ∂ν = 1 →
      Integrable (fun x => x ^ 2) ν ∧ Var[id; ν] ≤ -2 * ∫ x, x ∂ν ∧
      (∀ p : ℝ, 0 ≤ p → Real.log (∫ x, Real.exp (-p * x) ∂ν) ≤ -p * (∫ x, x ∂ν) + p ^ 2 / 2 *
        Var[id; ν]) ∧
      (Integrable (fun x => Real.exp (2 * x)) ν →
        -(∫ x, x ∂ν) ≤ Real.log (∫ x, Real.exp (2 * x) ∂ν) / 2 ∧
        ∀ p : ℝ, 0 ≤ p → ∫ x, Real.exp (-p * x) ∂ν ≤ (∫ x, Real.exp (2 * x) ∂ν) ^ (p * (p + 1) /
          2))) :=
  by
    refine ⟨?_, ehrhardType_representation, ehrhardType_weakClosure, ehrhardType_momentBounds⟩
    intro n μ hμ F hF
    exact ehrhardType_convexGaussianImage μ F hF

end EhrhardGaussian.Provider
