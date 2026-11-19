/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianProjectionIndependence.lean.
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

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! # Independence of orthogonal Gaussian process projections

A jointly Gaussian vector process with Brownian covariance splits into
independent processes under orthogonal projections. This isolates the noise
factorization step from the separate Itô and singular-SDE arguments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace GinibrePoincare

/-- Gaussianity and the standard Brownian covariance form. This packages only the properties needed
for independence; it does not assert path continuity or zero initial value. -/
structure IsGaussianProcessWithBrownianCovariance {Ω E : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (B : ℝ≥0 → Ω → E) (μ : Measure Ω) : Prop where
  gaussian : IsGaussianProcess B μ
  covariance : ∀ (s t : ℝ≥0) (x y : E),
    ProbabilityTheory.covariance (fun ω => inner ℝ x (B s ω)) (fun ω => inner ℝ y (B t ω)) μ =
      min s t * inner ℝ x y

/-- A continuous, zero-start Gaussian vector process with standard Brownian
covariance. -/
structure IsBrownianVectorProcess {Ω E : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (B : ℝ≥0 → Ω → E) (μ : Measure Ω) : Prop
    extends IsGaussianProcessWithBrownianCovariance B μ where
  continuous : ∀ᵐ ω ∂μ, Continuous (B · ω)
  zero_start : ∀ᵐ ω ∂μ, B 0 ω = 0

/-- A projection-valued Brownian process: the covariance is the Euclidean
inner product after applying the projection. -/
structure IsProjectedBrownianVectorProcess {Ω E : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (B : ℝ≥0 → Ω → E) (μ : Measure Ω) (P : E →L[ℝ] E) : Prop where
  gaussian : IsGaussianProcess B μ
  covariance : ∀ (s t : ℝ≥0) (x y : E),
    ProbabilityTheory.covariance (fun ω => inner ℝ x (B s ω))
      (fun ω => inner ℝ y (B t ω)) μ = min s t * inner ℝ (P x) (P y)
  continuous : ∀ᵐ ω ∂μ, Continuous (B · ω)
  zero_start : ∀ᵐ ω ∂μ, B 0 ω = 0

/-- Linear projections preserve Gaussian paths and transform Brownian
covariance by the adjoint on the test vectors. -/
theorem IsBrownianVectorProcess.project
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → E}
    (hB : IsBrownianVectorProcess B μ) (P : E →L[ℝ] E)
    (hPadj : ∀ x y, inner ℝ x (P y) = inner ℝ (P x) y) :
    IsProjectedBrownianVectorProcess (fun t ω => P (B t ω)) μ P := by
  refine ⟨hB.gaussian.comp_left (fun _ => P), ?_, ?_, ?_⟩
  · intro s t x y
    have hx : (fun ω => inner ℝ x (P (B s ω))) =
        (fun ω => inner ℝ (P x) (B s ω)) := by
      funext ω
      exact hPadj x (B s ω)
    have hy : (fun ω => inner ℝ y (P (B t ω))) =
        (fun ω => inner ℝ (P y) (B t ω)) := by
      funext ω
      exact hPadj y (B t ω)
    rw [hx, hy, hB.covariance s t (P x) (P y)]
  · filter_upwards [hB.continuous] with ω hω
    exact P.continuous.comp hω
  · filter_upwards [hB.zero_start] with ω hω
    simp [hω]

theorem orthogonalGaussianProjections_indepFun
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → E}
    (hB : IsGaussianProcessWithBrownianCovariance B μ)
    (P Q : E →L[ℝ] E)
    (hPadj : ∀ x y, inner ℝ x (P y) = inner ℝ (P x) y)
    (hQadj : ∀ x y, inner ℝ x (Q y) = inner ℝ (Q x) y)
    (hPQ : ∀ x y, inner ℝ (P x) (Q y) = 0) :
    IndepFun (fun ω t => P (B t ω)) (fun ω t => Q (B t ω)) μ := by
  let X : ℝ≥0 → Ω → E := fun t ω => P (B t ω)
  let Y : ℝ≥0 → Ω → E := fun t ω => Q (B t ω)
  have hJoint : IsGaussianProcess (Sum.elim X Y) μ := by
    apply hB.gaussian.of_isGaussianProcess
    intro p
    cases p with
    | inl t =>
        refine ⟨{t}, ?_, ?_⟩
        · exact
            { toFun := fun x => P (x ⟨t, by simp⟩)
              map_add' := by intro x y; simp
              map_smul' := by intro a x; simp }
        · intro ω
          simp [X, Finset.restrict_def]
    | inr t =>
        refine ⟨{t}, ?_, ?_⟩
        · exact
            { toFun := fun x => Q (x ⟨t, by simp⟩)
              map_add' := by intro x y; simp
              map_smul' := by intro a x; simp }
        · intro ω
          simp [Y, Finset.restrict_def]
  have hX : ∀ t, AEMeasurable (X t) μ := fun t => hJoint.aemeasurable (Sum.inl t)
  have hY : ∀ t, AEMeasurable (Y t) μ := fun t => hJoint.aemeasurable (Sum.inr t)
  apply hJoint.indepFun_of_covariance_inner hX hY
  intro s t x y
  have hcov := hB.covariance s t (P x) (Q y)
  have hx : (fun ω => inner ℝ x (X s ω)) = (fun ω => inner ℝ (P x) (B s ω)) := by
    funext ω
    simp only [X]
    rw [hPadj]
  have hy : (fun ω => inner ℝ y (Y t ω)) = (fun ω => inner ℝ (Q y) (B t ω)) := by
    funext ω
    simp only [Y]
    rw [hQadj]
  rw [hx, hy, hcov, hPQ]
  simp

end GinibrePoincare
