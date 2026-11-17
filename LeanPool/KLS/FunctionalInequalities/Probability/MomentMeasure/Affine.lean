/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.Affine
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Integrability
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Basic
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Exponential mass, integrals and the CEK functional under affine subtraction

Exact formulas for the conjugate mass, the integral and the extended-logarithm functional after
subtracting an affine
function: a finite-measure correction in general, and invariance for a centered probability measure
with finite first
moment; the normalization producing a nonnegative potential vanishing at the origin.

Supporting infrastructure for Cordero-Erausquin–Klartag, Proposition 12.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis

section
-- Mass of the Legendre transform under affine subtraction.

open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- The actual translated conjugate mass for a right-translation-invariant
background measure, retaining both zero and infinite values. -/
theorem mass_legendre_affineSubtract (dx : Measure E) [Measure.IsAddRightInvariant dx]
    (f : E → EReal) (a : E) (b : ℝ) :
    mass dx (legendre (affineSubtract f a b)) =
      EReal.exp ((-b : ℝ) : EReal) * mass dx (legendre f) := by
  have hneg (x : E) :
      -(legendre f (x + a) + (b : EReal)) =
        -legendre f (x + a) + ((-b : ℝ) : EReal) := by
    simpa only [sub_eq_add_neg, EReal.coe_neg] using
      (EReal.neg_add (.inr (EReal.coe_ne_top b)) (.inr (EReal.coe_ne_bot b)))
  unfold mass density
  simp_rw [legendre_affineSubtract, hneg, EReal.exp_add]
  rw [lintegral_mul_const' _ _ (by simp)]
  rw [lintegral_add_right_eq_self (μ := dx) (fun y : E => EReal.exp (-legendre f y)) a]
  exact mul_comm _ _
/-- Euclidean volume specialization used in the pinned source, including dimension0. -/
theorem mass_legendre_affineSubtract_volume {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EReal) (a : EuclideanSpace ℝ (Fin n)) (b : ℝ) :
    mass volume (legendre (affineSubtract f a b)) =
      EReal.exp ((-b : ℝ) : EReal) * mass volume (legendre f) :=
  mass_legendre_affineSubtract volume f a b

end

section
-- Integrability and integrals under affine subtraction.

open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

section StructuredSpace

variable [IsFiniteMeasure μ]
section AffineMoments

omit [BorelSpace E]
/-- The actual affine perturbation is admissible under the input first moment.
Neither output integrability nor a supporting affine plane is assumed. -/
theorem affineSubtract_potentialIntegrable
    (f : E → EReal) (a : E) (b : ℝ) (hf : PotentialIntegrable f μ)
    (hfirst : Integrable (fun x : E => x) μ) :
    PotentialIntegrable (affineSubtract f a b) μ := by
  have hlin : Integrable (fun x => inner ℝ a x) μ := (innerSL ℝ a).integrable_comp hfirst
  have heq : (fun x => (affineSubtract f a b x).toReal) =ᵐ[μ]
      (fun x => (f x).toReal - (inner ℝ a x + b)) := by
    filter_upwards [hf.2.1] with x hx
    exact affineSubtract_toReal_of_finite f a b x hx (hf.1 x)
  refine ⟨?_, ?_, ?_⟩
  · intro x
    change f x - ((inner ℝ a x + b : ℝ) : EReal) ≠ ⊥
    by_cases ht : f x = ⊤
    · rw [ht, EReal.top_sub_coe]
      exact top_ne_bot
    · rw [← EReal.coe_toReal ht (hf.1 x), ← EReal.coe_sub]
      exact EReal.coe_ne_bot _
  · filter_upwards [hf.2.1] with x hx
    change f x - ((inner ℝ a x + b : ℝ) : EReal) ≠ ⊤
    rw [← EReal.coe_toReal hx (hf.1 x), ← EReal.coe_sub]
    exact EReal.coe_ne_top _
  · exact (hf.2.2.sub (hlin.add (integrable_const b))).congr (Filter.EventuallyEq.symm heq)
/-- The actual integral formula retains total mass for a general finite measure.
This is not asserted to be invariant under a constant shift at arbitrary mass. -/
theorem integral_affineSubtract
    (f : E → EReal) (a : E) (b : ℝ) (hf : PotentialIntegrable f μ)
    (hfirst : Integrable (fun x : E => x) μ) :
    (∫ x, (affineSubtract f a b x).toReal ∂μ) =
      (∫ x, (f x).toReal ∂μ) - (∫ x, inner ℝ a x ∂μ) - (μ Set.univ).toReal * b := by
  have hlin : Integrable (fun x => inner ℝ a x) μ := (innerSL ℝ a).integrable_comp hfirst
  have heq : (fun x => (affineSubtract f a b x).toReal) =ᵐ[μ]
      (fun x => (f x).toReal - (inner ℝ a x + b)) := by
    filter_upwards [hf.2.1] with x hx
    exact affineSubtract_toReal_of_finite f a b x hx (hf.1 x)
  have hAff : Integrable (fun x => inner ℝ a x + b) μ := hlin.add (integrable_const b)
  have hsub : (∫ x, (f x).toReal - (inner ℝ a x + b) ∂μ) =
      (∫ x, (f x).toReal ∂μ) - ∫ x, inner ℝ a x + b ∂μ := integral_sub hf.2.2 hAff
  have hadd : (∫ x, inner ℝ a x + b ∂μ) = (∫ x, inner ℝ a x ∂μ) + ∫ _ : E, b ∂μ :=
    integral_add hlin (integrable_const b)
  rw [integral_congr_ae heq, hsub, hadd, integral_const]
  simp only [smul_eq_mul, measureReal_def]
  ring

end AffineMoments

end StructuredSpace
omit [BorelSpace E] in
/-- On a centered probability measure, the linear integral vanishes and the
constant contributes exactly its value, rather than total-mass times its value. -/
theorem integral_affineSubtract_of_probability [CompleteSpace E] [IsProbabilityMeasure μ]
    (f : E → EReal) (a : E) (b : ℝ) (hf : PotentialIntegrable f μ)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : (∫ x, x ∂μ) = 0) :
    (∫ x, (affineSubtract f a b x).toReal ∂μ) = (∫ x, (f x).toReal ∂μ) - b := by
  have hlin : (∫ x, inner ℝ a x ∂μ) = 0 := by
    simpa only [innerSL_apply_apply, hbar, map_zero] using (innerSL ℝ a).integral_comp_comm hfirst
  simpa [hlin] using integral_affineSubtract f a b hf hfirst
/-- Exact extended logarithm correction for the actual conjugate mass. -/
theorem log_mass_legendre_affineSubtract (dx : Measure E) [Measure.IsAddRightInvariant dx]
    (f : E → EReal) (a : E) (b : ℝ) :
    ENNReal.log (mass dx (legendre (affineSubtract f a b))) =
      ENNReal.log (mass dx (legendre f)) - (b : EReal) := by
  rw [mass_legendre_affineSubtract, ENNReal.log_mul_add, EReal.log_exp, EReal.coe_neg]
  rw [add_comm]
  rfl
/-- CEK's functional is invariant under the actual affine subtraction for a
centered probability measure, retaining zero/infinite exponential mass. -/
theorem variationalFunctional_affineSubtract [CompleteSpace E] [IsProbabilityMeasure μ]
    (dx : Measure E) [Measure.IsAddRightInvariant dx]
    (f : E → EReal) (a : E) (b : ℝ) (hf : PotentialIntegrable f μ)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : (∫ x, x ∂μ) = 0) :
    variationalFunctional dx μ (affineSubtract f a b) = variationalFunctional dx μ f := by
  unfold variationalFunctional
  rw [log_mass_legendre_affineSubtract, integral_affineSubtract_of_probability f a b hf hfirst hbar]
  exact sub_coe_cancel_shift _ _ b
/-- Euclidean volume specialization of the source normalization identity. -/
theorem variationalFunctional_affineSubtract_volume {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (f : EuclideanSpace ℝ (Fin n) → EReal) (a : EuclideanSpace ℝ (Fin n)) (b : ℝ)
    (hf : PotentialIntegrable f μ) (hfirst : Integrable (fun x => x) μ)
    (hbar : (∫ x, x ∂μ) = 0) :
    variationalFunctional volume μ (affineSubtract f a b) = variationalFunctional volume μ f :=
  variationalFunctional_affineSubtract volume f a b hf hfirst hbar

end

section
-- Normalizing a potential to vanish at the origin under a probability law.

open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
/-- The actual source affine normalization preserves admissibility and the
variational value under the source probability, first-moment and centering data. -/
theorem exists_origin_zero_affine_of_probability [FiniteDimensional ℝ E] [IsProbabilityMeasure μ]
    (dx : Measure E) [Measure.IsAddRightInvariant dx]
    (f : E → EReal) (hf : PotentialIntegrable f μ) (hconv : ConvexPotential f)
    (h0 : (0 : E) ∈ interior {x | f x ≠ ⊤})
    (hfirst : Integrable (fun x : E => x) μ) (hbar : (∫ x, x ∂μ) = 0) :
    ∃ a : E, let g := affineSubtract f a (f 0).toReal
      ConvexPotential g ∧ PotentialIntegrable g μ ∧ (∀ x, 0 ≤ g x) ∧ g 0 = 0 ∧
        variationalFunctional dx μ g = variationalFunctional dx μ f := by
  obtain ⟨a, hc, hnn, hg0⟩ := exists_nonnegative_origin_zero_affine f hconv h0
  refine ⟨a, hc, affineSubtract_potentialIntegrable f a (f 0).toReal hf hfirst, hnn, hg0, ?_⟩
  exact variationalFunctional_affineSubtract dx f a (f 0).toReal hf hfirst hbar

end

end FunctionalInequalities.Probability.MomentMeasure
