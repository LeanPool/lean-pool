/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.DensityExpectationContinuity

/-!
# Extending genuine density factorization through linear spans and closures

These lemmas extend an established equality of actual joint expectations.
They do not infer independence from commutation. The norm closure step
uses the actual bounded functional; the strong limit step uses its proved
bounded strong continuity for an arbitrary positive trace-class density.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open Filter Topology

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem linearFunctional_factorization_span
    (φ : (E →L[ℂ] E) →ₗ[ℂ] ℂ) (S T : Set (E →L[ℂ] E))
    (h : ∀ A ∈ S, ∀ B ∈ T, φ (A * B) = φ A * φ B)
    {A B : E →L[ℂ] E} (hA : A ∈ Submodule.span ℂ S)
    (hB : B ∈ Submodule.span ℂ T) : φ (A * B) = φ A * φ B := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    induction hB using Submodule.span_induction with
    | mem B hB => exact h A hA B hB
    | zero => simp
    | add B C hB hC ihB ihC => simp only [mul_add, map_add, ihB, ihC]
    | smul c B hB ih =>
      simp only [mul_smul_comm, map_smul, smul_eq_mul, ih]
      ring
  | zero => simp
  | add A C hA hC ihA ihC => simp only [add_mul, map_add, ihA, ihC]
  | smul c A hA ih =>
    simp only [smul_mul_assoc, map_smul, smul_eq_mul, ih]
    ring

theorem continuousLinearFunctional_factorization_closure
    (φ : (E →L[ℂ] E) →L[ℂ] ℂ) (S T : Set (E →L[ℂ] E))
    (h : ∀ A ∈ S, ∀ B ∈ T, φ (A * B) = φ A * φ B)
    {A B : E →L[ℂ] E} (hA : A ∈ closure S) (hB : B ∈ closure T) :
    φ (A * B) = φ A * φ B := by
  have hleft (B : E →L[ℂ] E) (hB : B ∈ T) : ∀ A ∈ closure S,
      φ (A * B) = φ A * φ B := by
    have hs : closure S ⊆ {P | φ (P * B) = φ P * φ B} :=
      closure_minimal (fun P hP => h P hP B hB)
        (isClosed_eq (φ.continuous.comp (continuous_id.mul_const B))
          (φ.continuous.mul_const (φ B)))
    exact fun P hP => hs hP
  have hright : closure T ⊆ {B | φ (A * B) = φ A * φ B} := by
    apply closure_minimal (fun B hB => hleft B hB A hA)
    exact isClosed_eq (φ.continuous.comp (continuous_const.mul continuous_id))
      (continuous_const.mul φ.continuous)
  exact hright hB

theorem densityExpectation_factorization_of_strong_left (b : HilbertBasis ι ℂ E)
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass ρ)
    {α : Type*} {l : Filter α} [l.NeBot] {As : α → E →L[ℂ] E}
    {A B : E →L[ℂ] E} {C : ℝ}
    (hstrong : ∀ x, Tendsto (fun i => As i x) l (𝓝 (A x)))
    (hbounded : ∀ᶠ i in l, ‖As i‖ ≤ C)
    (hfactor : ∀ᶠ i in l, densityExpectation b ρ (As i * B) =
      densityExpectation b ρ (As i) * densityExpectation b ρ B) :
    densityExpectation b ρ (A * B) = densityExpectation b ρ A * densityExpectation b ρ B := by
  apply tendsto_nhds_unique
    (tendsto_densityExpectation_mul_right_of_strong b hρ B hstrong hbounded)
  exact ((tendsto_densityExpectation_of_strong b hρ hstrong hbounded).mul
    tendsto_const_nhds).congr' (Filter.EventuallyEq.symm hfactor)

theorem densityExpectation_factorization_of_strong_right (b : HilbertBasis ι ℂ E)
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass ρ)
    {α : Type*} {l : Filter α} [l.NeBot] {Bs : α → E →L[ℂ] E}
    {A B : E →L[ℂ] E} {C : ℝ}
    (hstrong : ∀ x, Tendsto (fun i => Bs i x) l (𝓝 (B x)))
    (hbounded : ∀ᶠ i in l, ‖Bs i‖ ≤ C)
    (hfactor : ∀ᶠ i in l, densityExpectation b ρ (A * Bs i) =
      densityExpectation b ρ A * densityExpectation b ρ (Bs i)) :
    densityExpectation b ρ (A * B) = densityExpectation b ρ A * densityExpectation b ρ B := by
  apply tendsto_nhds_unique
    (tendsto_densityExpectation_mul_left_of_strong b hρ A hstrong hbounded)
  exact (tendsto_const_nhds.mul
    (tendsto_densityExpectation_of_strong b hρ hstrong hbounded)).congr'
      (Filter.EventuallyEq.symm hfactor)

end VacuumBellSeparation.Gaussian
