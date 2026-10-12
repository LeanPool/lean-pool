/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import LeanPool.LiebThirring.Kinetic.Currying
public import LeanPool.LiebThirring.Kinetic.Permutation

/-!
# Almost-everywhere equality of particle marginals

Particle marginals of an antisymmetric state agree as functions almost everywhere, strengthening
the existing equality of marginal tests.

The density is the particle count times any selected marginal almost everywhere. Selecting `i:
Fin N` already excludes the vacuum.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- Particle marginals of an antisymmetric state agree as functions almost
everywhere, strengthening the existing equality of marginal tests. -/
theorem particle_marginal_eq_ae {N q : ℕ} (ψ : State N q) (hψ : antisymmetric ψ)
    (i j : Fin N) :
    (fun x : Position => ∫⁻ y : OtherConfiguration i,
      (‖ψ (insertParticle i x y)‖₊ : ℝ≥0∞) ^ 2) =ᵐ[volume]
    (fun x : Position => ∫⁻ y : OtherConfiguration j,
      (‖ψ (insertParticle j x y)‖₊ : ℝ≥0∞) ^ 2) := by
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (measurable_particle_marginal ψ i) (measurable_particle_marginal ψ j)
  intro A hA _
  let v : Position → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hv : Measurable v := measurable_const.indicator hA
  have h := (particle_marginal_testing ψ i v hv).trans
    ((particle_marginals_eq ψ hψ i j v).trans
      (particle_marginal_testing ψ j v hv).symm)
  have ht (k : Fin N) :
      (∫⁻ x : Position, v x * ∫⁻ y : OtherConfiguration k,
        (‖ψ (insertParticle k x y)‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x : Position in A, ∫⁻ y : OtherConfiguration k,
        (‖ψ (insertParticle k x y)‖₊ : ℝ≥0∞) ^ 2 := by
    rw [← lintegral_indicator hA]
    apply lintegral_congr
    intro x
    simpa only [one_mul] using
      (Set.indicator_mul_left (i := x) A (fun _ : Position => (1 : ℝ≥0∞))
        (fun z => ∫⁻ y : OtherConfiguration k,
          (‖ψ (insertParticle k z y)‖₊ : ℝ≥0∞) ^ 2)).symm
  rw [ht i, ht j] at h
  exact h

/-- The density is the particle count times any selected marginal almost
everywhere. Selecting `i: Fin N` already excludes the vacuum. -/
theorem density_eq_mul_particle_marginal_ae {N q : ℕ} (ψ : State N q)
    (hψ : antisymmetric ψ) (i : Fin N) :
    density ψ =ᵐ[volume] fun x : Position => (N : ℝ≥0∞) *
      ∫⁻ y : OtherConfiguration i, (‖ψ (insertParticle i x y)‖₊ : ℝ≥0∞) ^ 2 := by
  have h := Filter.eventually_all.mpr (fun j : Fin N => particle_marginal_eq_ae ψ hψ j i)
  filter_upwards [h] with x hx
  simp only [density, hx, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

end LiebThirring

end
