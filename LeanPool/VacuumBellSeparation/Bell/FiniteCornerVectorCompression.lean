/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.FiniteVectorDomination
public import LeanPool.VacuumBellSeparation.Bell.NormalFunctionalVectorCornerCover
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
Finite compression keeps all cross terms. Its positive expectation is at
most card(ι) times the diagonal expectation sum. The actual finite Hilbert
amplification then represents the full compressed functional as a finite
positive vector sum on original H. Empty families are included.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped ComplexOrder InnerProductSpace BigOperators

section CStar
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The exact positive quadratic form, in the genuine GNS Hilbert space. -/
theorem positiveFunctional_conjugate_eq_gns_norm_sq (φ : A →ₚ[ℂ] ℂ)
    (a : A) (ha : 0 ≤ a) (x : A) :
    (φ (star x * a * x)).re =
      ‖φ.gnsStarAlgHom (CFC.sqrt a * x) (gnsUnitVector φ)‖ ^ 2 := by
  have hm : star (CFC.sqrt a * x) * (CFC.sqrt a * x) = star x * a * x := by
    rw [star_mul, (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq]
    calc
      _ = star x * (CFC.sqrt a * CFC.sqrt a) * x := by noncomm_ring
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self a ha]
  have h := congrArg Complex.re (gns_apply_unitVector_norm_sq φ (CFC.sqrt a * x))
  simpa only [Complex.ofReal_re, hm] using h.symm

/-- All off-diagonal terms of the finite sum are bounded, not removed. -/
theorem positiveFunctional_conjugate_sum_le_card (φ : A →ₚ[ℂ] ℂ)
    {ι : Type*} [Fintype ι] (P : ι → A) (a : A) (ha : 0 ≤ a) :
    (φ (star (∑ i, P i) * a * ∑ i, P i)).re ≤
      (Fintype.card ι : ℝ) * ∑ i, (φ (star (P i) * a * P i)).re := by
  classical
  let v : ι → φ.GNS := fun i => φ.gnsStarAlgHom (CFC.sqrt a * P i) (gnsUnitVector φ)
  have hv : φ.gnsStarAlgHom (CFC.sqrt a * ∑ i, P i) (gnsUnitVector φ) = ∑ i, v i := by
    simp only [v, Finset.mul_sum, map_sum, sum_apply]
  rw [positiveFunctional_conjugate_eq_gns_norm_sq φ a ha, hv]
  calc
    ‖∑ i, v i‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ => norm_nonneg _)).mpr
        (norm_sum_le _ _)
    _ ≤ (Fintype.card ι : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one] using
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1 : ℝ)) (fun i => ‖v i‖)
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (positiveFunctional_conjugate_eq_gns_norm_sq φ a ha (P i)).symm

end CStar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A finite family of vector-realized corners gives a vector-sum realization
of the FULL compression, even when its cross expectations are nonzero. -/
theorem exists_finite_vector_sum_compression (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) {ι : Type*} [Fintype ι]
    (P : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (P i))
    (ξ : ι → H)
    (hξ : ∀ i (a : M.toStarSubalgebra), vectorFunctional M (ξ i) a = φ (P i * a * P i)) :
    ∃ ζ : ι → H, compressionFunctional φ (∑ i, P i) = finiteVectorFunctional M ζ := by
  classical
  apply exists_finite_vector_sum_of_domination M _ ξ (Fintype.card ι) (by positivity)
  intro a ha
  rw [Complex.le_def]
  refine ⟨?_, ?_⟩
  · have hdiag : ∑ i, (φ (star (P i) * a * P i)).re =
        (finiteVectorFunctional M ξ a).re := by
      rw [finiteVectorFunctional_apply]
      change _ = Complex.reCLM (∑ i, inner ℂ (ξ i) ((a : H →L[ℂ] H) (ξ i)))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(hp i).isSelfAdjoint.star_eq, ← hξ i a]
      rfl
    simpa only [compressionFunctional_apply, Complex.smul_re, smul_eq_mul, hdiag] using
      positiveFunctional_conjugate_sum_le_card φ P a ha
  · have hl := (Complex.nonneg_iff.mp ((compressionFunctional φ (∑ i, P i)).map_nonneg ha)).2
    have hr := (Complex.nonneg_iff.mp ((finiteVectorFunctional M ξ).map_nonneg ha)).2
    simp only [Complex.smul_im, smul_eq_mul, ← hr, mul_zero]
    exact hl.symm

end VacuumBellSeparation.Bipartite
