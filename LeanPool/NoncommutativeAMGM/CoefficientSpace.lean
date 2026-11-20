/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.CoefficientEnergy
public import LeanPool.NoncommutativeAMGM.SpectralLower
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.Algebra.Polynomial.Sequence

/-!
# Finite-dimensional coefficient Hilbert spaces

Polynomials of degree less than `L`, with the Euclidean norm of their coefficients.
-/

@[expose] public section

namespace NoncommutativeAMGM

open Polynomial Module
open scoped RealInnerProductSpace

/-- Real polynomials of degree less than `L`, with a separate coefficient norm. -/
noncomputable def CoefficientSpace (L : ℕ) := Polynomial.degreeLT ℝ L

noncomputable instance (L : ℕ) : AddCommGroup (CoefficientSpace L) :=
  inferInstanceAs (AddCommGroup (Polynomial.degreeLT ℝ L))

noncomputable instance (L : ℕ) : Module ℝ (CoefficientSpace L) :=
  inferInstanceAs (Module ℝ (Polynomial.degreeLT ℝ L))

/-- Read a polynomial of degree below `L` as its `L` Euclidean coefficients. -/
noncomputable def coefficientSpaceEquiv (L : ℕ) :
    CoefficientSpace L ≃ₗ[ℝ] EuclideanSpace ℝ (Fin L) :=
  (Polynomial.degreeLTEquiv ℝ L).trans (EuclideanSpace.equiv (Fin L) ℝ).toLinearEquiv.symm

noncomputable instance (L : ℕ) : NormedAddCommGroup (CoefficientSpace L) :=
  NormedAddCommGroup.induced _ _ (coefficientSpaceEquiv L).toAddMonoidHom
    (coefficientSpaceEquiv L).injective

noncomputable instance (L : ℕ) : NormedSpace ℝ (CoefficientSpace L) :=
  NormedSpace.induced ℝ _ _ (coefficientSpaceEquiv L).toLinearMap

noncomputable instance (L : ℕ) : InnerProductSpace ℝ (CoefficientSpace L) :=
  InnerProductSpace.induced (coefficientSpaceEquiv L).toLinearMap

instance (L : ℕ) : FiniteDimensional ℝ (CoefficientSpace L) :=
  inferInstanceAs (FiniteDimensional ℝ (Polynomial.degreeLT ℝ L))

/-- Forget the degree bound. -/
noncomputable def coefficientSpaceVal (L : ℕ) : CoefficientSpace L →ₗ[ℝ] Polynomial ℝ :=
  (Polynomial.degreeLT ℝ L).subtype

theorem coefficientSpace_inner {L : ℕ} (hL : 0 < L) (p q : CoefficientSpace L) :
    ⟪p, q⟫ = realCoefficientInner (coefficientSpaceVal L p) (coefficientSpaceVal L q) := by
  have hp : (coefficientSpaceVal L p).natDegree < L := by
    by_cases hp0 : coefficientSpaceVal L p = 0
    · simpa [hp0] using hL
    · exact (natDegree_lt_iff_degree_lt hp0).mpr (mem_degreeLT.mp p.property)
  rw [realCoefficientInner_eq_sum _ _ hp]
  change inner ℝ (coefficientSpaceEquiv L p) (coefficientSpaceEquiv L q) = _
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  change (∑ i : Fin L, (coefficientSpaceVal L p).coeff i.val *
    (coefficientSpaceVal L q).coeff i.val) = _
  exact Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ (coefficientSpaceVal L p).coeff i * (coefficientSpaceVal L q).coeff i) L

/-- The shifted powers form a polynomial sequence. -/
noncomputable def shiftedPowerSequence : Polynomial.Sequence ℝ where
  elems' i := (X - 1) ^ i
  degree_eq' i := by
    rw [show (X - 1 : Polynomial ℝ) = X - C (1 : ℝ) by simp,
      degree_pow, degree_X_sub_C]
    simp

theorem powerTail_zero_eq_degreeLT (L : ℕ) : powerTail L 0 = Polynomial.degreeLT ℝ L := by
  have hs : {p : Polynomial ℝ | ∃ l : ℕ, 0 ≤ l ∧ l < L ∧ p = (X - 1) ^ l} =
      shiftedPowerSequence '' Set.Iio L := by
    ext p
    constructor
    · rintro ⟨l, _, hl, rfl⟩
      exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, by omega, hl, rfl⟩
  rw [powerTail, hs]
  apply shiftedPowerSequence.span_degreeLT
  intro i _
  have hmon : Monic ((X - 1 : Polynomial ℝ) ^ i) := by
    simpa using (monic_X_sub_C (1 : ℝ)).pow i
  change IsUnit (((X - 1 : Polynomial ℝ) ^ i).leadingCoeff)
  rw [hmon.leadingCoeff]
  exact isUnit_one

/-- Restriction of the concrete coefficient operator to bounded-degree polynomials. -/
noncomputable def boundedCoefficientOperator (L : ℕ) :
    CoefficientSpace L →ₗ[ℝ] CoefficientSpace L :=
  (coefficientOperator L).restrict (fun p hp ↦ by
    change p ∈ Polynomial.degreeLT ℝ L at hp
    change coefficientOperator L p ∈ Polynomial.degreeLT ℝ L
    rw [← powerTail_zero_eq_degreeLT] at hp ⊢
    exact coefficientOperator_preserves_powerTail L 0 p hp)

theorem boundedCoefficientOperator_symmetric {L : ℕ} (hL : 0 < L) :
    (boundedCoefficientOperator L).IsSymmetric := by
  intro p q
  rw [coefficientSpace_inner hL, coefficientSpace_inner hL]
  exact coefficientOperator_symmetric L _ _

theorem powerTail_natDegree_lt {L j : ℕ} (hL : 0 < L) (p : Polynomial ℝ)
    (hp : p ∈ powerTail L j) : p.natDegree < L := by
  have hp0 : p ∈ powerTail L 0 := by
    apply Submodule.span_mono (s := {q : Polynomial ℝ |
      ∃ l : ℕ, j ≤ l ∧ l < L ∧ q = (X - 1) ^ l}) (t := {q : Polynomial ℝ |
      ∃ l : ℕ, 0 ≤ l ∧ l < L ∧ q = (X - 1) ^ l}) ?_ hp
    rintro q ⟨l, _, hlL, rfl⟩
    exact ⟨l, by omega, hlL, rfl⟩
  rw [powerTail_zero_eq_degreeLT] at hp0
  by_cases hpz : p = 0
  · simpa [hpz] using hL
  · exact (natDegree_lt_iff_degree_lt hpz).mpr (mem_degreeLT.mp hp0)

end NoncommutativeAMGM
