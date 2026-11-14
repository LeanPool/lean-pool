/-
Copyright (c) 2026 Lukas Liehr, Mitchell A. Taylor, Peiyang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Liehr, Mitchell A. Taylor, Peiyang Yu
-/
module

public import LeanPool.GrothendieckBessel.Conventions

import Mathlib.Tactic.NormNum

/-!
# Abstract Bessel sequences and their Gram kernels
Adapted for Lean Pool from the Apache-2.0 upstream formalization, with module-system,
Mathlib API, and compilation changes.
-/

@[expose] public section


noncomputable section

open scoped BigOperators ComplexConjugate

namespace GrothendieckBessel

universe u

/-- The paper-convention Gram kernel of an abstract Hilbert-space sequence. -/
def besselGram
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : ℕ → H) : ℕ → ℕ → ℂ :=
  fun j k => inner ℂ (x k) (x j)

/-- Conjugate symmetry of the abstract Gram kernel. -/
theorem besselGram_conj_symm
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : ℕ → H) :
  ∀ j k, besselGram x k j = star (besselGram x j k) := by
  intro j k
  simp [besselGram]

/-- The finite Gram quadratic form is the squared norm of the vector sum. -/
theorem besselGram_quadratic_eq_norm_sq
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : ℕ → H) (F : Finset ℕ) (c : ℕ → ℂ) :
    (F.sum (fun j => F.sum (fun k =>
      c j * star (c k) * besselGram x j k))).re =
      ‖F.sum (fun j => c j • x j)‖ ^ 2 := by
  classical
  have hcomplex :
      F.sum (fun j => F.sum (fun k =>
        c j * star (c k) * besselGram x j k)) =
        inner ℂ (F.sum (fun j => c j • x j))
          (F.sum (fun j => c j • x j)) := by
    simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
    rw [Finset.sum_comm]
    simp [besselGram, mul_assoc, mul_comm, mul_left_comm]
  rw [hcomplex, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- A Bessel sequence with bound one has a finite positive-contraction Gram kernel. -/
theorem besselGram_finite_positive_contraction
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : ℕ → H) (hx : BesselSequenceBoundOne x) :
    FiniteHermitianPositiveContraction (besselGram x) := by
  constructor
  · exact besselGram_conj_symm x
  · intro F c
    rw [besselGram_quadratic_eq_norm_sq x F c]
    exact ⟨sq_nonneg _, hx F c⟩

end GrothendieckBessel
