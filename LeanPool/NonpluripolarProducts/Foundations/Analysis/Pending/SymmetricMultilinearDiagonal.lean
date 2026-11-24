/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.LinearAlgebra.Multilinear.Basic
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PolarizationAlgebra

/-!
# A symmetric multilinear map is determined by its diagonal

Polarization in the form needed to compare a mixed object with its pure specialization:
if two symmetric `ℝ`-multilinear functions of `n` vector arguments agree whenever all
`n` arguments are equal, they agree everywhere.

The combinatorial core is `Pending.PolarizationAlgebra.sum_powerset_signed_eq_factorial_mul`
(inclusion–exclusion over the images of the maps `Fin n → Fin n`); what is added here is
the multilinear expansion `M (∑_{j ∈ S} x_j, …, ∑_{j ∈ S} x_j) = ∑_{g : Fin n → S} M (x ∘ g)`
and the symmetry step that collapses the bijective terms.

No scalar is inverted apart from `n!`, so the statement holds in every dimension,
including `n = 0`, where both sides are the empty product.
-/

@[expose] public section

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.SymmetricMultilinearDiagonal

open Finset

variable {V : Type*} [AddCommMonoid V] [Module ℝ V] {n : ℕ}

/-- A multilinear map of `n` arguments is **symmetric** when permuting the arguments does
not change its value. -/
def IsSymmetricMultilinear (M : MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => V) ℝ) : Prop :=
  ∀ (x : Fin n → V) (τ : Equiv.Perm (Fin n)), M (fun i => x (τ i)) = M x

/-- Expanding a diagonal value of a multilinear map over a finite sum. -/
theorem map_diagonal_sum (M : MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => V) ℝ)
    (x : Fin n → V) (S : Finset (Fin n)) :
    M (fun _ => ∑ j ∈ S, x j) =
      ∑ g : Fin n → Fin n with (∀ j, g j ∈ S), M (fun i => x (g i)) := by
  classical
  rw [M.map_sum_finset (fun _ (j : Fin n) => x j) (fun _ => S)]
  refine Finset.sum_congr ?_ fun g _ => rfl
  ext g
  simp [Fintype.mem_piFinset]

/-- **The polarization identity.**  For a symmetric multilinear `M`, the signed sum of the
diagonal values over all subsets recovers `n!` times the value at an arbitrary argument
tuple. -/
theorem sum_powerset_signed_diagonal (M : MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => V) ℝ)
    (hM : IsSymmetricMultilinear M) (x : Fin n → V) :
    ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) * M (fun _ => ∑ j ∈ S, x j) =
      (n.factorial : ℝ) * M x := by
  classical
  have hd : ∀ σ : Equiv.Perm (Fin n),
      (fun g : Fin n → Fin n => M (fun i => x (g i))) σ =
        (fun g : Fin n → Fin n => M (fun i => x (g i))) id := by
    intro σ
    simpa using hM x σ
  have := PolarizationAlgebra.sum_powerset_signed_eq_factorial_mul
    (fun g : Fin n → Fin n => M (fun i => x (g i))) hd
  simp only [map_diagonal_sum M x]
  simpa using this

/-- **A symmetric multilinear map is determined by its diagonal.** -/
theorem eq_of_diagonal_eq (M N : MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => V) ℝ)
    (hM : IsSymmetricMultilinear M) (hN : IsSymmetricMultilinear N)
    (hdiag : ∀ y : V, M (fun _ => y) = N (fun _ => y)) (x : Fin n → V) :
    M x = N x := by
  have h1 := sum_powerset_signed_diagonal M hM x
  have h2 := sum_powerset_signed_diagonal N hN x
  have hsum : ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) * M (fun _ => ∑ j ∈ S, x j) =
      ∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) * N (fun _ => ∑ j ∈ S, x j) := by
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hdiag]
  rw [h1, h2] at hsum
  have hfac : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  exact mul_left_cancel₀ hfac hsum

end SGPT.Foundations.Analysis.Pending.SymmetricMultilinearDiagonal
