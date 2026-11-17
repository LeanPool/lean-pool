/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Partial sums of a non-principal Dirichlet character

`‖∑_{k=1}^{M} χ k‖ ≤ N` for a non-principal character `χ` modulo `N`.

Newer Tau Ceti also provides `DirichletCharacter.norm_sum_Icc_le_level`. Its module is
absent from the pool's pinned Tau Ceti revision `4705013d2da8bac010289af92000f4a5b8ffca00`.
These independent upstream proofs supply prerequisites for Siegel's uniform lower bound
on that dependency.
-/

@[expose] public section

open Finset

namespace SiegelThmLib

variable {N : ℕ} [NeZero N]

/-- A sum over `range N` of a function of the residue class is the sum over `ZMod N`. -/
lemma sum_range_natCast_eq_sum_univ (g : ZMod N → ℂ) :
    ∑ k ∈ range N, g (k : ZMod N) = ∑ x : ZMod N, g x := by
  refine Finset.sum_nbij' (fun k => (k : ZMod N)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro k _; exact Finset.mem_univ _
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro k hk; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hk)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro k _; rfl

/-- `N` consecutive values of a non-principal character sum to zero. -/
lemma sum_range_shift_eq_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (a : ℕ) :
    ∑ k ∈ range N, χ ((a + k : ℕ) : ZMod N) = 0 := by
  have h1 : ∑ k ∈ range N, χ ((a + k : ℕ) : ZMod N) =
      ∑ k ∈ range N, (fun x : ZMod N => χ ((a : ZMod N) + x)) (k : ZMod N) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Nat.cast_add]
  exact h1.trans ((sum_range_natCast_eq_sum_univ (fun x : ZMod N => χ ((a : ZMod N) + x))).trans
    ((Equiv.sum_comp (Equiv.addLeft (a : ZMod N)) (fun x => χ x)).trans
      (MulChar.sum_eq_zero_of_ne_one hχ)))

omit [NeZero N] in
/-- Partial sums as a sum over `range`. -/
lemma sum_Icc_eq_sum_range (χ : DirichletCharacter ℂ N) (M : ℕ) :
    ∑ k ∈ Icc 1 M, χ k = ∑ k ∈ range M, χ ((k + 1 : ℕ) : ZMod N) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma norm_sum_range_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (M : ℕ) :
    ‖∑ k ∈ range M, χ ((k + 1 : ℕ) : ZMod N)‖ ≤ N := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    by_cases hM : M < N
    · calc ‖∑ k ∈ range M, χ ((k + 1 : ℕ) : ZMod N)‖
          ≤ ∑ k ∈ range M, ‖χ ((k + 1 : ℕ) : ZMod N)‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ range M, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => DirichletCharacter.norm_le_one χ _
        _ = M := by simp
        _ ≤ N := by exact_mod_cast hM.le
    · obtain ⟨L, rfl⟩ : ∃ L, M = L + N := ⟨M - N, by omega⟩
      rw [Finset.sum_range_add]
      have h0 : ∑ k ∈ range N, χ ((L + k + 1 : ℕ) : ZMod N) = 0 := by
        have := sum_range_shift_eq_zero hχ (L + 1)
        simpa [add_assoc, add_comm, add_left_comm] using this
      rw [h0, add_zero]
      exact ih L (by have := NeZero.pos N; omega)

/-- Partial sums of a non-principal character are bounded by the modulus. -/
theorem norm_sum_Icc_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (M : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 M, χ k‖ ≤ N := by
  rw [sum_Icc_eq_sum_range]
  exact norm_sum_range_le hχ M

omit [NeZero N] in
/-- Values of a real (quadratic) character. -/
lemma val_cases {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) (a : ZMod N) :
    χ a = 0 ∨ χ a = 1 ∨ χ a = -1 :=
  MulChar.isQuadratic_iff_sq_eq_one.mpr hχ a

omit [NeZero N] in
/-- A real character takes real values. -/
lemma val_eq_ofReal_re {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) (a : ZMod N) :
    χ a = ((χ a).re : ℂ) := by
  rcases val_cases hχ a with h | h | h <;> simp [h]

end SiegelThmLib
