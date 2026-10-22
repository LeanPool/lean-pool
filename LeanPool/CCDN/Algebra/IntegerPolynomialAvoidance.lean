/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Combinatorics.Nullstellensatz

/-! A nonzero polynomial over a characteristic-zero domain has a nonzero value at an integer
point with every coordinate between 0 and its degree. This is the combinatorial
Nullstellensatz `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` on the grid {0,...,D}. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A nonzero polynomial with coordinate degrees at most `D` has a nonzero value on the
integer grid {0,...,D}, in any finite number of variables. Unlike the total-degree version,
the side length does not grow with the number of variables. -/
theorem exists_integer_grid_eval_ne_zero_of_degreeOf
    {R σ : Type*} [CommRing R] [IsDomain R] [CharZero R] [Finite σ]
    (f : MvPolynomial σ R) (hf : f ≠ 0) (D : ℕ) (hdeg : ∀ i, f.degreeOf i ≤ D) :
    ∃ v : σ → ℤ, (∀ i, 0 ≤ v i ∧ v i ≤ D) ∧ eval (fun i => (v i : R)) f ≠ 0 := by
  classical
  by_contra! hn
  let S : Finset R := (Finset.range (D + 1)).image Nat.cast
  have hS : S.card = D + 1 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  refine hf (eq_zero_of_eval_zero_at_prod_finset f (fun _ => S)
    (fun i => hS ▸ Nat.lt_succ_of_le (hdeg i)) fun x hx => ?_)
  choose a ha he using fun i => Finset.mem_image.mp (hx i)
  have hv := hn (fun i => (a i : ℤ)) fun i =>
    ⟨Int.natCast_nonneg _, by exact_mod_cast Finset.mem_range_succ_iff.mp (ha i)⟩
  simpa only [Int.cast_natCast, he] using hv

/-- A nonzero polynomial of total degree at most `A` over a characteristic-zero domain has a
nonzero value on the integer grid {0,...,A}. -/
theorem exists_integer_grid_eval_ne_zero_of_totalDegree
    {R σ : Type*} [CommRing R] [IsDomain R] [CharZero R] [Finite σ]
    (f : MvPolynomial σ R) (hf : f ≠ 0) (A : ℕ) (hd : f.totalDegree ≤ A) :
    ∃ v : σ → ℤ, (∀ i, 0 ≤ v i ∧ v i ≤ A) ∧ eval (fun i => (v i : R)) f ≠ 0 :=
  exists_integer_grid_eval_ne_zero_of_degreeOf f hf A fun i =>
    (degreeOf_le_totalDegree f i).trans hd

/-- The integer case of `exists_integer_grid_eval_ne_zero_of_totalDegree`. The bound is
independent of the number and names of the coordinates. -/
theorem exists_integer_grid_eval_ne_zero {σ : Type*} [Finite σ]
    (f : MvPolynomial σ ℤ) (hf : f ≠ 0) (A : ℕ) (hd : f.totalDegree ≤ A) :
    ∃ v : σ → ℤ, (∀ i, 0 ≤ v i ∧ v i ≤ A) ∧ eval v f ≠ 0 := by
  simpa only [Int.cast_id] using exists_integer_grid_eval_ne_zero_of_totalDegree f hf A hd

end
end CCDN
