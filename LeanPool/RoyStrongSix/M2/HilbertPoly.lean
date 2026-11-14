/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module
public import Mathlib.RingTheory.Polynomial.Pochhammer

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.Hilbert

/-!
# The Hilbert polynomial

* `hilb_colon_hom`: for any homogeneous `f ≠ 0` of degree `e`,
  `hilb J (k+e) = hilb (J + (f)) (k+e) + hilb (J : f) k`.
* `evPoly_poly`: an eventually polynomial `ℕ → ℤ` (some `Δⁿ` eventually zero) agrees for large `k`
  with an honest polynomial `P ∈ ℚ[X]`. This is the Gregory–Newton formula.
* `hpoly J`: the Hilbert polynomial of a homogeneous ideal, unique by `poly_unique`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule

namespace StrongSix.M2

variable {K : Type*} [Field K] {m : ℕ}

local notation "A" => MvPolynomial (Fin m) K

/-! ### From eventual polynomiality to a polynomial -/

theorem iter_Δ_zero_from {f : ℕ → ℤ} {N k0 : ℕ} (h : ∀ k ≥ k0, (Δ^[N] f) k = 0) :
    ∀ i, ∀ k ≥ k0, (Δ^[N + i] f) k = 0 := by
  intro i
  induction i with
  | zero => exact h
  | succ i ih =>
    intro k hk
    rw [← add_assoc, Function.iterate_succ_apply']
    change (Δ^[N + i] f) (k + 1) - (Δ^[N + i] f) k = 0
    rw [ih k hk, ih (k + 1) (by omega), sub_zero]

/-- **Gregory–Newton**: an eventually polynomial function is eventually a polynomial. -/
theorem evPoly_poly {f : ℕ → ℤ} (h : EvPoly f) :
    ∃ P : Polynomial ℚ, ∀ᶠ k in Filter.atTop, (f k : ℚ) = P.eval (k : ℚ) := by
  classical
  obtain ⟨N, hN⟩ := h
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp hN
  have hzero : ∀ j, N ≤ j → (Δ^[j] f) k0 = 0 := fun j hj => by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact iter_Δ_zero_from hk0 i k0 le_rfl
  refine ⟨∑ j ∈ Finset.range N, Polynomial.C (((Δ^[j] f) k0 : ℚ) / j.factorial) *
      (descPochhammer ℚ j).comp (Polynomial.X - Polynomial.C (k0 : ℚ)), ?_⟩
  refine Filter.eventually_atTop.mpr ⟨k0, fun k hk => ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  -- Newton's formula
  have hnewton := shift_eq_sum_fwdDiff_iter (h := (1 : ℕ)) f n k0
  rw [smul_eq_mul, mul_one] at hnewton
  have hsum : ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ) * (Δ^[j] f) k0 =
      ∑ j ∈ Finset.range N, (n.choose j : ℤ) * (Δ^[j] f) k0 := by
    have hA : ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ) * (Δ^[j] f) k0 =
        ∑ j ∈ Finset.range (n + 1 + N), (n.choose j : ℤ) * (Δ^[j] f) k0 :=
      Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j _ hj => by
        rw [Finset.mem_range] at hj
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    have hB : ∑ j ∈ Finset.range N, (n.choose j : ℤ) * (Δ^[j] f) k0 =
        ∑ j ∈ Finset.range (n + 1 + N), (n.choose j : ℤ) * (Δ^[j] f) k0 :=
      Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j _ hj => by
        rw [Finset.mem_range] at hj
        rw [hzero j (by omega), mul_zero]
    rw [hA, hB]
  simp only [nsmul_eq_mul] at hnewton
  rw [hnewton, hsum]
  push_cast
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, show ((k0 : ℚ) + (n : ℚ) - k0) = ((n : ℕ) : ℚ) by ring,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  have : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  push_cast
  field_simp

/-- Two polynomials eventually equal on `ℕ` are equal. -/
theorem poly_unique {P Q : Polynomial ℚ} {f : ℕ → ℤ}
    (hP : ∀ᶠ k in Filter.atTop, (f k : ℚ) = P.eval (k : ℚ))
    (hQ : ∀ᶠ k in Filter.atTop, (f k : ℚ) = Q.eval (k : ℚ)) : P = Q := by
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp (hP.and hQ)
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((k0 + n : ℕ) : ℚ))
  · intro a b h; simpa using h
  · intro n
    have := hk0 (k0 + n) (by omega)
    change Polynomial.eval _ P = Polynomial.eval _ Q
    rw [← this.1, ← this.2]

/-- **The Hilbert polynomial** of a homogeneous ideal. -/
noncomputable def hpoly (J : Ideal A) (hJ : HomIdeal J) : Polynomial ℚ :=
  Classical.choose (evPoly_poly (hilb_evPoly J hJ))

theorem hpoly_spec (J : Ideal A) (hJ : HomIdeal J) :
    ∀ᶠ k in Filter.atTop, (hilb J k : ℚ) = (hpoly J hJ).eval (k : ℚ) := by
  filter_upwards [Classical.choose_spec (evPoly_poly (hilb_evPoly J hJ))] with k hk
  rw [hpoly, ← hk]
  simp

end StrongSix.M2

end LeanPool
