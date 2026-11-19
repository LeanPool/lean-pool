/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# A nonzero integer as a power of `p` times a unit at `p`, and a square of this form

Candidates for `Mathlib.NumberTheory.Padics.PadicVal.Basic`: a nonzero integer as the power of `p`
of its valuation times an integer prime to `p`, for any `p ≠ 1`
(`Int.exists_eq_pow_padicValInt_mul`), the `p`-adic valuation of the integer `p ^ k` for any `p > 1`
(`padicValInt_base_pow`, the integer form of `padicValNat_base_pow`), and a square that is a power
of `p` times a unit at `p`, whose exponent is even and whose unit part is a square
(`Int.even_and_isSquare_of_sq_eq_pow_mul`), also for a square that is a sum whose terms but one are
divisible by a higher power of `p` (`Int.even_and_exists_isSquare_add_of_sq_eq_sum`).

## Main statements

* `Int.exists_eq_pow_padicValInt_mul`: a nonzero integer is `p ^ v_p(n)` times an integer prime to
  `p`, for `p ≠ 1`.
* `padicValInt_base_pow`: `v_p(p ^ k) = k` for the integer `p ^ k` and `p > 1`.
* `Int.even_and_isSquare_of_sq_eq_pow_mul`: `y ^ 2 = p ^ v u` with `p ∤ u` makes `v` even and `u` a
  square.
* `Int.even_and_exists_isSquare_add_of_sq_eq_sum`: a square sum with one term `p ^ v u` of least
  valuation, `p ∤ u`, makes `v` even and `u + p t` a square for some `t`.
-/

@[expose] public section

/-- A nonzero integer is `p ^ v_p(n)` times an integer prime to `p`, for any `p ≠ 1`, since the
multiplicity of `p` in `n` is finite (`FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd`). -/
theorem Int.exists_eq_pow_padicValInt_mul {p : ℕ} (hp : p ≠ 1) {n : ℤ} (hn : n ≠ 0) :
    ∃ r, n = (p : ℤ) ^ padicValInt p n * r ∧ ¬(p : ℤ) ∣ r := by
  rw [padicValInt.of_ne_one_ne_zero]
  exact (Int.finiteMultiplicity_iff.mpr ⟨by simpa using hp, hn⟩).exists_eq_pow_mul_and_not_dvd

theorem padicValInt_base_pow {p : ℕ} (hp : 1 < p) (k : ℕ) : padicValInt p ((p : ℤ) ^ k) = k := by
  rw [← Nat.cast_pow, padicValInt.of_nat, padicValNat_base_pow hp]

/-- **A square with a known power of `p`.** If `y ^ 2 = p ^ v u` with `p ∤ u`, then `v` is even, by
the valuations at `p`, and `u` is the square of `y / p ^ (v / 2)`. -/
theorem Int.even_and_isSquare_of_sq_eq_pow_mul {p : ℕ} [hp : Fact p.Prime] {y u : ℤ} {v : ℕ}
    (h : y ^ 2 = (p : ℤ) ^ v * u) (hu : ¬(p : ℤ) ∣ u) : Even v ∧ IsSquare u := by
  have hu0 : u ≠ 0 := fun h0 ↦ hu (h0 ▸ dvd_zero _)
  have hp0 : (p : ℤ) ≠ 0 := mod_cast hp.out.ne_zero
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (pow_ne_zero v hp0) hu0 (by simpa using h.symm)
  have hval := congr(padicValInt p $h)
  rw [sq, padicValInt.mul hy0 hy0, padicValInt.mul (pow_ne_zero _ hp0) hu0,
    padicValInt.eq_zero_of_not_dvd hu, padicValInt_base_pow hp.out.one_lt] at hval
  obtain ⟨k, rfl⟩ : Even v := ⟨padicValInt p y, by lia⟩
  refine ⟨⟨k, rfl⟩, ?_⟩
  obtain ⟨z, rfl⟩ : (p : ℤ) ^ k ∣ y :=
    (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨u, by rw [h, ← pow_mul, Nat.mul_comm, two_mul]⟩
  refine ⟨z, (mul_left_cancel₀ (pow_ne_zero (k + k) hp0) ?_).symm⟩
  rw [← h, pow_add]
  ring

/-- **A square sum with one term of least valuation.** If `y ^ 2 = ∑ i ∈ s, f i`, where
`f j = p ^ v u` with `p ∤ u` and `p ^ (v + 1)` divides every other term, then `v` is even and
`u + p t` is a square for some `t`, so that `u` is a square modulo `p`. -/
theorem Int.even_and_exists_isSquare_add_of_sq_eq_sum {ι : Type*} {s : Finset ι} {f : ι → ℤ}
    {p : ℕ} [Fact p.Prime] {y u : ℤ} {v : ℕ} {j : ι} (hy : y ^ 2 = ∑ i ∈ s, f i) (hj : j ∈ s)
    (hfj : f j = (p : ℤ) ^ v * u) (hu : ¬(p : ℤ) ∣ u)
    (h : ∀ i ∈ s, i ≠ j → (p : ℤ) ^ (v + 1) ∣ f i) : Even v ∧ ∃ t, IsSquare (u + p * t) := by
  classical
  obtain ⟨t, ht⟩ : (p : ℤ) ^ (v + 1) ∣ ∑ i ∈ s.erase j, f i :=
    Finset.dvd_sum fun i hi ↦ h i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
  have hsum : y ^ 2 = (p : ℤ) ^ v * (u + p * t) := by
    rw [hy, ← Finset.add_sum_erase s f hj, hfj, ht, pow_succ]
    ring
  obtain ⟨hv, hsq⟩ := Int.even_and_isSquare_of_sq_eq_pow_mul hsum
    (by rwa [dvd_add_left (dvd_mul_right _ _)])
  exact ⟨hv, t, hsq⟩

end
