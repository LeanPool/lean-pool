/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Module.Rat
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module

/-!
# Rational multiples of an indivisible element of a subgroup

Let `P` be an additive subgroup of a `ℚ`-vector space and `x ∈ P` an element which is not a
proper integer multiple of an element of `P`. Then `q • x ∈ P` exactly when `q` is an integer.

## Main statements

* `AddSubgroup.rat_smul_mem_iff`.
-/

public section

namespace AddSubgroup

/-- If `x ∈ P` is only an integer multiple `m • y` of elements `y ∈ P` with `m` a unit, then
`q • x ∈ P` iff `q` is an integer. -/
theorem rat_smul_mem_iff {V : Type*} [AddCommGroup V] [Module ℚ V] {P : AddSubgroup V} {x : V}
    (hx : x ∈ P) (hx' : ∀ y ∈ P, ∀ m : ℤ, x = m • y → IsUnit m) {q : ℚ} :
    q • x ∈ P ↔ ∃ n : ℤ, q = n := by
  refine ⟨fun hq ↦ ?_, fun ⟨n, hn⟩ ↦ by simpa [hn, Int.cast_smul_eq_zsmul] using P.zsmul_mem hx n⟩
  obtain ⟨u, v, huv⟩ := q.isCoprime_num_den
  have hd := hx' _ (P.add_mem (P.zsmul_mem hq u) (P.zsmul_mem hx v)) q.den <| by
    have h : (u * q.num + v * q.den : ℚ) = 1 := by exact_mod_cast huv
    rw [← q.den_mul_eq_num] at h
    match_scalars
    linarith
  exact ⟨q.num, by simpa [Int.isUnit_iff_natAbs_eq, eq_comm, Rat.den_eq_one_iff] using hd⟩

end AddSubgroup
