/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
import LeanPool.CCDN.ForMathlib.MvPolynomialDerivative

/-!
# Characteristic zero or larger than a bound

`CharZeroOrGT R n` says that the positive natural numbers up to `n` are nonzero in `R`. For a
field this means that the characteristic is zero or larger than `n`. Results that hold both in
characteristic zero and in characteristic `p > n` are stated once under this hypothesis.

## Main results

* `CCDN.CharZeroOrGT.of_charZero`, `CCDN.CharZeroOrGT.of_charP`: the two sources of the
  hypothesis.
* `CCDN.CharZeroOrGT.map`: the hypothesis passes to any extension of a field.
* `CCDN.CharZeroOrGT.iff_ringChar`: the characterization by `ringChar`.
-/

@[expose] public section

namespace CCDN

/-- The positive natural numbers up to `n` are nonzero in `R`; for a field, the characteristic
of `R` is zero or larger than `n`. -/
def CharZeroOrGT (R : Type*) [AddMonoidWithOne R] (n : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → m ≤ n → (m : R) ≠ 0

namespace CharZeroOrGT

variable {R S : Type*}

/-- Characteristic zero exceeds every bound. -/
theorem of_charZero [AddMonoidWithOne R] [CharZero R] (n : ℕ) : CharZeroOrGT R n :=
  fun _ hm _ ↦ Nat.cast_ne_zero.mpr hm.ne'

/-- Characteristic `p` exceeds every bound below `p`. -/
theorem of_charP [AddMonoidWithOne R] {p n : ℕ} [CharP R p] (h : n < p) : CharZeroOrGT R n :=
  fun _ hm hmn ↦ CharP.natCast_ne_zero_of_lt R hm.ne' (hmn.trans_lt h)

/-- The hypothesis weakens to any smaller bound. -/
theorem mono [AddMonoidWithOne R] {m n : ℕ} (h : CharZeroOrGT R n) (hmn : m ≤ n) :
    CharZeroOrGT R m :=
  fun k hk hkm ↦ h k hk (hkm.trans hmn)

/-- A positive natural number up to the bound is nonzero. -/
theorem natCast_ne_zero [AddMonoidWithOne R] {m n : ℕ} (h : CharZeroOrGT R n) (hm : m ≠ 0)
    (hmn : m ≤ n) : (m : R) ≠ 0 :=
  h m (Nat.pos_of_ne_zero hm) hmn

/-- The hypothesis passes along a ring homomorphism out of a division ring, such as the
algebra map of a field extension. -/
theorem map [DivisionRing R] [Semiring S] [Nontrivial S] {n : ℕ} (h : CharZeroOrGT R n)
    (φ : R →+* S) : CharZeroOrGT S n :=
  fun m hm hmn ↦ by simpa only [map_natCast] using (map_ne_zero φ).mpr (h m hm hmn)

/-- `CharZeroOrGT R n` says exactly that the characteristic of `R` is zero or exceeds `n`. -/
theorem iff_ringChar [NonAssocSemiring R] {n : ℕ} :
    CharZeroOrGT R n ↔ ringChar R = 0 ∨ n < ringChar R := by
  refine ⟨fun h ↦ ?_, fun h m hm hmn hz ↦ ?_⟩
  · refine (Nat.eq_zero_or_pos (ringChar R)).imp id fun hp ↦ ?_
    by_contra! hle
    exact h _ hp hle (ringChar.Nat.cast_ringChar)
  · have hdvd := (ringChar.spec R m).mp hz
    rcases h with h | h
    · rw [h, zero_dvd_iff] at hdvd
      omega
    · exact absurd (Nat.le_of_dvd hm hdvd) (by omega)

end CharZeroOrGT

end CCDN
