/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Units in a local ring of prescribed residue characteristic

In a local ring `O` whose maximal ideal contains a prime `p` (equivalently, of residue
characteristic `p`), every integer prime to `p` is a unit. Splitting off the `p`-part
accordingly writes a nonzero `n` as `p^{v_p(n)}` times a unit, whence `n ∣ p^n`.

`IsLocalRing.IsUniformizer π p e` packages the situation the `p`-adic analysis of this
development runs in: `π` generates the maximal ideal, `p` is the residue characteristic, and the
absolute ramification index is at most `e`. Its one substantial lemma,
`IsLocalRing.IsUniformizer.exists_pow_eq`, trades a denominator `p ^ v` for a loss of `e·v` in
the `π`-adic order.

Also here, the two directions of the comparison of two elements through their residues: equal
residues from a difference in the maximal ideal, and a unit difference from distinct residues.
-/

@[expose] public section

namespace IsLocalRing

variable {O : Type*} [CommRing O] [IsLocalRing O] {p : ℕ}

/-- Integers prime to `p` are units in a local ring whose maximal ideal contains `p`
(equivalently, of residue characteristic `p`). -/
theorem isUnit_natCast_of_not_dvd (hp : p.Prime) (hpmem : (p : O) ∈ maximalIdeal O) {n : ℕ}
    (hn : ¬ p ∣ n) :
    IsUnit (n : O) := by
  by_contra hu
  have hmem : (n : O) ∈ maximalIdeal O := hu
  obtain ⟨a, b, hab⟩ := (hp.coprime_iff_not_dvd.mpr hn).symm.cast (R := O)
  have h1 : (1 : O) ∈ maximalIdeal O := by
    rw [← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hpmem)
  exact (maximalIdeal.isMaximal O).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

/-- **Factoring a natural number by its `p`-part**: in a local ring whose maximal ideal contains
the prime `p`, the prime-to-`p` part of `n ≠ 0` is a unit. -/
theorem exists_units_natCast_eq (hp : p.Prime) (hpmem : (p : O) ∈ maximalIdeal O) {n : ℕ}
    (hn : n ≠ 0) :
    ∃ u : Oˣ, (n : O) = (p : O) ^ padicValNat p n * u := by
  set v := padicValNat p n
  obtain ⟨c, hc⟩ : p ^ v ∣ n := pow_padicValNat_dvd
  have hnd : ¬ p ∣ c := fun hd ↦ by
    have hdvd : p ^ (v + 1) ∣ n := by
      rw [hc, pow_succ]
      exact mul_dvd_mul_left _ hd
    lia [(Nat.pow_dvd_iff_le_padicValNat hp.ne_one hn).mp hdvd]
  obtain ⟨u, hu⟩ := isUnit_natCast_of_not_dvd hp hpmem hnd
  exact ⟨u, by rw [hu, hc]; push_cast; ring⟩

/-- **Every nonzero natural number divides the like power of `p`** in a local ring whose maximal
ideal contains the prime `p`: `n = p^{v_p(n)}·unit` and `v_p(n) ≤ n`. -/
theorem natCast_dvd_pow_self (hp : p.Prime) (hpmem : (p : O) ∈ maximalIdeal O) {n : ℕ}
    (hn : n ≠ 0) :
    (n : O) ∣ (p : O) ^ n := by
  obtain ⟨u, hu⟩ := exists_units_natCast_eq hp hpmem hn
  rw [hu, u.isUnit.mul_right_dvd]
  exact pow_dvd_pow _ (Nat.padicValNat_le_self n)

/-! ### Uniformizers -/

/-- **A uniformizer, with a bound on the ramification**: `π` generates the maximal ideal of the
local ring `O`, the prime `p` lies in it (so `p` is the residue characteristic), and `p ∣ π ^ e`
(the absolute ramification index is at most `e`). The absolutely unramified case is
`IsUniformizer (p : O) p 1`. -/
structure IsUniformizer (π : O) (p e : ℕ) : Prop where
  /-- `p` is a prime number. -/
  prime : p.Prime
  /-- `π` generates the maximal ideal. -/
  maximalIdeal_eq : maximalIdeal O = Ideal.span {π}
  /-- The residue characteristic is `p`. -/
  natCast_mem : (p : O) ∈ maximalIdeal O
  /-- The absolute ramification index is at most `e`. -/
  natCast_dvd : (p : O) ∣ π ^ e

namespace IsUniformizer

variable {π : O} {e : ℕ} (h : IsUniformizer π p e)
include h

theorem mem : π ∈ maximalIdeal O := h.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π

theorem mem_iff {x : O} : x ∈ maximalIdeal O ↔ π ∣ x := by
  rw [h.maximalIdeal_eq, Ideal.mem_span_singleton]

theorem mem_pow_iff {x : O} {k : ℕ} : x ∈ maximalIdeal O ^ k ↔ π ^ k ∣ x := by
  rw [h.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- A uniformizer detects units: `x` is a unit exactly when `π` does not divide it. -/
theorem isUnit_iff_not_dvd {x : O} : IsUnit x ↔ ¬ π ∣ x := by
  rw [← h.mem_iff]
  exact notMem_maximalIdeal.symm

theorem ne_zero_of_natCast_ne_zero (hp0 : (p : O) ≠ 0) : π ≠ 0 := fun h0 ↦ hp0 <| by
  simpa [h0] using h.mem_iff.mp h.natCast_mem

theorem ne_zero [CharZero O] : π ≠ 0 :=
  h.ne_zero_of_natCast_ne_zero (Nat.cast_ne_zero.mpr h.prime.ne_zero)

/-- A uniformizer is nonzero when the fraction field has characteristic zero (`ne_zero` asks
this of `O` itself): `π` divides the residue characteristic `p`, which is then nonzero. -/
theorem ne_zero_of_charZero_fractionRing [CharZero (FractionRing O)] : π ≠ 0 :=
  have : CharZero O := (algebraMap O (FractionRing O)).charZero
  h.ne_zero

/-- **Splitting a power of `p` off a power of the uniformizer**: for `e·v ≤ k` one has
`π ^ k = p ^ v · c` with `c` in `𝔪 ^ (k - e·v)`. This is the only place the ramification
bound is used: it turns a denominator `p ^ v` into a loss of `e·v` in the `π`-adic order. -/
theorem exists_pow_eq {v k : ℕ} (hk : e * v ≤ k) :
    ∃ c ∈ maximalIdeal O ^ (k - e * v), π ^ k = (p : O) ^ v * c := by
  obtain ⟨t, ht⟩ := h.natCast_dvd
  refine ⟨t ^ v * π ^ (k - e * v), Ideal.mul_mem_left _ _ (h.mem_pow_iff.mpr dvd_rfl), ?_⟩
  rw [← mul_assoc, ← mul_pow, ← ht, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hk]

/-- A nonzero natural number divides `π ^ k` as soon as `e·v_p(n) ≤ k`. -/
theorem natCast_dvd_pow {n : ℕ} (hn : n ≠ 0) {k : ℕ} (hk : e * padicValNat p n ≤ k) :
    (n : O) ∣ π ^ k := by
  obtain ⟨u, hu⟩ := exists_units_natCast_eq h.prime h.natCast_mem hn
  obtain ⟨c, -, hc⟩ := h.exists_pow_eq hk
  rw [hu, hc]
  exact mul_dvd_mul_left _ u.isUnit.dvd

end IsUniformizer

/-! ### Comparing elements through their residues -/

/-- Elements whose difference lies in the maximal ideal have the same residue. -/
theorem residue_eq_of_sub_mem {a b : O} (h : a - b ∈ maximalIdeal O) :
    residue O a = residue O b := by
  rw [← sub_eq_zero, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr h

/-- In a local ring, elements with distinct residues differ by a unit. -/
theorem isUnit_sub_of_residue_ne {a b : O} (h : residue O a ≠ residue O b) : IsUnit (a - b) :=
  notMem_maximalIdeal.mp fun hmem ↦ h (residue_eq_of_sub_mem hmem)

end IsLocalRing

end
