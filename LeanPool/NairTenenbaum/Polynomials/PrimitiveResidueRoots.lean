/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.RootCount
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.Polynomial.Content

/-! # Residue roots of primitive integral polynomials -/

@[expose] public section

namespace NairTenenbaum

open Polynomial

theorem primitive_map_zmod_ne_zero {Q : ℤ[X]} (hQ : Q.IsPrimitive)
    {p : ℕ} (hp : p.Prime) : Q.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hzero
  have H : (C (p : ℤ) : ℤ[X]) ∣ Q := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have := congrArg (fun R : (ZMod p)[X] => R.coeff i) hzero
    simpa only [coeff_map, coeff_zero, Int.coe_castRingHom] using this
  exact (Nat.prime_iff_prime_int.mp hp).not_isUnit (hQ _ H)

theorem rootCount_le_reduction_degree {Q : ℤ[X]} {p : ℕ} (hp : p.Prime)
    (hQ : Q.map (Int.castRingHom (ZMod p)) ≠ 0) :
    rootCount Q p ≤ (Q.map (Int.castRingHom (ZMod p))).natDegree := by
  let : Fact p.Prime := ⟨hp⟩
  rw [rootCount_eq_card_filter Q p]
  apply Polynomial.card_le_degree_of_subset_roots
  intro a ha
  exact (Polynomial.mem_roots hQ).mpr (by
    simpa only [Polynomial.IsRoot, Polynomial.eval_map] using (Finset.mem_filter.mp ha).2)

theorem primitive_rootCount_le_degree {Q : ℤ[X]} (hQ : Q.IsPrimitive)
    {p : ℕ} (hp : p.Prime) : rootCount Q p ≤ Q.natDegree :=
  (rootCount_le_reduction_degree hp (primitive_map_zmod_ne_zero hQ hp)).trans natDegree_map_le

theorem primitive_rootCount_lt_of_degree_lt {Q : ℤ[X]} (hQ : Q.IsPrimitive)
    {p : ℕ} (hp : p.Prime) (hdeg : Q.natDegree < p) : rootCount Q p < p :=
  (primitive_rootCount_le_degree hQ hp).trans_lt hdeg

theorem primitive_noFixedPrimeDivisor_of_degree_le_one {Q : ℤ[X]} (hQ : Q.IsPrimitive)
    (hdeg : Q.natDegree ≤ 1) : NoFixedPrimeDivisor Q :=
  fun _ hp => primitive_rootCount_lt_of_degree_lt hQ hp (hdeg.trans_lt hp.one_lt)

end NairTenenbaum
