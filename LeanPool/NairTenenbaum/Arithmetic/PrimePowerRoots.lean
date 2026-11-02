/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.RootCount
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-! # Root counts at prime powers

Reduction modulo a prime is injective on roots whose derivative is nonzero
modulo that prime. In particular separable reduction gives a bound independent
of the exponent of the prime power.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial

/-- Reduction of a root to a divisor of its modulus. -/
noncomputable def rootsReduce (Q : ℤ[X]) {m n : ℕ} (hmn : m ∣ n) :
    ResidueRoots Q n → ResidueRoots Q m := fun a =>
  ⟨ZMod.castHom hmn (ZMod m) a, by
    rw [← eval₂_int_cast_natural, a.property, map_zero]⟩

/-- A congruence with no roots remains root-free at every multiple of its modulus. -/
theorem rootCount_eq_zero_of_dvd {Q : ℤ[X]} {m n : ℕ} (hm : m ≠ 0)
    (hmn : m ∣ n) (hQ : rootCount Q m = 0) : rootCount Q n = 0 := by
  let : NeZero m := ⟨hm⟩
  have : IsEmpty (ResidueRoots Q m) := Fintype.card_eq_zero_iff.mp
    (by simpa only [rootCount, Nat.card_eq_fintype_card] using hQ)
  let : IsEmpty (ResidueRoots Q n) :=
    ⟨fun a => isEmptyElim (rootsReduce Q hmn a)⟩
  exact Nat.card_of_isEmpty

/-- Uniqueness of a simple root above its residue modulo `p`. -/
theorem rootsReduce_injective_of_simple {Q : ℤ[X]} {p ν : ℕ} (hp : p.Prime)
    (hν : ν ≠ 0)
    (hsimple : ∀ a : ResidueRoots Q p,
      Q.derivative.eval₂ (Int.castRingHom (ZMod p)) (a : ZMod p) ≠ 0) :
    Function.Injective (rootsReduce Q (dvd_pow_self p hν)) := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero ν := ⟨hν⟩
  let φ := ZMod.castHom (dvd_pow_self p hν) (ZMod p)
  let : NeZero (p ^ ν) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let : IsLocalHom φ := ⟨fun x hx => by
    have hcast : φ x = (x.val : ZMod p) := by
      calc
        φ x = φ (x.val : ZMod (p ^ ν)) := congrArg φ (ZMod.natCast_zmod_val x).symm
        _ = _ := map_natCast φ x.val
    have hcop := (ZMod.isUnit_iff_coprime x.val p).mp (hcast ▸ hx)
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.isUnit_iff_coprime x.val (p ^ ν)).mpr (hcop.pow_right ν)⟩
  let : IsLocalRing (ZMod (p ^ ν)) := φ.domain_isLocalRing
  intro a b hab
  have heq : φ a = φ b := congrArg Subtype.val hab
  have hnonunit : ¬ IsUnit ((a : ZMod (p ^ ν)) - b) := by
    intro hu
    have hz : φ ((a : ZMod (p ^ ν)) - b) = 0 :=
      (map_sub φ _ _).trans (sub_eq_zero.mpr heq)
    exact not_isUnit_zero (hz ▸ hu.map φ)
  have hd : IsUnit ((Q.map (Int.castRingHom (ZMod (p ^ ν)))).derivative.eval
      (a : ZMod (p ^ ν))) := by
    apply (isUnit_map_iff φ _).mp
    apply isUnit_iff_ne_zero.mpr
    rw [derivative_map, Polynomial.eval_map, eval₂_int_cast_natural]
    exact hsimple (rootsReduce Q (dvd_pow_self p hν) a)
  apply Subtype.ext
  exact IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
    (by simpa only [Polynomial.eval_map] using a.property)
    (by simpa only [Polynomial.eval_map] using b.property) hnonunit hd

theorem rootCount_prime_pow_le_of_simple {Q : ℤ[X]} {p ν : ℕ} (hp : p.Prime)
    (hν : ν ≠ 0)
    (hsimple : ∀ a : ResidueRoots Q p,
      Q.derivative.eval₂ (Int.castRingHom (ZMod p)) (a : ZMod p) ≠ 0) :
    rootCount Q (p ^ ν) ≤ rootCount Q p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  exact Nat.card_le_card_of_injective _ (rootsReduce_injective_of_simple hp hν hsimple)

/-- The prime-power root bound for a polynomial with separable reduction. -/
theorem rootCount_prime_pow_le {Q : ℤ[X]} {p ν : ℕ} (hp : p.Prime) (hν : ν ≠ 0)
    (hsep : (Q.map (Int.castRingHom (ZMod p))).Separable) :
    rootCount Q (p ^ ν) ≤ rootCount Q p := by
  let : Fact p.Prime := ⟨hp⟩
  apply rootCount_prime_pow_le_of_simple hp hν
  intro a
  have h := hsep.eval₂_derivative_ne_zero (RingHom.id (ZMod p))
    (x := (a : ZMod p)) (by simpa only [eval₂_id, Polynomial.eval_map] using a.property)
  simpa only [eval₂_id, derivative_map, Polynomial.eval_map] using h

end NairTenenbaum
