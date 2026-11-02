/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.Squarefree

/-! # Polynomial root counts, equation (10)

The roots are residue classes, so multiplicities of polynomial roots are not counted.
The Chinese remainder theorem gives multiplicativity for all coprime positive moduli.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial

/-- Roots of an integral polynomial in the specified residue ring. -/
abbrev ResidueRoots (Q : ℤ[X]) (n : ℕ) :=
  {a : ZMod n // Q.eval₂ (Int.castRingHom (ZMod n)) a = 0}

/-- `ρ_Q(n)`, the number of roots modulo `n`. Only positive moduli are used. -/
noncomputable def rootCount (Q : ℤ[X]) (n : ℕ) : ℕ := Nat.card (ResidueRoots Q n)

theorem eval₂_int_cast_natural {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Q : ℤ[X]) (a : R) :
    f (Q.eval₂ (Int.castRingHom R) a) = Q.eval₂ (Int.castRingHom S) (f a) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext_int _ _

/-- The CRT equivalence restricted to the zero loci. -/
noncomputable def rootsCRT (Q : ℤ[X]) {m n : ℕ} (h : m.Coprime n) :
    ResidueRoots Q (m * n) ≃ ResidueRoots Q m × ResidueRoots Q n := by
  let e := ZMod.chineseRemainder h
  let f : ZMod (m * n) →+* ZMod m := (RingHom.fst _ _).comp e.toRingHom
  let g : ZMod (m * n) →+* ZMod n := (RingHom.snd _ _).comp e.toRingHom
  refine {
    toFun := fun a => (⟨f a, ?_⟩, ⟨g a, ?_⟩)
    invFun := fun a => ⟨e.symm (a.1, a.2), ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · rw [← eval₂_int_cast_natural f, a.property, map_zero]
  · rw [← eval₂_int_cast_natural g, a.property, map_zero]
  · apply e.injective
    apply Prod.ext
    · change f (Q.eval₂ _ _) = _
      rw [eval₂_int_cast_natural]
      simpa [f] using a.1.property
    · change g (Q.eval₂ _ _) = _
      rw [eval₂_int_cast_natural]
      simpa [g] using a.2.property
  · intro a
    apply Subtype.ext
    exact e.symm_apply_apply a
  · intro a
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst (e.apply_symm_apply (a.1, a.2))
    · exact congrArg Prod.snd (e.apply_symm_apply (a.1, a.2))

theorem rootCount_mul (Q : ℤ[X]) {m n : ℕ} (h : m.Coprime n) :
    rootCount Q (m * n) = rootCount Q m * rootCount Q n := by
  rw [rootCount, Nat.card_congr (rootsCRT Q h), Nat.card_prod]
  rfl

@[simp] theorem rootCount_one (Q : ℤ[X]) : rootCount Q 1 = 1 := by
  have : Unique (ResidueRoots Q 1) :=
    { default := ⟨0, Subsingleton.elim _ _⟩
      uniq := fun _ => Subsingleton.elim _ _ }
  exact Nat.card_unique

theorem rootCount_le (Q : ℤ[X]) {n : ℕ} (hn : n ≠ 0) : rootCount Q n ≤ n := by
  let : NeZero n := ⟨hn⟩
  calc
    rootCount Q n ≤ Nat.card (ZMod n) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = n := by simp [Nat.card_eq_fintype_card]

/-- Dividing a polynomial can only remove residue roots. -/
theorem rootCount_le_of_dvd {Q T : ℤ[X]} (hQT : Q ∣ T) {n : ℕ} (hn : n ≠ 0) :
    rootCount Q n ≤ rootCount T n := by
  let : NeZero n := ⟨hn⟩
  obtain ⟨S, rfl⟩ := hQT
  let f : ResidueRoots Q n → ResidueRoots (Q * S) n := fun a =>
    ⟨a, by rw [Polynomial.eval₂_mul, a.property, zero_mul]⟩
  exact Nat.card_le_card_of_injective f fun a b hab =>
    Subtype.ext (congrArg (fun x : ResidueRoots (Q * S) n => (x : ZMod n)) hab)

/-- Multiplication by an integral unit does not change the residue roots. -/
theorem rootCount_C_mul_unit (Q : ℤ[X]) {u : ℤ} (hu : IsUnit u) (n : ℕ) :
    rootCount (C u * Q) n = rootCount Q n := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro a
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C]
  exact (hu.map (Int.castRingHom (ZMod n))).mul_right_eq_zero

@[simp] theorem rootCount_X (n : ℕ) : rootCount (X : ℤ[X]) n = 1 := by
  let e : ResidueRoots (X : ℤ[X]) n ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨0, by simp⟩
      left_inv := fun a => Subtype.ext (by simpa using a.property.symm)
      right_inv := fun _ => rfl }
  rw [rootCount, Nat.card_congr e]
  simp

/-- The paper's admissibility condition on polynomials. -/
def NoFixedPrimeDivisor (Q : ℤ[X]) : Prop :=
  ∀ p : ℕ, p.Prime → rootCount Q p < p

theorem NoFixedPrimeDivisor.of_dvd {Q T : ℤ[X]} (hT : NoFixedPrimeDivisor T)
    (hQT : Q ∣ T) : NoFixedPrimeDivisor Q := fun p hp =>
  (rootCount_le_of_dvd hQT hp.ne_zero).trans_lt (hT p hp)

theorem noFixedPrimeDivisor_X : NoFixedPrimeDivisor (X : ℤ[X]) := by
  intro p hp
  simpa using hp.one_lt

/-- Removing positive powers from a product does not change its roots modulo a prime. -/
theorem rootCount_prod_pow_prime {ι : Type*} [Fintype ι] (R : ι → ℤ[X])
    (γ : ι → ℕ) (hγ : ∀ i, 0 < γ i) {p : ℕ} (hp : p.Prime) :
    rootCount (∏ i, R i ^ γ i) p = rootCount (∏ i, R i) p := by
  let : Fact p.Prime := ⟨hp⟩
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro a
  simp only [Polynomial.eval₂_finsetProd, Polynomial.eval₂_pow, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (pow_eq_zero_iff (hγ i).ne').mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (pow_eq_zero_iff (hγ i).ne').mpr hi⟩

/-- A translate of `X` has exactly one root for every positive modulus. -/
theorem rootCount_X_add_C (b : ℤ) (n : ℕ) :
    rootCount (X + C b : ℤ[X]) n = 1 := by
  let e : ResidueRoots (X + C b : ℤ[X]) n ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨-(b : ZMod n), by
        simp only [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C]
        exact neg_add_cancel _⟩
      left_inv := fun a => Subtype.ext (by
        have ha : (a : ZMod n) + (b : ZMod n) = 0 := by
          have ha := a.property
          simp only [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C] at ha
          exact ha
        exact (eq_neg_of_add_eq_zero_left ha).symm)
      right_inv := fun _ => rfl }
  rw [rootCount, Nat.card_congr e]
  simp

theorem noFixedPrimeDivisor_X_add_C (b : ℤ) : NoFixedPrimeDivisor (X + C b : ℤ[X]) := by
  intro p hp
  rw [rootCount_X_add_C]
  exact hp.one_lt

theorem rootCount_eq_card_filter (Q : ℤ[X]) (n : ℕ) [NeZero n] :
    rootCount Q n = (Finset.univ.filter fun a : ZMod n => Q.eval₂ (Int.castRingHom _) a = 0).card
        := by
  simp only [rootCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- A polynomial with no fixed prime divisor cannot become the zero polynomial
after reduction modulo a prime. -/
theorem NoFixedPrimeDivisor.map_ne_zero {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {p : ℕ} (hp : p.Prime) : Q.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  intro hz
  have hall : ∀ a : ZMod p, Q.eval₂ (Int.castRingHom _) a = 0 := by
    intro a
    rw [← Polynomial.eval_map, hz, Polynomial.eval_zero]
  have hc : rootCount Q p = p := by
    rw [rootCount_eq_card_filter Q p]
    simp [hall]
  exact (hQ p hp).ne hc

/-- The standard prime-modulus root bound used in the sieve. -/
theorem rootCount_le_degree {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {p : ℕ} (hp : p.Prime) : rootCount Q p ≤ Q.natDegree := by
  let : Fact p.Prime := ⟨hp⟩
  rw [rootCount_eq_card_filter Q p]
  apply le_trans (Polynomial.card_le_degree_of_subset_roots (p := Q.map (Int.castRingHom (ZMod
      p))) ?_)
    Polynomial.natDegree_map_le
  intro a ha
  have ha' := (Finset.mem_filter.mp ha).2
  exact (Polynomial.mem_roots (hQ.map_ne_zero hp)).mpr (by
    simpa only [Polynomial.IsRoot, Polynomial.eval_map] using ha')

/-- The local sieve factor in Theorem 1. -/
noncomputable def sieveProduct (Q : ℤ[X]) (x : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 - (rootCount Q p : ℝ) / p)

theorem sieveProduct_pos {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q) (x : ℝ) :
    0 < sieveProduct Q x := by
  apply Finset.prod_pos
  intro p hp
  have hp' := (Finset.mem_filter.mp hp).2
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp'.pos
  have hlt : (rootCount Q p : ℝ) < p := by exact_mod_cast hQ p hp'
  exact sub_pos.mpr ((div_lt_one hpos).2 hlt)

/-- A finite product of distinct primes is squarefree. -/
theorem primeSet_product_squarefree (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    rw [Finset.prod_insert hp]
    have hprime := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ S, q) := Nat.coprime_prod_right_iff.mpr (fun q hq =>
      (Nat.coprime_primes hprime (hS' q hq)).mpr (fun h => hp (h ▸ hq)))
    exact (Nat.squarefree_mul hcop).mpr ⟨hprime.squarefree, ih hS'⟩

end NairTenenbaum
