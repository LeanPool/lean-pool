/-
Copyright (c) 2026 Richard Bean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Bean
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Algebra.Operations

/-! The pigeonhole step, stated independently of Latin squares. -/

@[expose] public section

namespace LatinQuarter

open scoped BigOperators Pointwise

variable {R : Type*} [CommRing R]

theorem product_eq_zero_of_repeated_square_zero
    {ι : Type*} [Fintype ι] (f : ι → R)
    {a b : ι} (hab : a ≠ b) (heq : f a = f b)
    (hsq : f a * f a = 0) : ∏ i, f i = 0 := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase a) f
    (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
  rw [← mul_assoc, ← heq, hsq, zero_mul]

theorem product_eq_zero_of_card_lt
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (z : κ → R) (hz : ∀ j, z j * z j = 0)
    (f : ι → κ) (hcard : Fintype.card κ < Fintype.card ι) :
    ∏ i, z (f i) = 0 := by
  have hn : ¬ Function.Injective f := by
    intro hf
    exact (not_le_of_gt hcard) (Fintype.card_le_of_injective f hf)
  simp only [Function.Injective, not_forall] at hn
  obtain ⟨a, b, hab⟩ := hn
  have heq : f a = f b := by tauto
  have hne : a ≠ b := by tauto
  exact product_eq_zero_of_repeated_square_zero (fun i => z (f i))
    hne (congrArg z heq) (hz (f a))

theorem span_square_zero_pow_eq_bot
    {κ : Type*} [Fintype κ] (z : κ → R)
    (hz : ∀ j, z j * z j = 0) {d : ℕ}
    (hd : Fintype.card κ < d) :
    Ideal.span (Set.range z) ^ d = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  change (Submodule.span R (Set.range z)) ^ d ≤ ⊥
  rw [Submodule.span_pow]
  apply Submodule.span_le.mpr
  intro x hx
  obtain ⟨f, hf, rfl⟩ := Set.mem_pow_iff_prod.mp hx
  choose g hg using hf
  have hfz : f = fun i => z (g i) := funext (fun i => (hg i).symm)
  rw [hfz]
  have heq := product_eq_zero_of_card_lt z hz g (by simpa using hd)
  simpa only [Submodule.mem_bot, SetLike.mem_coe] using heq

end LatinQuarter
