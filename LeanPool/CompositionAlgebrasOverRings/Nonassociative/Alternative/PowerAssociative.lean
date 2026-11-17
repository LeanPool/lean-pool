/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Alternative.Artin
public import Mathlib.Algebra.Group.PNatPowAssoc

/-!
# Power-associativity of alternative rings

A multiplication is *power-associative* if every element generates an associative subring, so that
all parenthesizations of `a * a * ⋯ * a` agree and `a ^ n` is well defined.

## Implementation notes

⚠ This file deliberately does **not** introduce a hierarchy of power-associative classes. An earlier
draft defined four bundled classes (`NonUnitalPowerAssocSemiring`, `PowerAssocSemiring`,
`NonUnitalPowerAssocRing`, `PowerAssocRing`) whose only content was that associative rings are
power-associative — the trivial direction, and a doubling of the class count for no theorem we need.

In this development power-associativity is a **corollary of Artin's theorem**: a single element
generates a two-generated (indeed one-generated) subring, which Artin makes associative. That is the
direction we actually use, and it needs no new classes.

The recursive power below is `private` implementation detail. It exists only because a
non-associative multiplication has no canonical `Monoid.npow`; once associativity is available,
prefer mathlib's `^`. mathlib's power-associativity mixin `PNatPowAssoc` is stated for a type
that already carries a power operation, and an alternative ring carries none; so the left-recursive
power is packaged as `leftRecursivePPow`, a `def` rather than an instance, and
`IsAlternative.pnatPowAssoc` proves `PNatPowAssoc` for it. Installing `leftRecursivePPow` as a
local instance then gives mathlib's API (`ppow_mul_assoc`, `ppow_mul_comm`, `ppow_mul`).

## Main results

* `IsAlternative.pow_assoc` : powers of a single element associate.
* `IsAlternative.pnatPowAssoc` : the same, as mathlib's `PNatPowAssoc` for `leftRecursivePPow`.

## References

* Schafer, *An Introduction to Nonassociative Algebras*, §3.
-/

@[expose] public section

universe u

/-- Left-recursive power for positive exponents: `nonassocPow n a = a ^ (n + 1)`.
Private implementation detail — see the module docstring. -/
def nonassocPow {α : Type u} [Mul α] : ℕ → α → α
  | 0, a => a
  | n + 1, a => a * nonassocPow n a

@[simp]
theorem nonassocPow_zero {α : Type u} [Mul α] (a : α) : nonassocPow 0 a = a := rfl

@[simp] theorem nonassocPow_succ {α : Type u} [Mul α] (n : ℕ) (a : α) :
    nonassocPow (n + 1) a = a * nonassocPow n a := rfl

/-- Positive powers by left recursion, `a ^ 1 = a` and `a ^ (n + 1) = a * a ^ n`, as a power by
`ℕ+`. A non-associative multiplication has no canonical power, so this is a `def` to be installed
as a local instance where wanted, not a global instance. -/
@[instance_reducible]
def leftRecursivePPow (α : Type u) [Mul α] : Pow α ℕ+ :=
  ⟨fun a n ↦ nonassocPow n.natPred a⟩

namespace IsAlternative

variable {α : Type u} [NonUnitalNonAssocRing α] [IsAlternative α]

/-- Powers of a single element associate: `aᵐ⁺¹ * aⁿ⁺¹ = aᵐ⁺ⁿ⁺²`.
-/
theorem pow_assoc (m n : ℕ) (a : α) :
    nonassocPow m a * nonassocPow n a = nonassocPow (m + n + 1) a := by
  have hpow : ∀ r : ℕ, nonassocPow r a ∈ NonUnitalSubring.closure ({a, a} : Set α) := by
    intro r
    induction r with
    | zero => exact NonUnitalSubring.subset_closure (Or.inl rfl)
    | succ r hr => exact mul_mem (NonUnitalSubring.subset_closure (Or.inl rfl)) hr
  induction m with
  | zero =>
      simpa only [nonassocPow_zero, Nat.zero_add] using (nonassocPow_succ n a).symm
  | succ m ih =>
      rw [nonassocPow_succ]
      rw [artin_two_generated_assoc a a (NonUnitalSubring.subset_closure (Or.inl rfl))
        (hpow m) (hpow n), ih]
      rw [← nonassocPow_succ]
      congr 1
      omega

/-- **Power-associativity in mathlib's sense**: with the left-recursive power `leftRecursivePPow`,
an alternative ring is `PNatPowAssoc`. This is `IsAlternative.pow_assoc` with the exponents shifted
to `ℕ+`. -/
theorem pnatPowAssoc : @PNatPowAssoc α _ (leftRecursivePPow α) :=
  letI := leftRecursivePPow α
  { ppow_add := fun k n x ↦ by
      change nonassocPow (k + n).natPred x = nonassocPow k.natPred x * nonassocPow n.natPred x
      rw [pow_assoc]
      congr 1
      simp only [PNat.natPred, PNat.add_coe]
      have := k.pos
      have := n.pos
      omega
    ppow_one := fun _ ↦ rfl }

end IsAlternative
