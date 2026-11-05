/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Ring.Opposite
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Associator

/-!
# Alternative rings and algebras

An *alternative* multiplication satisfies the two alternative laws

* **left alternative**  `a * (a * b) = (a * a) * b`
* **right alternative** `(b * a) * a = b * (a * a)`

Every associative multiplication is alternative; the octonions are the standard non-associative
example. Alternativity is the structural hypothesis under which composition algebras live
(`GPR 19.3`: every composition algebra is alternative).

## Implementation notes

`IsAlternative` is a **`Prop`-valued mixin on `[Mul α]`**, following `IsJordan` in
`Mathlib.Algebra.Jordan.Basic`. It deliberately does **not** bundle the ring structure:

* the axioms are multiplicative equations and need neither addition nor negation, so `[Mul α]` is
  the honest hypothesis;
* bundling would fuse "is a non-associative ring" with "satisfies the alternative laws", which
  overview §2 forbids — algebra structure, norm regularity and module regularity are independent
  axes;
* a bundled class carrying its own `NonAssocRing` parent diamonds against `ConicAlgebra`'s
  `[NonAssocRing A] [Module k A] [SMulCommClass k A A] [IsScalarTower k A A]` (mathlib's `Algebra`
  requires an associative `Semiring`), making `IsComposition → IsAlternative` awkward to state.

One instance (`Semigroup.isAlternative`) covers every associative case, mirroring
`CommSemigroup.isCommJordan`.

The associator characterizations live below `[NonUnitalNonAssocRing α]`, where subtraction exists.

⚠ The linearizations are proved using additivity only — **no `Invertible 2`** — so they hold in
characteristic 2. Do not "simplify" them by halving.

## Main results

* `IsAlternative` : the mixin.
* `IsAlternative.associator_self_left/right/mid` : the associator vanishes on repeated arguments.
* `IsAlternative.associator_swap_left/right` : the associator is alternating.
* `IsAlternative.flexible` : `(a * b) * a = a * (b * a)`.
* `IsAlternative.left_alt_linearized`, `right_alt_linearized` : the linearized laws.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 13.2.
* Schafer, *An Introduction to Nonassociative Algebras*, §3.
* Zhevlakov et al., *Rings That Are Nearly Associative*, Ch. 2.
-/

@[expose] public section

universe u

/-- An **alternative** multiplication: the associator vanishes whenever two adjacent arguments
coincide. Stated on `[Mul α]` as a `Prop` mixin, following `IsJordan`. -/
class IsAlternative (α : Type u) [Mul α] : Prop where
  /-- Left alternative law: `a * (a * b) = (a * a) * b`. -/
  left_alt : ∀ a b : α, a * (a * b) = (a * a) * b
  /-- Right alternative law: `(b * a) * a = b * (a * a)`. -/
  right_alt : ∀ a b : α, (b * a) * a = b * (a * a)

namespace IsAlternative

section Mul
variable {α : Type u} [Mul α] [IsAlternative α]

theorem mul_mul_self_left (a b : α) : a * (a * b) = (a * a) * b := IsAlternative.left_alt a b

theorem mul_self_mul_right (a b : α) : (b * a) * a = b * (a * a) := IsAlternative.right_alt a b

end Mul

/-- Every associative multiplication is alternative. This single instance replaces what a bundled
hierarchy would need four instances for. -/
instance (priority := 100) _root_.Semigroup.isAlternative (α : Type u) [Semigroup α] :
    IsAlternative α where
  left_alt a b := (mul_assoc a a b).symm
  right_alt a b := mul_assoc b a a

section Ring
variable {α : Type u} [NonUnitalNonAssocRing α] [IsAlternative α]

/-- The associator vanishes when the first two arguments coincide. -/
theorem associator_self_left (a b : α) : associator a a b = 0 := by
  simp [associator, mul_mul_self_left]

/-- The associator vanishes when the last two arguments coincide. -/
theorem associator_self_right (a b : α) : associator b a a = 0 := by
  simp [associator, mul_self_mul_right]

/-! ### The associator is alternating

Linearizations of the two alternative laws. Additivity only — valid in characteristic 2. -/

/-- Linearized left alternative law: `⁅a, b, c⁆ + ⁅b, a, c⁆ = 0`. -/
theorem associator_add_swap_left (a b c : α) :
    associator a b c + associator b a c = 0 := by
  have h := associator_self_left (a + b) c
  rw [associator_add_left, associator_add_mid, associator_add_mid,
    associator_self_left, associator_self_left, zero_add, add_zero] at h
  exact h

/-- Swapping the first two arguments negates the associator. -/
theorem associator_swap_left (a b c : α) : associator a b c = -associator b a c :=
  eq_neg_of_add_eq_zero_left (associator_add_swap_left a b c)

/-- Linearized right alternative law: `⁅a, b, c⁆ + ⁅a, c, b⁆ = 0`. -/
theorem associator_add_swap_right (a b c : α) :
    associator a b c + associator a c b = 0 := by
  have h := associator_self_right (b + c) a
  rw [associator_add_mid, associator_add_right, associator_add_right,
    associator_self_right, associator_self_right, zero_add, add_zero] at h
  exact h

/-- Swapping the last two arguments negates the associator. -/
theorem associator_swap_right (a b c : α) : associator a b c = -associator a c b :=
  eq_neg_of_add_eq_zero_left (associator_add_swap_right a b c)

/-- The associator vanishes when the first and third arguments coincide. -/
theorem associator_self_mid (a b : α) : associator a b a = 0 := by
  rw [associator_swap_left a b a, associator_self_right, neg_zero]

/-- **Flexible law**: `(a * b) * a = a * (b * a)`. -/
theorem flexible (a b : α) : (a * b) * a = a * (b * a) :=
  (associator_eq_zero_iff a b a).mp (associator_self_mid a b)

/-! ### Linearized alternative laws, multiplicative form -/

/-- `a * (b * x) + b * (a * x) = (a * b) * x + (b * a) * x`. -/
theorem left_alt_linearized (a b x : α) :
    a * (b * x) + b * (a * x) = (a * b) * x + (b * a) * x := by
  calc
    a * (b * x) + b * (a * x) =
        ((a * b) * x - associator a b x) +
          ((b * a) * x - associator b a x) := by
      simp only [associator]
      abel
    _ = (a * b) * x + (b * a) * x -
        (associator a b x + associator b a x) := by
      abel
    _ = (a * b) * x + (b * a) * x := by
      rw [associator_add_swap_left]
      simp

/-- `(x * a) * b + (x * b) * a = x * (a * b) + x * (b * a)`. -/
theorem right_alt_linearized (x a b : α) :
    (x * a) * b + (x * b) * a = x * (a * b) + x * (b * a) := by
  calc
    (x * a) * b + (x * b) * a =
        (x * (a * b) + associator x a b) +
          (x * (b * a) + associator x b a) := by
      simp only [associator]
      abel
    _ = x * (a * b) + x * (b * a) +
        (associator x a b + associator x b a) := by
      abel
    _ = x * (a * b) + x * (b * a) := by
      rw [associator_add_swap_right]
      simp

end Ring

/-- The opposite of an alternative multiplication is alternative: the two laws swap. -/
instance {α : Type u} [Mul α] [IsAlternative α] : IsAlternative αᵐᵒᵖ where
  left_alt a b := by
    obtain ⟨a⟩ := a; obtain ⟨b⟩ := b
    change MulOpposite.op ((b * a) * a) = MulOpposite.op (b * (a * a))
    rw [mul_self_mul_right]
  right_alt a b := by
    obtain ⟨a⟩ := a; obtain ⟨b⟩ := b
    change MulOpposite.op (a * (a * b)) = MulOpposite.op ((a * a) * b)
    rw [mul_mul_self_left]

end IsAlternative
