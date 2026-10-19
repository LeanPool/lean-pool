/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import Mathlib.Init

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
The least congruence containing a relation, defined as the intersection of
all equivalence relations compatible with the given binary operation.
No associativity, identity, or arithmetic hypothesis is required.
-/

@[expose] public section

namespace FailureOfComposition
namespace CompositionClosure

universe u v

variable {A : Type u}

/-- The Is Congruence construction in `FailureOfComposition.CompositionClosure`. -/
def IsCongruence (op : A → A → A) (R : A → A → Prop) : Prop :=
  Equivalence R ∧ ∀ a a' b b', R a a' → R b b' → R (op a b) (op a' b')

/-- The Generated construction in `FailureOfComposition.CompositionClosure`. -/
def Generated (op : A → A → A) (r : A → A → Prop) (a b : A) : Prop :=
  ∀ R : A → A → Prop, IsCongruence op R → (∀ x y, r x y → R x y) → R a b

theorem base (op : A → A → A) (r : A → A → Prop) {a b : A} (h : r a b) : Generated op r a b :=
  fun _ _ hr => hr a b h

theorem refl (op : A → A → A) (r : A → A → Prop) (a : A) : Generated op r a a := fun _ hR _ =>
  hR.1.refl a

theorem symm {op : A → A → A} {r : A → A → Prop} {a b : A} (h : Generated op r a b) :
    Generated op r b a := fun R hR hr => hR.1.symm (h R hR hr)

theorem trans {op : A → A → A} {r : A → A → Prop} {a b c : A} (hab : Generated op r a b)
    (hbc : Generated op r b c) : Generated op r a c := fun R hR hr =>
  hR.1.trans (hab R hR hr) (hbc R hR hr)

theorem comp {op : A → A → A} {r : A → A → Prop} {a a' b b' : A} (ha : Generated op r a a')
    (hb : Generated op r b b') : Generated op r (op a b) (op a' b') := fun R hR hr =>
  hR.2 a a' b b' (ha R hR hr) (hb R hR hr)

theorem comp_left (op : A → A → A) (r : A → A → Prop) (c : A) {a b : A}
    (h : Generated op r a b) : Generated op r (op c a) (op c b) :=
  comp (refl op r c) h

theorem comp_right (op : A → A → A) (r : A → A → Prop) (c : A) {a b : A}
    (h : Generated op r a b) : Generated op r (op a c) (op b c) :=
  comp h (refl op r c)

/-- Every congruence containing the generators contains the generated relation. -/
theorem least {op : A → A → A} {r R : A → A → Prop} (hR : IsCongruence op R)
    (hr : ∀ x y, r x y → R x y) {a b : A} (h : Generated op r a b) : R a b :=
  h R hR hr

theorem isCongruence (op : A → A → A) (r : A → A → Prop) : IsCongruence op (Generated op r) :=
  ⟨⟨refl op r, fun h => symm h, fun h h' => trans h h'⟩, fun _ _ _ _ ha hb => comp ha hb⟩

/-- The setoid construction in `FailureOfComposition.CompositionClosure`. -/
def setoid (op : A → A → A) (r : A → A → Prop) : Setoid A
    where
  r := Generated op r
  iseqv := (isCongruence op r).1

theorem monotone {op : A → A → A} {r s : A → A → Prop} (hrs : ∀ x y, r x y → s x y) {a b : A}
    (h : Generated op r a b) : Generated op s a b := fun R hR hs =>
  h R hR (fun x y hxy => hs x y (hrs x y hxy))

theorem iff_of_isCongruence {op : A → A → A} {r : A → A → Prop} (hr : IsCongruence op r)
    (a b : A) : Generated op r a b ↔ r a b :=
  ⟨least hr (fun _ _ h => h), base op r⟩

theorem idempotent (op : A → A → A) (r : A → A → Prop) (a b : A) :
    Generated op (Generated op r) a b ↔ Generated op r a b :=
  iff_of_isCongruence (isCongruence op r) a b

/-- A homomorphism carrying generators into generators preserves their
generated congruences, even between different universes. -/
theorem map {B : Type v} (opA : A → A → A) (opB : B → B → B) (r : A → A → Prop)
    (s : B → B → Prop) (f : A → B) (hop : ∀ x y, f (opA x y) = opB (f x) (f y))
    (hrs : ∀ x y, r x y → s (f x) (f y)) {a b : A} (h : Generated opA r a b) :
    Generated opB s (f a) (f b) := by
  intro R hR hs
  apply h (fun x y => R (f x) (f y))
  · constructor
    · exact ⟨fun x => hR.1.refl (f x), fun h => hR.1.symm h, fun h h' => hR.1.trans h h'⟩
    · intro x x' y y' hxx' hyy'
      rw [hop x y, hop x' y']
      exact hR.2 _ _ _ _ hxx' hyy'
  · exact fun x y hxy => hs (f x) (f y) (hrs x y hxy)

end CompositionClosure
end FailureOfComposition

end

end PointwiseComposition
