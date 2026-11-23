/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

/-!
# Laws of the Equational Theories Project used here

Laws are numbered as in the Equational Theories Project (ETP, `teorth/equational_theories`).
A magma is a type with a binary operation `op`, written `◇` in the docstrings, and it satisfies a
law when the identity holds for all values of the variables. We write `S x = x ◇ x`.

The definitions are the ones registered with Palomar (`PALOMAR-2026-09-30-000005`), unchanged.
-/

@[expose] public section

namespace Magma1518

/-- ETP law 1518: `x = (y ◇ y) ◇ (x ◇ (y ◇ x))`. -/
def Law1518 {G : Type} (op : G → G → G) : Prop := ∀ x y, x = (op (op y y) (op x (op y x)))

/-- ETP law 3862: `x ◇ x = (x ◇ (x ◇ x)) ◇ x`. -/
def Law3862 {G : Type} (op : G → G → G) : Prop := ∀ x, (op x x) = (op (op x (op x x)) x)

/-- ETP law 47: `x = x ◇ (x ◇ (x ◇ x))`. -/
def Law47 {G : Type} (op : G → G → G) : Prop := ∀ x, x = (op x (op x (op x x)))

/-- ETP law 614: `x = x ◇ (x ◇ ((x ◇ x) ◇ x))`. -/
def Law614 {G : Type} (op : G → G → G) : Prop := ∀ x, x = (op x (op x (op (op x x) x)))

/-- ETP law 817: `x = x ◇ ((x ◇ x) ◇ (x ◇ x))`. -/
def Law817 {G : Type} (op : G → G → G) : Prop := ∀ x, x = (op x (op (op x x) (op x x)))

/-- `T x = {x, S x, S (S x)}` with `S y = y ◇ y`: `inT op x y` says that `y` is one of the
three. -/
def inT {G : Type} (op : G → G → G) (x y : G) : Prop :=
  y = x ∨ y = op x x ∨ y = op (op x x) (op x x)

/-- Words in one generator: the free magma on one generator `v`. -/
inductive W where
  /-- The generator. -/
  | v : W
  /-- The product of two words. -/
  | m : W → W → W

/-- Evaluation of a word at `x`. -/
def ev {G : Type} (op : G → G → G) (x : G) : W → G
  | .v => x
  | .m a b => op (ev op x a) (ev op x b)

end Magma1518
