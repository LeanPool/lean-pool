/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import LeanPool.FormalLinguistics.Lambek

/-!
  Shared definitions for the proof that Lambek grammars generate only context-free
  languages (Pentus 1993).

    • `LDer0`: the cut-free Lambek calculus with atomic axioms.
    • `LType.size`, `LType.occ`, `LType.map`: size, occurrence counts and renaming of
      primitive types.
    • `FGWord`: words over signed letters, with a normaliser `reduce`, used for the
      free-group interpretation of types.

  The statements proved about these definitions live in `LambekCut.lean`,
  `LambekInterpolation.lean` and `LambekFreeGroup.lean`.
-/

@[expose] public section

namespace FormalLinguistics

/-- The cut-free Lambek calculus `L` with atomic axioms `p → p`. The rules are those of
    `LDer` without cut. -/
inductive LDer0 {P : Type} : List (LType P) → LType P → Prop where
  | ax (p : P) : LDer0 [LType.prim p] (LType.prim p)
  | overR {Γ : List (LType P)} {A B : LType P} :
      Γ ≠ [] → LDer0 (Γ ++ [B]) A → LDer0 Γ (LType.over A B)
  | underR {Γ : List (LType P)} {A B : LType P} :
      Γ ≠ [] → LDer0 (B :: Γ) A → LDer0 Γ (LType.under B A)
  | overL {Γ Δ Θ : List (LType P)} {A B C : LType P} :
      LDer0 Θ B → LDer0 (Γ ++ [A] ++ Δ) C → LDer0 (Γ ++ [LType.over A B] ++ Θ ++ Δ) C
  | underL {Γ Δ Θ : List (LType P)} {A B C : LType P} :
      LDer0 Θ B → LDer0 (Γ ++ [A] ++ Δ) C → LDer0 (Γ ++ Θ ++ [LType.under B A] ++ Δ) C
  | mulR {Γ Δ : List (LType P)} {A B : LType P} :
      LDer0 Γ A → LDer0 Δ B → LDer0 (Γ ++ Δ) (LType.mul A B)
  | mulL {Γ Δ : List (LType P)} {A B C : LType P} :
      LDer0 (Γ ++ [A, B] ++ Δ) C → LDer0 (Γ ++ [LType.mul A B] ++ Δ) C

namespace LType

variable {P Q : Type}

/-- Number of occurrences of primitive types in a type. -/
def size : LType P → Nat
  | prim _ => 1
  | over A B => size A + size B
  | under B A => size B + size A
  | mul A B => size A + size B

/-- Number of occurrences of the primitive type `p` in a type. -/
def occ [DecidableEq P] (p : P) : LType P → Nat
  | prim q => if q = p then 1 else 0
  | over A B => occ p A + occ p B
  | under B A => occ p B + occ p A
  | mul A B => occ p A + occ p B

/-- Renaming of primitive types. -/
def map (f : P → Q) : LType P → LType Q
  | prim p => prim (f p)
  | over A B => over (map f A) (map f B)
  | under B A => under (map f B) (map f A)
  | mul A B => mul (map f A) (map f B)

end LType

/-- Total size of a sequence of types. -/
def sizeList {P : Type} (Γ : List (LType P)) : Nat := (Γ.map LType.size).sum

/-- Number of occurrences of `p` in a sequence of types. -/
def occList {P : Type} [DecidableEq P] (p : P) (Γ : List (LType P)) : Nat :=
  (Γ.map (LType.occ p)).sum

/-- Words over signed letters: `(p, true)` stands for the generator `p` and `(p, false)`
    for its inverse. -/
abbrev FGWord (P : Type) := List (P × Bool)

namespace FGWord

variable {P : Type}

/-- Formal inverse of a word. -/
def inv (w : FGWord P) : FGWord P := (w.map fun x => (x.1, !x.2)).reverse

/-- Push a letter on a stack (top at the head), cancelling it against the top if the top
    is its inverse. -/
def push [DecidableEq P] (s : FGWord P) (x : P × Bool) : FGWord P :=
  match s with
  | y :: s' => if y.1 = x.1 ∧ y.2 = !x.2 then s' else x :: y :: s'
  | [] => [x]

/-- The freely reduced form of a word. -/
def reduce [DecidableEq P] (w : FGWord P) : FGWord P := (w.foldl push []).reverse

/-- Length of the freely reduced form. -/
def norm [DecidableEq P] (w : FGWord P) : Nat := (reduce w).length

end FGWord

namespace LType

variable {P : Type}

/-- Free-group interpretation of a type, as an unreduced word. -/
def interp : LType P → FGWord P
  | prim p => [(p, true)]
  | over A B => interp A ++ FGWord.inv (interp B)
  | under B A => FGWord.inv (interp B) ++ interp A
  | mul A B => interp A ++ interp B

end LType

/-- Free-group interpretation of a sequence of types. -/
def interpList {P : Type} (Γ : List (LType P)) : FGWord P := (Γ.map LType.interp).flatten

end FormalLinguistics
