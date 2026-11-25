/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Lookup.Defs
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.CompareExchange

/-!
# Stable radix passes with spare slots

A set presence flag denotes an empty slot. Each block receives a
pack's worth of separators for every digit. Stability places these
after the real rows of that digit.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent.Radix

/-- Requires `ys.Perm xs ∧ ys.Pairwise (fun i j => d i ≤ d j) ∧ ∀ k, ys.filter (fun x => d x =
k) = xs.filter (fun x => d x = k)`. -/
def Stable {α : Type} {s : ℕ} (d : α → Val (word s)) (xs ys : List α) : Prop :=
  ys.Perm xs ∧ ys.Pairwise (fun i j => d i ≤ d j) ∧
    ∀ k, ys.filter (fun x => d x = k) = xs.filter (fun x => d x = k)

/-- Computes the slot by the application `Wire.pair .bit a`. -/
abbrev slot (a : Wire) := Wire.pair .bit a
/-- The quantity computed by `Wire.pair (word (s + 1)) (slot a)`. -/
abbrev aug (s : ℕ) (a : Wire) := Wire.pair (word (s + 1)) (slot a)

/-- Transforms the indexed data by `(xs.filter (fun r => !r.1)).map Prod.snd`. -/
def real {α : Type} (xs : List (Bool × α)) : List α :=
  (xs.filter (fun r => !r.1)).map Prod.snd

theorem real_append {α : Type} (xs ys : List (Bool × α)) :
    real (xs ++ ys) = real xs ++ real ys := by simp [real]

/-- The value specified by `((x.1, d x.2), x)`. -/
def decorate {α : Type} {s : ℕ} (d : α → Val (word s)) (x : Bool × α) :
    Val (word (s + 1)) × (Bool × α) := ((x.1, d x.2), x)

/-- The indexed operation `keys.flatMap (fun k => List.replicate P ((false, k), true, junk)) ++
List.replicate e ((true, Lookup.zero s), true, junk)`. -/
def filler {α : Type} {s : ℕ} (junk : α) (keys : List (Val (word s))) (P e : ℕ) :
    List (Val (word (s + 1)) × (Bool × α)) :=
  keys.flatMap (fun k => List.replicate P ((false, k), true, junk)) ++
    List.replicate e ((true, Lookup.zero s), true, junk)

/-- The condition `∀ x ∈ xs, ∀ y ∈ xs, d x = d y` on the specified data. -/
def homogeneous {α : Type} {s : ℕ} (d : α → Val (word s)) (xs : List α) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ xs, d x = d y

/-- The value specified by `!(real b).isEmpty`. -/
def live {α : Type} (b : List (Bool × α)) : Bool := !(real b).isEmpty

end MatrixMultiplicationAllFields.MatrixExponent.Radix
