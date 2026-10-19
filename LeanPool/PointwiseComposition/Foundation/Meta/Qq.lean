/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import Mathlib.Util.Qq
public meta import Mathlib.Util.Qq
public import Mathlib.Tactic.TypeStar
public meta import Lean.Meta.LitValues

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public meta section

namespace Qq

open _root_.Qq

open _root_.Lean Mathlib _root_.Qq Qq Lean Elab Meta Tactic

/-- The rfl Q construction in `Qq`. -/
def rflQ {α : Q(Sort u)} (a : Q($α)) : Q($a = $a) := q(rfl)







/-- The to QList construction in `Qq`. -/
def toQList {α : Q(Type u)} : List Q($α) → Q(List $α)
  |     [] => q([])
  | a :: v => q($a :: $(toQList v))







lemma List.mem_of_eq {a b : α} {l} (h : a = b) : a ∈ b :: l := by simp [h]

lemma List.mem_of_mem {a b : α} {l : List α} (h : a ∈ l) : a ∈ b :: l := by simp [h]

lemma List.mem_singleton_of_eq (a b : α) (h : a = b) : a ∈ [b] := by simp [h]

/-- The mem QList? construction in `Qq`. -/
def memQListOptional {α : Q(Type u)} (a : Q($α)) : (l : List Q($α)) → MetaM <| Option Q($a ∈
    $(toQList l))
  |     [] => return none
  | b :: l => do
    if (← isDefEq (← whnf a) (← whnf b)) then
      let e : Q($a = $b) := rflQ a
      return some q(List.mem_of_eq $e)
    else
      let some h ← memQListOptional a l | return none
      return some q(List.mem_of_mem $h)







/-- The mem QList?' construction in `Qq`. -/
def memQListOptional' (a : Expr) (l : List Expr) : MetaM (Option Expr) := do
  let ⟨u, _, a⟩ ← inferTypeQ' a
  memQListOptional (u := u) a l

/-- The of QList construction in `Qq`. -/
def ofQList {α : Q(Type u)} (l : Q(List $α)) : MetaM <| List Q($α) := do
  let some entries ← getListLit? (← whnf l)
    | throwError "Expected an explicit list of formulas"
  return entries.toList

end Qq

end

end PointwiseComposition
