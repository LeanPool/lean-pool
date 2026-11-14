/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.Meta.Qq
public import LeanPool.PointwiseComposition.Foundation.Logic.LogicSymbol

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

public section

namespace FFL
namespace Meta

open _root_.Lean Mathlib _root_.Qq Qq Lean Elab Meta Tactic

/-- Data and laws for Litform in `FFL.Meta`. -/
inductive Litform (α : Type*) : Type _
  | atom (a : α) : Litform α
  | verum : Litform α
  | falsum : Litform α
  | and : Litform α → Litform α → Litform α
  | or : Litform α → Litform α → Litform α
  | neg : Litform α → Litform α
  | imply : Litform α → Litform α → Litform α
  | iff : Litform α → Litform α → Litform α

namespace Litform

instance : LogicalConnective (Litform α)
    where
  wedge := Litform.and
  vee := Litform.or
  arrow := Litform.imply
  tilde := Litform.neg

instance : LogicalNeutral (Litform α)
    where
  top := Litform.verum
  bot := Litform.falsum

section ToString

/-- The to Str construction in `FFL.Meta.Litform`. -/
def toStr [ToString α] : Litform α → String
  | ⊤ => "⊤"
  | ⊥ => "⊥"
  | atom a => s! "atom {toString a}"
  | ∼φ => "(¬" ++ toStr φ ++ ")"
  | φ ⋏ ψ => "(" ++ toStr φ ++ " ∧ " ++ toStr ψ ++ ")"
  | φ ⋎ ψ => "(" ++ toStr φ ++ " ∨ " ++ toStr ψ ++ ")"
  | φ ⇒ₗ ψ => "(" ++ toStr φ ++ " → " ++ toStr ψ ++ ")"
  | iff φ ψ => "(" ++ toStr φ ++ " ↔ " ++ toStr ψ ++ ")"

instance [ToString α] : ToString (Litform α) :=
  ⟨toStr⟩

/-- The format construction in `FFL.Meta.Litform`. -/
def format [Repr α] : Litform α → Format
  | ⊤ => s!"⊤"
  | ⊥ => s!"⊥"
  | atom a => repr a
  | ∼φ => s! "(¬{format φ})"
  | φ ⋏ ψ => s!"({(format φ)} ∧ {format ψ})"
  | φ ⋎ ψ => s!"({(format φ)} ∨ {format ψ})"
  | φ ⇒ₗ ψ => s!"({(format φ)} → {format ψ})"
  | iff φ ψ => s!"({(format φ)} ↔ {format ψ})"

instance [Repr α] : Repr (Litform α) :=
  ⟨fun t _ ↦ format t⟩

end ToString

variable (F : Q(Type*)) (ls : Q(LogicalConnective $F)) (ln : Q(LogicalNeutral $F))

/-- The Lit construction in `FFL.Meta`. -/
abbrev _root_.PointwiseComposition.FFL.Meta.Lit :=
  Litform Expr

variable {F}

/-- The to Expr construction in `FFL.Meta.Litform`. -/
abbrev toExpr : Lit → Q($F)
  |  atom e => e
  |       ⊤ => q(⊤)
  |       ⊥ => q(⊥)
  |   φ ⋏ ψ => q($(toExpr φ) ⋏ $(toExpr ψ))
  |   φ ⋎ ψ => q($(toExpr φ) ⋎ $(toExpr ψ))
  |      ∼φ => q(∼$(toExpr φ))
  |   φ ⇒ₗ ψ => q($(toExpr φ) ⇒ₗ $(toExpr ψ))
  | iff φ ψ => q($(toExpr φ) ⇔ₗ $(toExpr ψ))



/-- The summands At Depth construction in `FFL.Meta.Litform`. -/
def summandsAtDepth {α : Q(Type $u)} (inst : Q(Add $α)) :
    ℕ → Q($α) → MetaM (List Q($α))
  | 0, expression => return [expression]
  | depth + 1, expression => do
    match expression with
    | ~q($x + $y) =>
      return (← summandsAtDepth inst depth x) ++ (← summandsAtDepth inst depth y)
    | _ => return [expression]



/-- The summands construction in `FFL.Meta.Litform`. -/
def summands {α : Q(Type $u)} (inst : Q(Add $α)) (expression : Q($α)) : MetaM (List Q($α)) := do
  let expression ← instantiateMVars expression
  summandsAtDepth inst (expression.approxDepth.toNat + 1) expression

/-- The denote At Depth construction in `FFL.Meta.Litform`. -/
def denoteAtDepth : ℕ → Q($F) → MetaM Lit
  | 0, expression => return atom expression
  | depth + 1, expression => do
    match expression with
    | ~q(⊤) => return ⊤
    | ~q(⊥) => return ⊥
    | ~q($φ ⋏ $ψ) => return (← denoteAtDepth depth φ) ⋏ (← denoteAtDepth depth ψ)
    | ~q($φ ⋎ $ψ) => return (← denoteAtDepth depth φ) ⋎ (← denoteAtDepth depth ψ)
    | ~q($φ ⇒ₗ $ψ) => return (← denoteAtDepth depth φ) ⇒ₗ (← denoteAtDepth depth ψ)
    | ~q($φ ⇔ₗ $ψ) => return iff (← denoteAtDepth depth φ) (← denoteAtDepth depth ψ)
    | ~q(∼$φ) => return ∼(← denoteAtDepth depth φ)
    | _ => return atom expression



/-- Reify the input's structural depth, keeping any remaining subexpression atomic. -/
def denote (expression : Q($F)) : MetaM Lit := do
  let expression ← instantiateMVars expression
  denoteAtDepth ls ln (expression.approxDepth.toNat + 1) expression

/-- The complexity construction in `FFL.Meta.Litform`. -/
@[simp]
def complexity : Litform α → ℕ
  | atom _ => 0
  | ⊤ => 0
  | ⊥ => 0
  | φ ⋏ ψ => max φ.complexity ψ.complexity + 1
  | φ ⋎ ψ => max φ.complexity ψ.complexity + 1
  | ∼φ => φ.complexity + 1
  | φ ⇒ₗ ψ => max φ.complexity ψ.complexity + 1
  | iff φ ψ => max φ.complexity ψ.complexity + 1

end Litform

namespace Lit

/-- The DEq construction in `FFL.Meta.Lit`. -/
def DEq : Lit → Lit → MetaM Bool
  | .atom e, .atom e' => Lean.Meta.isDefEq e e'
  | ⊤, ⊤ => return true
  | ⊥, ⊥ => return true
  | ∼φ, ∼ψ => return (← DEq φ ψ)
  | φ₁ ⋏ ψ₁, φ₂ ⋏ ψ₂ => return (← DEq φ₁ φ₂) && (← DEq ψ₁ ψ₂)
  | φ₁ ⋎ ψ₁, φ₂ ⋎ ψ₂ => return (← DEq φ₁ φ₂) && (← DEq ψ₁ ψ₂)
  | φ₁ ⇒ₗ ψ₁, φ₂ ⇒ₗ ψ₂ => return (← DEq φ₁ φ₂) && (← DEq ψ₁ ψ₂)
  | .iff φ₁ ψ₁, .iff φ₂ ψ₂ => return (← DEq φ₁ φ₂) && (← DEq ψ₁ ψ₂)
  | _, _ => return false

/-- The d Mem construction in `FFL.Meta.Lit`. -/
def dMem (φ : Lit) (Δ : List Lit) : MetaM Bool :=
  Δ.foldrM (fun ψ ih ↦ return (← DEq φ ψ) || ih) false

/-- The d Subset List construction in `FFL.Meta.Lit`. -/
def dSubsetList (Γ Δ : List Lit) : MetaM Bool := do
  match Γ with
  | [] =>
    return true
  | φ :: Γ =>
    return (← φ.dMem Δ) && (← dSubsetList Γ Δ)

end Lit

end Meta
end FFL

end

end PointwiseComposition
