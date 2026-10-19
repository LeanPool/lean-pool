/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.LE

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

/-!
# Preperations for arithmetic

- *NOTE*:
  To avoid the duplicate definitions of `Tarski.Structure ℒₒᵣ` for models,
  we basically use `ORingStructure`, and generated `standardStructure` instead of
  `Tarski.Structure ℒₒᵣ` itself.
-/

namespace FFL

/-- An interpretation of zero, one, addition, multiplication and strict order. -/
class ORingStructure (α : Type*) extends Zero α, One α, Add α, Mul α, LT α

instance [Zero α] [One α] [Add α] [Mul α] [LT α] : ORingStructure α where

namespace ORingStructure

variable {α : Type*} [ORingStructure α]

/-- The numeral construction in `FFL.ORingStructure`. -/
def numeral : ℕ → α
  | 0 => 0
  | 1 => 1
  | n + 2 => numeral (n + 1) + 1

@[simp]
lemma zero_eq_zero : (numeral 0 : α) = 0 :=
  rfl

@[simp]
lemma one_eq_one : (numeral 1 : α) = 1 :=
  rfl

end ORingStructure

@[simp]
lemma Nat.numeral_eq : (n : ℕ) → ORingStructure.numeral n = n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by simp [ORingStructure.numeral, Nat.numeral_eq (n + 1)]

namespace FirstOrder

/-- The Arithmetic Theory construction in `FFL.FirstOrder`. -/
abbrev ArithmeticTheory :=
  Theory ℒₒᵣ

/-- The Arithmetic Semiterm construction in `FFL.FirstOrder`. -/
abbrev ArithmeticSemiterm (ξ : Type*) (n : ℕ) :=
  Semiterm ℒₒᵣ ξ n

/-- The Arithmetic Term construction in `FFL.FirstOrder`. -/
abbrev ArithmeticTerm (ξ : Type*) :=
  Term ℒₒᵣ ξ

/-- The Arithmetic Semiformula construction in `FFL.FirstOrder`. -/
abbrev ArithmeticSemiformula (ξ : Type*) (n : ℕ) :=
  Semiformula ℒₒᵣ ξ n

/-- The Arithmetic Formula construction in `FFL.FirstOrder`. -/
abbrev ArithmeticFormula (ξ : Type*) :=
  Formula ℒₒᵣ ξ

/-- The Arithmetic Semisentence construction in `FFL.FirstOrder`. -/
abbrev ArithmeticSemisentence (n : ℕ) :=
  Semisentence ℒₒᵣ n

/-- The Arithmetic Sentence construction in `FFL.FirstOrder`. -/
abbrev ArithmeticSentence :=
  Sentence ℒₒᵣ

/-- The Arithmetic Semiproposition construction in `FFL.FirstOrder`. -/
abbrev ArithmeticSemiproposition (n : ℕ) :=
  Semiproposition ℒₒᵣ n

/-- The Arithmetic Proposition construction in `FFL.FirstOrder`. -/
abbrev ArithmeticProposition :=
  Proposition ℒₒᵣ

section ToString

variable {L : Language} [L.ORing]

variable [ToString ξ]

/-- The to String ORing construction in `FFL.FirstOrder.Semiterm`. -/
def Semiterm.toStringORing : ArithmeticSemiterm ξ n → String
  | #x => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x => "a_{" ++ toString x ++ "}"
  | func Language.Zero.zero _ => "0"
  | func Language.One.one _ => "1"
  | func Language.Add.add v => "(" ++ toStringORing (v 0) ++ " + " ++ toStringORing (v 1) ++ ")"
  | func Language.Mul.mul v =>
    "(" ++ toStringORing (v 0) ++ " \\cdot " ++ toStringORing (v 1) ++ ")"

instance : Repr (ArithmeticSemiterm ξ n) :=
  ⟨fun t _ ↦ t.toStringORing⟩

instance : ToString (ArithmeticSemiterm ξ n) :=
  ⟨Semiterm.toStringORing⟩

/-- The to String ORing construction in `FFL.FirstOrder.Semiformula`. -/
def Semiformula.toStringORing : ∀ {n}, ArithmeticSemiformula ξ n → String
  | _, ⊤ => "\\top"
  | _, ⊥ => "\\bot"
  | _, rel Language.Eq.eq v => (v 0).toStringORing ++ " = " ++ (v 1).toStringORing
  | _, rel Language.LT.lt v => (v 0).toStringORing ++ " < " ++ (v 1).toStringORing
  | _, nrel Language.Eq.eq v => (v 0).toStringORing ++ " \\not = " ++ (v 1).toStringORing
  | _, nrel Language.LT.lt v => (v 0).toStringORing ++ " \\not < " ++ (v 1).toStringORing
  | _, φ ⋏ ψ => "[" ++ φ.toStringORing ++ "]" ++ " \\land " ++ "[" ++ ψ.toStringORing ++ "]"
  | _, φ ⋎ ψ => "[" ++ φ.toStringORing ++ "]" ++ " \\lor " ++ "[" ++ ψ.toStringORing ++ "]"
  | n, ∀¹ (rel Language.LT.lt v ⇒ₗ φ) =>
    "(\\forall x_{" ++ toString n ++ "} < " ++ (v 1).toStringORing ++ ") " ++ "[" ++
        φ.toStringORing ++
      "]"
  | n, ∃¹ (rel Language.LT.lt v ⋏ φ) =>
    "(\\exists x_{" ++ toString n ++ "} < " ++ (v 1).toStringORing ++ ") " ++ "[" ++
        φ.toStringORing ++
      "]"
  | n, ∀¹ φ => "(\\forall x_{" ++ toString n ++ "}) " ++ "[" ++ φ.toStringORing ++ "]"
  | n, ∃¹ φ => "(\\exists x_{" ++ toString n ++ "}) " ++ "[" ++ φ.toStringORing ++ "]"

instance : Repr (ArithmeticSemiformula ξ n) :=
  ⟨fun φ _ ↦ φ.toStringORing⟩

instance : ToString (ArithmeticSemiformula ξ n) :=
  ⟨Semiformula.toStringORing⟩

end ToString

namespace Arithmetic

open Encodable Semiterm.Operator.GödelNumber

variable {α} [Encodable α]

instance : Semiterm.Operator.GödelNumber ℒₒᵣ α :=
  Semiterm.Operator.GödelNumber.ofEncodable

lemma gödelNumber_def (a : α) : gödelNumber a = Semiterm.Operator.encode ℒₒᵣ a :=
  rfl

lemma gödelNumber'_def (a : α) :
    (⌜a⌝ : ArithmeticSemiterm ξ n) = Semiterm.Operator.encode ℒₒᵣ a :=
  rfl

lemma gödelNumber'_eq_coe_encode (a : α) :
    (⌜a⌝ : ArithmeticSemiterm ξ n) = ↑(Encodable.encode a) :=
  rfl

@[simp]
lemma encode_encode_eq (a : α) :
    (gödelNumber (encode a) : Semiterm.Const ℒₒᵣ) = gödelNumber a := by
  simp [Semiterm.Operator.encode, gödelNumber_def]

@[simp]
lemma rew_gödelNumber' (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) (a : α) : ω ⌜a⌝ = ⌜a⌝ := by
  simp [gödelNumber'_def]

end Arithmetic

/-!
### Semantics of arithmetic  -/

/-- Data and laws for ORing in `FFL.FirstOrder.Tarski.Structure`. -/
class Tarski.Structure.ORing (L : Language) [L.ORing] (M : Type w) [ORingStructure M]
    [Tarski.Structure L M] extends Tarski.Structure.Zero L M, Tarski.Structure.One L M,
    Tarski.Structure.Add L M, Tarski.Structure.Mul L M, Tarski.Structure.Eq L M,
    Tarski.Structure.LT L M

attribute [instance] Tarski.Structure.ORing.mk

namespace Tarski
namespace Structure

open Semiterm Semiformula

variable [Operator.Zero L] [Operator.One L] [Operator.Add L] {M : Type u} [ORingStructure M]
  [Tarski.Structure L M] [Tarski.Structure.Zero L M] [Tarski.Structure.One L M]
  [Tarski.Structure.Add L M]

@[simp]
lemma numeral_eq_numeral :
    (z : ℕ) → (Semiterm.Operator.numeral L z).val ![] = (ORingStructure.numeral z : M)
  | 0 => by simp [ORingStructure.numeral, Semiterm.Operator.numeral_zero]
  | 1 => by simp [ORingStructure.numeral, Semiterm.Operator.numeral_one]
  | z + 2 => by
    simp [ORingStructure.numeral, Semiterm.Operator.numeral_add_two, Semiterm.Operator.val_comp,
      Matrix.fun_eq_vec_two, numeral_eq_numeral (z + 1)]

end Structure
end Tarski

namespace Semiformula

variable {L : Language} [L.LT] [L.Zero] [L.One] [L.Add]

/-- The ball LTSucc construction in `FFL.FirstOrder.Semiformula`. -/
def ballLTSucc (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  φ.ballLT (‘!!t + 1’)

/-- The bexs LTSucc construction in `FFL.FirstOrder.Semiformula`. -/
def bexsLTSucc (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  φ.bexsLT (‘!!t + 1’)

variable {M : Type*} {s : Tarski.Structure L M} [LT M] [One M] [Add M] [Tarski.Structure.LT L M]
  [Tarski.Structure.One L M] [Tarski.Structure.Add L M]

lemma eval_ballLTSucc {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} {fv bv} :
    (φ.ballLTSucc t).Eval (M := M) fv bv ↔
      ∀ x < t.val (M := M) fv bv + 1, φ.Eval (M := M) (x :> fv) bv :=
  by simp [ballLTSucc, Semiterm.Operator.numeral]

lemma eval_bexsLTSucc {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} {fv bv} :
    (φ.bexsLTSucc t).Eval (M := M) fv bv ↔
      ∃ x < t.val (M := M) fv bv + 1, φ.Eval (M := M) (x :> fv) bv :=
  by simp [bexsLTSucc, Semiterm.Operator.numeral]

end Semiformula

namespace BinderNotation

open _root_.Lean Lean PrettyPrinter Delaborator SubExpr

/-- The «first order formula∀ <⁺ , » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∀ " ident " <⁺ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula∃ <⁺ , » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∃ " ident " <⁺ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula

macro_rules
  | `(quoteformula(lit)[$binders* | $fbinders* | ∀ $x <⁺ $t, $φ]) => do
    if binders.elem x then
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let binders' := binders.insertIdx 0 x
      `(Semiformula.ballLTSucc quoteterm(lit)[$binders* | $fbinders* | $t]
            quoteformula(lit)[$binders'* | $fbinders* | $φ])
  | `(quoteformula(lit)[$binders* | $fbinders* | ∃ $x <⁺ $t, $φ]) => do
    if binders.elem x then
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let binders' := binders.insertIdx 0 x
      `(Semiformula.bexsLTSucc quoteterm(lit)[$binders* | $fbinders* | $t]
            quoteformula(lit)[$binders'* | $fbinders* | $φ])

end BinderNotation

end FirstOrder

end FFL

end

end PointwiseComposition
