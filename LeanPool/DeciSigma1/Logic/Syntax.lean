/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import Mathlib.Data.Nat.Notation

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Boolean combinations of existential and universal sentences

The first-order theory of subtyping has one binary relation, the subtype order `≤`, and the
term constructors of the signature. This module defines, for an arbitrary term language, the
fragment decided in this library: quantifier-free formulas built from inequalities `s ≤ t`
between terms, existential sentences `∃ x₀ … x_{m-1}, φ` with a quantifier-free body `φ`
(Σ₁ sentences), universal sentences `∀ x₀ … x_{m-1}, φ` (Π₁ sentences), and Boolean
combinations of these. Each quantifier block binds all the variables of its body.

A term language is a family `T V` of terms with variables in `V`. Its meaning is given by an
`Interpretation`: a domain, the value of a term under an assignment of its variables, and the
relation interpreting `≤`. Truth of a sentence is relative to a class of admissible values for
the variables, such as all trees, the regular trees or the finite trees. The two signatures of
this library instantiate the language in `DeciSigma1.Entailment.Logic` and
`DeciSigma1.Full.Logic`.

## Main declarations

- `Interpretation`, `Interpretation.TermClosed`: the domain, the evaluation of terms and the order
  relation, and the classes of values closed under the term language.
- `QuantifierFreeFormula`, `QuantifierFreeFormula.Holds`: quantifier-free formulas and their truth.
- `Sigma1`, `Sigma1.HoldsIn`: existential sentences and their truth in a class of values.
- `BooleanSentence`, `BooleanSentence.HoldsIn`: Boolean combinations of existential and
  universal sentences.
- `BooleanSentence.all_iff_not_ex_not`: a universal sentence is the negation of an existential
  one.
-/

@[expose] public section


namespace DeciSigma1.Logic

/-- An interpretation of the term language `T` in the domain `D`: the value of a term when its
variables have given values, and the relation interpreting `≤`. -/
structure Interpretation (T : Type → Type) (D : Type) where
  /-- The value of a term when its variables have the values `ρ`. -/
  eval {V : Type} : (V → D) → T V → D
  /-- The relation interpreting `≤`. -/
  le : D → D → Prop

/-- A class `C` of values is closed under the term language if every term takes a value in `C`
whenever its variables do. -/
def Interpretation.TermClosed {T : Type → Type} {D : Type} (I : Interpretation T D)
    (C : D → Prop) : Prop :=
  ∀ {V : Type} (ρ : V → D) (t : T V), (∀ v, C (ρ v)) → C (I.eval ρ t)

variable {T : Type → Type} {D V : Type}

/-- Quantifier-free formulas whose atoms are inequalities between terms with variables in
`V`. -/
inductive QuantifierFreeFormula (T : Type → Type) (V : Type) where
  /-- The inequality `s ≤ t`. -/
  | le (s t : T V)
  /-- The true formula. -/
  | tt
  /-- The false formula. -/
  | ff
  /-- Negation. -/
  | not (φ : QuantifierFreeFormula T V)
  /-- Conjunction. -/
  | and (φ ψ : QuantifierFreeFormula T V)
  /-- Disjunction. -/
  | or (φ ψ : QuantifierFreeFormula T V)

/-- The equality `s = t`, as the conjunction of `s ≤ t` and `t ≤ s`. -/
def QuantifierFreeFormula.eq (s t : T V) : QuantifierFreeFormula T V := .and (.le s t) (.le t s)

/-- Truth of a quantifier-free formula when its variables have the values `ρ`. -/
def QuantifierFreeFormula.Holds (I : Interpretation T D) (ρ : V → D) :
    QuantifierFreeFormula T V → Prop
  | .le s t => I.le (I.eval ρ s) (I.eval ρ t)
  | .tt => True
  | .ff => False
  | .not φ => ¬ φ.Holds I ρ
  | .and φ ψ => φ.Holds I ρ ∧ ψ.Holds I ρ
  | .or φ ψ => φ.Holds I ρ ∨ ψ.Holds I ρ

/-- The existential sentence `∃ x₀ … x_{m-1}, body` with `m = variableCount`. -/
structure Sigma1 (T : Type → Type) where
  /-- The number of bound variables. -/
  variableCount : ℕ
  /-- The quantifier-free body. -/
  body : QuantifierFreeFormula T (Fin variableCount)

/-- Truth of an existential sentence when the variables range over the class `C`. -/
def Sigma1.HoldsIn (I : Interpretation T D) (C : D → Prop) (s : Sigma1 T) : Prop :=
  ∃ ρ : Fin s.variableCount → D, (∀ v, C (ρ v)) ∧ s.body.Holds I ρ

/-- Boolean combinations of existential and universal sentences. -/
inductive BooleanSentence (T : Type → Type) where
  /-- The existential sentence `∃ x₀ … x_{m-1}, φ`. -/
  | ex (s : Sigma1 T)
  /-- The universal sentence `∀ x₀ … x_{m-1}, φ`, for `s = ⟨m, φ⟩`. -/
  | all (s : Sigma1 T)
  /-- Negation. -/
  | not (φ : BooleanSentence T)
  /-- Conjunction. -/
  | and (φ ψ : BooleanSentence T)
  /-- Disjunction. -/
  | or (φ ψ : BooleanSentence T)

/-- Truth of a sentence when the variables range over the class `C`. -/
def BooleanSentence.HoldsIn (I : Interpretation T D) (C : D → Prop) :
    BooleanSentence T → Prop
  | .ex s => s.HoldsIn I C
  | .all s => ∀ ρ : Fin s.variableCount → D, (∀ v, C (ρ v)) → s.body.Holds I ρ
  | .not φ => ¬ φ.HoldsIn I C
  | .and φ ψ => φ.HoldsIn I C ∧ ψ.HoldsIn I C
  | .or φ ψ => φ.HoldsIn I C ∨ ψ.HoldsIn I C

/-- `∀ x, φ` holds exactly when `∃ x, ¬ φ` fails. -/
theorem BooleanSentence.all_iff_not_ex_not (I : Interpretation T D) (C : D → Prop)
    (s : Sigma1 T) :
    (BooleanSentence.all s).HoldsIn I C ↔
        ¬ (Sigma1.mk s.variableCount (.not s.body)).HoldsIn I C := by
  simp [BooleanSentence.HoldsIn, Sigma1.HoldsIn, QuantifierFreeFormula.Holds]

end DeciSigma1.Logic
