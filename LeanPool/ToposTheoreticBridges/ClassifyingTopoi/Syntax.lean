/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.ModelTheory.Syntax

/-!
# Geometric logic: syntax

Geometric formulas over a first-order language `L` (Mathlib's `FirstOrder.Language`), in a
context `Fin n` of free variables: they are built from equalities of terms and relation symbols
applied to terms by finite conjunction (`⊤` and binary `and`), disjunction indexed by an arbitrary
type in `Type w`, and existential quantification of the last variable of the context. A geometric
sequent `φ ⊢ ψ` is a pair of formulas in the same context, and a geometric theory is a set of
sequents.

## Main definitions

* `LeanPool.ClassifyingTopoi.GeometricFormula`: geometric formulas;
* `LeanPool.ClassifyingTopoi.GeometricFormula.bot`: the false formula, the empty disjunction;
* `LeanPool.ClassifyingTopoi.GeometricFormula.IsCoherent`: coherent formulas, whose disjunctions
  are all finite;
* `LeanPool.ClassifyingTopoi.Sequent`, `LeanPool.ClassifyingTopoi.GeometricTheory`;
* `LeanPool.ClassifyingTopoi.GeometricFormula.IsHorn`, `GeometricTheory.IsHorn`: Horn formulas
  (finite conjunctions of atomic formulas) and Horn theories;
* `LeanPool.ClassifyingTopoi.GeometricFormula.exs`: existential quantification of the last `m`
  variables.

## References

* P. T. Johnstone, *Sketches of an Elephant*, D1.1.
* O. Caramello, *Theories, Sites, Toposes*, 1.2.1 (Definitions 1.2.3–1.2.5).
-/

@[expose] public section

universe w u₁ u₂

namespace LeanPool.ClassifyingTopoi

/-- Geometric formulas over a first-order language `L` in the context `Fin n`: built
from atomic formulas by finite conjunction, disjunction indexed by a type in `Type w`, and
existential quantification of the last variable. -/
inductive GeometricFormula (L : FirstOrder.Language.{u₁, u₂}) :
    ℕ → Type (max u₁ u₂ (w + 1)) where
  /-- The true formula. -/
  | top {n : ℕ} : GeometricFormula L n
  /-- Binary conjunction. -/
  | and {n : ℕ} (φ ψ : GeometricFormula L n) : GeometricFormula L n
  /-- Disjunction of a family indexed by `ι : Type w`. -/
  | iSup {n : ℕ} {ι : Type w} (φ : ι → GeometricFormula L n) : GeometricFormula L n
  /-- Equality of two terms. -/
  | equal {n : ℕ} (t₁ t₂ : L.Term (Fin n)) : GeometricFormula L n
  /-- A relation symbol applied to terms. -/
  | rel {n k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (Fin n)) : GeometricFormula L n
  /-- Existential quantification of the last variable of the context `Fin (n + 1)`. -/
  | ex {n : ℕ} (φ : GeometricFormula L (n + 1)) : GeometricFormula L n

variable {L : FirstOrder.Language.{u₁, u₂}}

/-- The false formula: the disjunction of the empty family. -/
def GeometricFormula.bot {n : ℕ} : GeometricFormula.{w} L n :=
  .iSup (ι := PEmpty) PEmpty.elim

/-- Coherent formulas: geometric formulas whose disjunctions are all finite. -/
def GeometricFormula.IsCoherent : {n : ℕ} → GeometricFormula.{w} L n → Prop
  | _, .top => True
  | _, .and φ ψ => φ.IsCoherent ∧ ψ.IsCoherent
  | _, .iSup (ι := ι) φ => Finite ι ∧ ∀ i, (φ i).IsCoherent
  | _, .equal _ _ => True
  | _, .rel _ _ => True
  | _, .ex φ => φ.IsCoherent

/-- A geometric sequent `φ ⊢ ψ` in the context `Fin n`. -/
structure Sequent (L : FirstOrder.Language.{u₁, u₂}) where
  /-- The length of the context. -/
  n : ℕ
  /-- The hypothesis. -/
  lhs : GeometricFormula.{w} L n
  /-- The conclusion. -/
  rhs : GeometricFormula.{w} L n

variable (L) in
/-- A geometric theory: a set of geometric sequents. -/
abbrev GeometricTheory := Set (Sequent.{w} L)

/-- Horn formulas: finite conjunctions of atomic formulas. -/
def GeometricFormula.IsHorn : {n : ℕ} → GeometricFormula.{w} L n → Prop
  | _, .top => True
  | _, .and φ ψ => φ.IsHorn ∧ ψ.IsHorn
  | _, .iSup _ => False
  | _, .equal _ _ => True
  | _, .rel _ _ => True
  | _, .ex _ => False

/-- A Horn theory: every axiom is a sequent between Horn formulas. -/
def GeometricTheory.IsHorn (T : GeometricTheory.{w} L) : Prop :=
  ∀ σ ∈ T, σ.lhs.IsHorn ∧ σ.rhs.IsHorn

/-- Existential quantification of the last `m` variables of the context
`Fin (n + m)`. -/
def GeometricFormula.exs {n : ℕ} : {m : ℕ} → GeometricFormula.{w} L (n + m) →
    GeometricFormula.{w} L n
  | 0, φ => φ
  | m + 1, φ => exs (m := m) (.ex φ)

end LeanPool.ClassifyingTopoi
