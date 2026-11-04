/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.LJ.Head

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace FFL
namespace FirstOrder

variable {L : Language.{u}}

open Semiformulaᵢ

namespace LJ

/-- Data and laws for Derivation in `FFL.FirstOrder.LJ`. -/
inductive Derivation : Sequent L → Head L → Type _/-- Identity rule -/
  | identity (R : L.Rel k) (v) : Derivation ⦃rel R v⦄ (rel R v)/-- Cut rule -/
  |
  cut {φ : Propositionᵢ L} {Γ Δ Ξ} :
    Derivation Γ φ → Derivation (Δ + ⦃φ⦄) Ξ → Derivation (Γ + Δ) Ξ/--
Left contraction -/
  | contraction : Derivation (Γ + ⦃φ, φ⦄) Ξ → Derivation (Γ + ⦃φ⦄) Ξ/-- Left weakening -/
  | weakening : Derivation Γ Ξ → Derivation (Γ + ⦃φ⦄) Ξ/-- Right weakening -/
  | weakeningRight : Derivation Γ none → Derivation Γ (some φ)/--
Positive introduction of verum -/
  | verum : Derivation 0 (some ⊤)/-- Negative introduction of falsum -/
  | falsum : Derivation ⦃⊥⦄ none/-- Positive introduction of implication -/
  | positiveImply {φ ψ : Propositionᵢ L} : Derivation (Γ + ⦃φ⦄) ψ → Derivation Γ (φ ⇒ₗ ψ)/--
Negative introduction of implication -/
  |
  negativeImply {φ ψ : Propositionᵢ L} :
    Derivation Γ φ → Derivation (Δ + ⦃ψ⦄) Ξ → Derivation (Γ + Δ + ⦃φ ⇒ₗ ψ⦄) Ξ/--
Positive introduction of conjunction -/
  |
  positiveAnd {φ ψ : Propositionᵢ L} : Derivation Γ φ → Derivation Γ ψ → Derivation Γ (φ ⋏ ψ)/--
Negative introduction of conjunction -/
  |
  negativeAnd {φ ψ : Propositionᵢ L} : Derivation (Γ + ⦃φ, ψ⦄) Ξ → Derivation (Γ + ⦃φ ⋏ ψ⦄) Ξ/--
Positive introduction of disjunction (left) -/
  | positiveOrLeft {φ ψ : Propositionᵢ L} : Derivation Γ φ → Derivation Γ (φ ⋎ ψ)/--
Positive introduction of disjunction (right) -/
  | positiveOrRight {φ ψ : Propositionᵢ L} : Derivation Γ ψ → Derivation Γ (φ ⋎ ψ)/--
Negative introduction of disjunction -/
  | negativeOr : Derivation (Γ + ⦃φ⦄) Ξ → Derivation (Γ + ⦃ψ⦄) Ξ → Derivation (Γ + ⦃φ ⋎ ψ⦄) Ξ/--
Positive introduction of universal quantifier -/
  |
  positiveForall {φ : Semipropositionᵢ L 1} :
    Derivation Γ⁺ (Rewriting.free φ) → Derivation Γ (∀¹ φ)/--
Negative introduction of universal quantifier -/
  |
  negativeForall {φ : Semipropositionᵢ L 1} {t : Term L ℕ} :
    Derivation (Γ + ⦃φ/[t]⦄) Ξ → Derivation (Γ + ⦃∀¹ φ⦄) Ξ/--
Positive introduction of existential quantifier -/
  |
  positiveExists {φ : Semipropositionᵢ L 1} {t : Term L ℕ} :
    Derivation Γ (φ/[t]) → Derivation Γ (∃¹ φ)/--
Negative introduction of existential quantifier -/
  |
  negativeExists {φ : Semipropositionᵢ L 1} :
    Derivation (Γ⁺ + ⦃Rewriting.free φ⦄) Ξ.shift → Derivation (Γ + ⦃∃¹ φ⦄) Ξ

/-- The «term ⊢ᴸᴶ¹ » construction in `FFL.FirstOrder.LJ`. -/
infix:45 " ⊢ᴸᴶ¹ " => Derivation

namespace Derivation

variable {Γ Δ : Sequent L} {Ξ Λ : Head L}

open Rewriting LawfulSyntacticRewriting

/-- The cast construction in `FFL.FirstOrder.LJ.Derivation`. -/
def cast (d : Γ ⊢ᴸᴶ¹ Ξ) (seq : Γ = Δ := by abel) (heq : Ξ = Λ := by simp) : Δ ⊢ᴸᴶ¹ Λ :=
  seq ▸ heq ▸ d

instance : Structural (fun Γ ↦ Γ ⊢ᴸᴶ¹ Ξ)
    where
  weakening d := d.weakening
  contraction d := d.contraction

/-- The traversal construction in `FFL.FirstOrder.LJ.Derivation`. -/
def traversal [L.DecidableEq] {Γ : Sequent L} {Ξ : Head L} :
    Γ ⊢ᴸᴶ¹ Ξ → (PointwiseComposition.Multiset.Traversal Γ)
  | identity R v => .atom (Semiformulaᵢ.rel R v)
  | cut d e => d.traversal.add e.traversal.remove
  | contraction (φ := φ) d => (d.traversal.cast (by abel)).remove (a := φ)
  | weakening (φ := φ) d => d.traversal.succ φ
  | weakeningRight d => d.traversal
  | verum => .zero
  | falsum => .atom ⊥
  | positiveImply d => d.traversal.remove
  | negativeImply (φ := φ) (ψ := ψ) d e => (d.traversal.add e.traversal.remove).succ (φ ⇒ₗ ψ)
  | positiveAnd d _ => d.traversal
  | negativeAnd (φ := φ) (ψ := ψ) d =>
    ((d.traversal.cast (by abel)).remove (a := ψ)).remove (a := φ) |>.succ (φ ⋏ ψ)
  | positiveOrLeft d => d.traversal
  | positiveOrRight d => d.traversal
  | negativeOr (φ := φ) (ψ := ψ) d _ => d.traversal.remove.succ (φ ⋎ ψ)
  | positiveForall d =>
    (d.traversal.map (Rew.rewriteMap Nat.pred ▹ ·)).cast
      (by simp [Rewriting.shifts, Multiset.map_map, Rewriting.rewriteMap_pred_shift])
  | negativeForall (φ := φ) d => d.traversal.remove.succ (∀¹ φ)
  | positiveExists d => d.traversal
  | negativeExists (φ := φ) d =>
    ((d.traversal.remove.map (Rew.rewriteMap Nat.pred ▹ ·)).cast
          (by simp [Rewriting.shifts, Multiset.map_map, Rewriting.rewriteMap_pred_shift])).succ
      (∃¹ φ)

/-- The contra construction in `FFL.FirstOrder.LJ.Derivation`. -/
def contra [L.DecidableEq] (d : Γ ⊢ᴸᴶ¹ Ξ) (t : (PointwiseComposition.Multiset.Traversal Δ))
    (h : Γ ⊆ Δ := by simp) : Δ ⊢ᴸᴶ¹ Ξ :=
  Structural.ofSubset (F := Propositionᵢ L) (𝔇 := fun Γ ↦ Γ ⊢ᴸᴶ¹ Ξ) (Γ := Γ) (Δ := Δ)
    d.traversal t d h

/-- The eta construction in `FFL.FirstOrder.LJ.Derivation`. -/
def eta : (φ : Propositionᵢ L) → ⦃φ⦄ ⊢ᴸᴶ¹ φ
  | .rel R v => identity R v
  | ⊥ => falsum.weakeningRight
  | φ ⋏ ψ =>
    positiveAnd
      (cast
        (negativeAnd (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := φ) <|
          ((eta φ).weakening (φ := ψ)).cast (by simp)))
      (cast
        (negativeAnd (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := ψ) <|
          ((eta ψ).weakening (φ := φ)).cast (by simp [add_comm])))
  | φ ⋎ ψ =>
    negativeOr (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := φ ⋎ ψ) (cast (positiveOrLeft (ψ := ψ) (eta φ)))
      (cast (positiveOrRight (φ := φ) (eta ψ)))
  | φ ⇒ₗ ψ =>
    positiveImply <|
      cast
        (negativeImply (φ := φ) (ψ := ψ) (Δ := 0) (Ξ := ψ) (eta φ)
          (cast (eta ψ) (by simp) (by simp)))
  | ∀¹ φ =>
    positiveForall (Γ := ⦃∀¹ φ⦄) <|
      cast
        (negativeForall (Γ := 0) (Ξ := Rewriting.free φ) (φ := Rewriting.shift φ) (t := &0) <|
          cast (eta (Rewriting.free φ)) (by simp) (by simp))
        (by simp)
  | ∃¹ φ =>
    negativeExists (Γ := 0) (Ξ := ∃¹ φ) <|
      cast
        (positiveExists (Γ := ⦃Rewriting.free φ⦄) (φ := Rewriting.shift φ) (t := &0) <|
          cast (eta (Rewriting.free φ)) (by simp) (by simp))
termination_by φ => φ.complexity

/-- The assumption construction in `FFL.FirstOrder.LJ.Derivation`. -/
def assumption [L.DecidableEq] {φ : Propositionᵢ L}
    (t : (PointwiseComposition.Multiset.Traversal Γ)) (h : φ ∈ Γ) : Γ ⊢ᴸᴶ¹ φ :=
  (eta φ).contra t (by simpa using h)

/-- The positive Neg construction in `FFL.FirstOrder.LJ.Derivation`. -/
def positiveNeg {φ : Propositionᵢ L} (d : Γ + ⦃φ⦄ ⊢ᴸᴶ¹ (⊥ : Propositionᵢ L)) :
    Γ ⊢ᴸᴶ¹ (∼φ : Propositionᵢ L) :=
  positiveImply d

/-- The negative Neg construction in `FFL.FirstOrder.LJ.Derivation`. -/
def negativeNeg {φ : Propositionᵢ L} (d : Γ ⊢ᴸᴶ¹ φ) : Γ + ⦃(∼φ : Propositionᵢ L)⦄ ⊢ᴸᴶ¹ none :=
  cast (seq := by rw [add_zero]; rfl) <|
    negativeImply (φ := φ) (ψ := ⊥) (Γ := Γ) (Δ := 0) (Ξ := none) d <|
      cast falsum (by simp) (by rfl)

/-- The modus Ponens construction in `FFL.FirstOrder.LJ.Derivation`. -/
def modusPonens [L.DecidableEq] {φ ψ : Propositionᵢ L} (di : Γ ⊢ᴸᴶ¹ φ ⇒ₗ ψ) (dφ : Γ ⊢ᴸᴶ¹ φ) :
    Γ ⊢ᴸᴶ¹ ψ :=
  have d : Γ + Γ ⊢ᴸᴶ¹ ψ :=
    cut (φ := φ ⇒ₗ ψ) (Γ := Γ) (Δ := Γ) (Ξ := ψ) di <|
      cast (seq := by simp) <|
        negativeImply (φ := φ) (ψ := ψ) (Γ := Γ) (Δ := 0) (Ξ := ψ) dφ
          (cast (eta ψ) (by simp) (by simp))
  cast
    (Structural.contractMany (F := Propositionᵢ L) (𝔇 := fun Δ ↦ Δ ⊢ᴸᴶ¹ (some ψ)) (Δ := 0)
      di.traversal (cast d (by simp) (by rfl)))
    (by simp)

/-- The neg Elim construction in `FFL.FirstOrder.LJ.Derivation`. -/
def negElim [L.DecidableEq] {φ : Propositionᵢ L} (dn : Γ ⊢ᴸᴶ¹ (∼φ : Propositionᵢ L))
    (dφ : Γ ⊢ᴸᴶ¹ φ) : Γ ⊢ᴸᴶ¹ (⊥ : Propositionᵢ L) :=
  modusPonens dn dφ

/-- The cut One construction in `FFL.FirstOrder.LJ.Derivation`. -/
def cutOne {φ : Propositionᵢ L} (dφ : Γ ⊢ᴸᴶ¹ φ) (d : ⦃φ⦄ ⊢ᴸᴶ¹ Ξ) : Γ ⊢ᴸᴶ¹ Ξ :=
  cast (seq := by simp) <| cut (Γ := Γ) (Δ := 0) (Ξ := Ξ) dφ <| cast d (by simp)

/-- The and Left construction in `FFL.FirstOrder.LJ.Derivation`. -/
def andLeft {φ ψ : Propositionᵢ L} (d : Γ ⊢ᴸᴶ¹ φ ⋏ ψ) : Γ ⊢ᴸᴶ¹ φ :=
  cutOne d <|
    cast <|
      negativeAnd (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := φ) <|
        ((eta φ).weakening (φ := ψ)).cast (by simp)

/-- The and Right construction in `FFL.FirstOrder.LJ.Derivation`. -/
def andRight {φ ψ : Propositionᵢ L} (d : Γ ⊢ᴸᴶ¹ φ ⋏ ψ) : Γ ⊢ᴸᴶ¹ ψ :=
  cutOne d <|
    cast <|
      negativeAnd (Γ := 0) (φ := φ) (ψ := ψ) (Ξ := ψ) <|
        ((eta ψ).weakening (φ := φ)).cast (by simp [add_comm])

/-- The specialize construction in `FFL.FirstOrder.LJ.Derivation`. -/
def specialize {φ : Semipropositionᵢ L 1} (d : Γ ⊢ᴸᴶ¹ ∀¹ φ) (t : Term L ℕ) : Γ ⊢ᴸᴶ¹ φ/[t] :=
  cutOne d <|
    cast <|
      negativeForall (Γ := 0) (Ξ := φ/[t]) (φ := φ) (t := t) <| (eta (φ/[t])).cast (by simp)

/-- The rewrite construction in `FFL.FirstOrder.LJ.Derivation`. -/
def rewrite (f : ℕ → SyntacticTerm L) {Γ : Sequent L} {Ξ : Head L} :
    Γ ⊢ᴸᴶ¹ Ξ → Γ.map (Rew.rewrite f ▹ ·) ⊢ᴸᴶ¹ Head.rewrite f Ξ
  | identity R v => identity R (Rew.rewrite f ∘ v)
  | cut (φ := φ) (Γ := Γ) (Δ := Δ) dφ d =>
    (cut (φ := Rew.rewrite f ▹ φ) (Γ := Γ.map (Rew.rewrite f ▹ ·)) (Δ :=
          Δ.map (Rew.rewrite f ▹ ·)) (Ξ := Head.rewrite f Ξ) ((rewrite f dφ).cast)
          ((rewrite f d).cast (by simp))).cast
      (by simp)
  | contraction (Γ := Γ) (φ := φ) (Ξ := Ξ) d =>
    (contraction (Γ := Γ.map (Rew.rewrite f ▹ ·)) (φ := Rew.rewrite f ▹ φ) (Ξ :=
          Head.rewrite f Ξ) ((rewrite f d).cast (by simp) (by cases Ξ <;> rfl))).cast
      (by simp) (by cases Ξ <;> rfl)
  | weakening (Γ := Γ) (φ := φ) (Ξ := Ξ) d =>
    (weakening (Γ := Γ.map (Rew.rewrite f ▹ ·)) (φ := Rew.rewrite f ▹ φ) (Ξ := Head.rewrite f Ξ)
          (rewrite f d)).cast
      (by simp) (by cases Ξ <;> rfl)
  | weakeningRight (φ := φ) d =>
    ((rewrite f d).weakeningRight (φ := Rew.rewrite f ▹ φ)).cast (by simp)
  | verum => verum
  | falsum => falsum
  | positiveImply (Γ := Γ) (φ := φ) (ψ := ψ) d =>
    (positiveImply (Γ := Γ.map (Rew.rewrite f ▹ ·)) (φ := Rew.rewrite f ▹ φ) (ψ :=
          Rew.rewrite f ▹ ψ) ((rewrite f d).cast (by simp))).cast
      (by simp)
  | negativeImply (Γ := Γ) (Δ := Δ) (φ := φ) (ψ := ψ) dφ dψ =>
    (negativeImply (Γ := Γ.map (Rew.rewrite f ▹ ·)) (Δ := Δ.map (Rew.rewrite f ▹ ·)) (Ξ :=
          Head.rewrite f Ξ) (φ := Rew.rewrite f ▹ φ) (ψ := Rew.rewrite f ▹ ψ)
          (rewrite f dφ).cast ((rewrite f dψ).cast (by simp))).cast
      (by simp)
  | positiveAnd dφ dψ => positiveAnd (rewrite f dφ) (rewrite f dψ)
  | negativeAnd (Γ := Γ) (φ := φ) (ψ := ψ) d =>
    (negativeAnd (Γ := Γ.map (Rew.rewrite f ▹ ·)) (Ξ := Head.rewrite f Ξ) (φ :=
          Rew.rewrite f ▹ φ) (ψ := Rew.rewrite f ▹ ψ) ((rewrite f d).cast (by simp))).cast
      (by simp)
  | positiveOrLeft d => positiveOrLeft (rewrite f d)
  | positiveOrRight d => positiveOrRight (rewrite f d)
  | negativeOr (Γ := Γ) (φ := φ) (ψ := ψ) dφ dψ =>
    (negativeOr (Γ := Γ.map (Rew.rewrite f ▹ ·)) (Ξ := Head.rewrite f Ξ) (φ :=
          Rew.rewrite f ▹ φ) (ψ := Rew.rewrite f ▹ ψ) ((rewrite f dφ).cast (by simp))
          ((rewrite f dψ).cast (by simp))).cast
      (by simp)
  | positiveForall (Γ := Γ) (φ := φ) d =>
    let g : ℕ → SyntacticTerm L := &0 :>ₙ fun x ↦ Rew.shift (f x)
    (positiveForall (Γ := Γ.map (Rew.rewrite f ▹ ·)) (φ := Rew.rewrite (Rew.bShift ∘ f) ▹ φ) <|
        (rewrite g d).cast (by simp [g, Rewriting.shifts, shift_rewrite_eq])
          (by simp [g, Head.rewrite, free_rewrite_eq, Function.comp_def])) |>.cast
      (by simp) (by simp [Head.rewrite, Rew.q_rewrite])
  | negativeForall (Γ := Γ) (φ := φ) (t := t) d =>
    (negativeForall (Γ := Γ.map (Rew.rewrite f ▹ ·)) (Ξ := Head.rewrite f Ξ) (φ :=
          Rew.rewrite (Rew.bShift ∘ f) ▹ φ) (t := Rew.rewrite f t)
          ((rewrite f d).cast (by simp [rewrite_subst_eq]))).cast
      (by simp [Rew.q_rewrite])
  | positiveExists (φ := φ) (t := t) d =>
    (positiveExists (Γ := Γ.map (Rew.rewrite f ▹ ·)) (φ := Rew.rewrite (Rew.bShift ∘ f) ▹ φ)
          (t := Rew.rewrite f t) ((rewrite f d).cast (heq := by simp [rewrite_subst_eq]))).cast
      (heq := by simp [Head.rewrite, Rew.q_rewrite])
  | negativeExists (Γ := Γ) (Ξ := Ξ) (φ := φ) d =>
    let g : ℕ → SyntacticTerm L := &0 :>ₙ fun x ↦ Rew.shift (f x)
    (negativeExists (Γ := Γ.map (Rew.rewrite f ▹ ·)) (Ξ := Head.rewrite f Ξ) (φ :=
          Rew.rewrite (Rew.bShift ∘ f) ▹ φ) <|
        (rewrite g d).cast
          (by simp [g, Rewriting.shifts, free_rewrite_eq, shift_rewrite_eq, Function.comp_def])
          (by cases Ξ <;> simp [g, Head.rewrite, Head.shift, shift_rewrite_eq])) |>.cast
      (by simp [Rew.q_rewrite])

/-- Height of an LJ derivation, with initial rules at height zero (standard definition). -/
def height {Γ : Sequent L} {Ξ : Head L} : Γ ⊢ᴸᴶ¹ Ξ → ℕ
  | identity _ _ => 0
  | cut d₁ d₂ => max (height d₁) (height d₂) + 1
  | contraction d => height d + 1
  | weakening d => height d + 1
  | weakeningRight d => height d + 1
  | verum => 0
  | falsum => 0
  | positiveImply d => height d + 1
  | negativeImply d₁ d₂ => max (height d₁) (height d₂) + 1
  | positiveAnd d₁ d₂ => max (height d₁) (height d₂) + 1
  | negativeAnd d => height d + 1
  | positiveOrLeft d => height d + 1
  | positiveOrRight d => height d + 1
  | negativeOr d₁ d₂ => max (height d₁) (height d₂) + 1
  | positiveForall d => height d + 1
  | negativeForall d => height d + 1
  | positiveExists d => height d + 1
  | negativeExists d => height d + 1

/-- Transport along sequent equalities preserves height (routine). -/
@[simp]
lemma height_cast {Γ Δ : Sequent L} {Ξ Λ : Head L} (d : Γ ⊢ᴸᴶ¹ Ξ) (hΓ : Γ = Δ) (hΞ : Ξ = Λ) :
    height (d.cast hΓ hΞ) = height d := by
  subst Δ
  subst Λ
  rfl

/-- Term substitution preserves derivation height (standard syntactic property). -/
@[simp]
lemma height_rewrite (f : ℕ → SyntacticTerm L) {Γ : Sequent L} {Ξ : Head L} (d : Γ ⊢ᴸᴶ¹ Ξ) :
    height (d.rewrite f) = height d :=
  by
  induction d generalizing f <;> simp only [LJ.Derivation.rewrite, height, height_cast]
  case positiveAnd a b iha ihb => exact congrArg (· + 1) <| congrArg₂ max (iha f) (ihb f)
  all_goals aesop

/-- The map construction in `FFL.FirstOrder.LJ.Derivation`. -/
protected def map (d : Γ ⊢ᴸᴶ¹ Ξ) (f : ℕ → ℕ) :
    Γ.map (Rew.rewriteMap f ▹ ·) ⊢ᴸᴶ¹ Ξ.map (Rew.rewriteMap f ▹ ·) :=
  d.rewrite fun x ↦ &(f x)

/-- The shift construction in `FFL.FirstOrder.LJ.Derivation`. -/
protected def shift (d : Γ ⊢ᴸᴶ¹ Ξ) : Γ⁺ ⊢ᴸᴶ¹ Ξ.shift :=
  cast (d.map Nat.succ) (by rfl) (by cases Ξ <;> rfl)

/-- The dni construction in `FFL.FirstOrder.LJ.Derivation`. -/
def dni {φ : Propositionᵢ L} (d : Γ ⊢ᴸᴶ¹ φ) : Γ ⊢ᴸᴶ¹ (∼∼φ : Propositionᵢ L) :=
  positiveNeg d.negativeNeg.weakeningRight

/-- Contraposition for singleton derivations (standard intuitionistic reasoning). -/
def contrapose {φ ψ : Propositionᵢ L} (d : ⦃φ⦄ ⊢ᴸᴶ¹ ψ) : ⦃∼ψ⦄ ⊢ᴸᴶ¹ (∼φ : Propositionᵢ L) :=
  positiveNeg <| d.negativeNeg.weakeningRight.cast (heq := rfl)

/-- Double negation preserves derivability, by twice applying contraposition (folklore). -/
def doubleNegationMap {φ ψ : Propositionᵢ L} (d : ⦃φ⦄ ⊢ᴸᴶ¹ ψ) :
    ⦃∼∼φ⦄ ⊢ᴸᴶ¹ (∼∼ψ : Propositionᵢ L) :=
  d.contrapose.contrapose

/-- The dne Of Negative construction in `FFL.FirstOrder.LJ.Derivation`. -/
def dneOfNegative : {φ : Propositionᵢ L} → φ.IsNegative → ⦃∼∼φ⦄ ⊢ᴸᴶ¹ φ
  | ⊥, _ =>
    ((positiveNeg (Γ := 0) (φ := ⊥) ((eta ⊥).cast (by simp))).negativeNeg.weakeningRight).cast
      (heq := rfl)
  | φ ⋏ ψ, h =>
    have hn : φ.IsNegative ∧ ψ.IsNegative := by simpa using h
    positiveAnd (cutOne (doubleNegationMap (andLeft (eta _))) (dneOfNegative hn.1))
      (cutOne (doubleNegationMap (andRight (eta _))) (dneOfNegative hn.2))
  | φ ⇒ₗ ψ, h => by
    have ihψ := dneOfNegative (φ := ψ) (by simpa using h)
    let d₁ : ⦃φ⦄ + ⦃φ ⇒ₗ ψ⦄ ⊢ᴸᴶ¹ ψ :=
      negativeImply (Δ := 0) (eta φ) ((eta ψ).cast (by simp) rfl) |>.cast (heq := rfl)
    let d₂ : ⦃φ, ∼ψ⦄ ⊢ᴸᴶ¹ (∼(φ ⇒ₗ ψ) : Propositionᵢ L) :=
      positiveNeg <| d₁.negativeNeg.weakeningRight.cast (heq := rfl)
    let d₃ : ⦃∼∼(φ ⇒ₗ ψ), φ⦄ ⊢ᴸᴶ¹ (∼∼ψ : Propositionᵢ L) :=
      positiveNeg <| d₂.negativeNeg.weakeningRight.cast (heq := rfl)
    exact positiveImply (cutOne d₃ ihψ)
  | ∀¹ φ, h =>
    positiveForall <|
      cutOne
        (cast (doubleNegationMap (specialize (eta (∀¹ Rewriting.shift φ)) &0))
          (by simp [Semiformulaᵢ.neg_def]) (by simp))
        (dneOfNegative (by simpa using h))
termination_by φ _ => φ.complexity

/-- The of DNOf Negative construction in `FFL.FirstOrder.LJ.Derivation`. -/
def ofDNOfNegative {φ : Propositionᵢ L} (d : Γ ⊢ᴸᴶ¹ (∼∼φ : Propositionᵢ L)) (h : φ.IsNegative) :
    Γ ⊢ᴸᴶ¹ φ :=
  cutOne d (dneOfNegative h)

/-- Mutual LJ derivability from singleton antecedents. -/
abbrev InterDerivation (L : Language.{u}) (φ ψ : Propositionᵢ L) :=
  (⦃φ⦄ ⊢ᴸᴶ¹ ψ) × (⦃ψ⦄ ⊢ᴸᴶ¹ φ)

namespace InterDerivation

variable {φ ψ χ φ₁ φ₂ ψ₁ ψ₂ : Propositionᵢ L}

/-- The refl construction in `FFL.FirstOrder.LJ.Derivation.InterDerivation`. -/
protected def refl (φ : Propositionᵢ L) : InterDerivation L φ φ :=
  ⟨eta φ, eta φ⟩

/-- The symm construction in `FFL.FirstOrder.LJ.Derivation.InterDerivation`. -/
def symm (d : InterDerivation L φ ψ) : InterDerivation L ψ φ :=
  ⟨d.2, d.1⟩

/-- The trans construction in `FFL.FirstOrder.LJ.Derivation.InterDerivation`. -/
def trans (d₁ : InterDerivation L φ ψ) (d₂ : InterDerivation L ψ χ) : InterDerivation L φ χ :=
  ⟨cutOne d₁.1 d₂.1, cutOne d₂.2 d₁.2⟩

/-- The neg construction in `FFL.FirstOrder.LJ.Derivation.InterDerivation`. -/
def neg (d : InterDerivation L φ ψ) : InterDerivation L (∼φ) (∼ψ) :=
  ⟨contrapose d.2, contrapose d.1⟩

/-- The and construction in `FFL.FirstOrder.LJ.Derivation.InterDerivation`. -/
def and (dφ : InterDerivation L φ₁ φ₂) (dψ : InterDerivation L ψ₁ ψ₂) :
    InterDerivation L (φ₁ ⋏ ψ₁) (φ₂ ⋏ ψ₂) :=
  by
  constructor
  · exact positiveAnd (cutOne (andLeft (eta _)) dφ.1) (cutOne (andRight (eta _)) dψ.1)
  · exact positiveAnd (cutOne (andLeft (eta _)) dφ.2) (cutOne (andRight (eta _)) dψ.2)

/-- The all construction in `FFL.FirstOrder.LJ.Derivation.InterDerivation`. -/
def all {φ ψ : Semipropositionᵢ L 1}
    (d : InterDerivation L (Rewriting.free φ) (Rewriting.free ψ)) :
    InterDerivation L (∀¹ φ) (∀¹ ψ) :=
  by
  let lift :
    ∀ {φ ψ : Semipropositionᵢ L 1},
      (⦃Rewriting.free φ⦄ ⊢ᴸᴶ¹ Rewriting.free ψ) → ⦃∀¹ φ⦄ ⊢ᴸᴶ¹ ∀¹ ψ :=
    fun {φ ψ} d ↦
    positiveForall <|
      cutOne (cast (specialize (eta (∀¹ Rewriting.shift φ)) &0) (by simp) (by simp)) d
  exact ⟨lift d.1, lift d.2⟩

/-- The dne construction in `FFL.FirstOrder.LJ.Derivation.InterDerivation`. -/
def dne (h : φ.IsNegative) : InterDerivation L (∼∼φ) φ :=
  ⟨dneOfNegative h, dni (eta φ)⟩

/-- The iffneg Of Neg Iff construction in `FFL.FirstOrder.LJ.Derivation.InterDerivation`. -/
def iffnegOfNegIff (h : φ.IsNegative) (d : InterDerivation L (∼φ) ψ) :
    InterDerivation L φ (∼ψ) :=
  (dne h).symm.trans d.neg

end InterDerivation

end Derivation

end LJ

/-- Data and laws for LJ in `FFL.FirstOrder`. -/
inductive LJ (L : Language.{u})
  | symbol

/-- The «term𝐋𝐉¹» construction in `FFL.FirstOrder`. -/
notation "𝐋𝐉¹" => LJ.symbol

/-- The «term𝐋𝐉¹[ ]» construction in `FFL.FirstOrder`. -/
notation "𝐋𝐉¹[" L "]" => LJ.symbol (L := L)

/-- The Proof construction in `FFL.FirstOrder.LJ`. -/
abbrev LJ.Proof (φ : Propositionᵢ L) :=
  0 ⊢ᴸᴶ¹ some φ

instance : Entailment (LJ L) (Propositionᵢ L) where Prf _ := LJ.Proof

namespace LJ

namespace Proof

lemma def_eq (φ : Propositionᵢ L) : (𝐋𝐉¹ ⊢! φ) = (0 ⊢ᴸᴶ¹ some φ) :=
  rfl

end Proof

end LJ

/-- Data and laws for Proof in `FFL.FirstOrder.Theoryᵢ`. -/
structure Theoryᵢ.Proof (T : Theoryᵢ L) (σ : Sentenceᵢ L) where
  /-- The axioms construction in `FFL.FirstOrder.Theoryᵢ.Proof`. -/
  axioms : Multiset (Sentenceᵢ L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
  /-- The derivation construction in `FFL.FirstOrder.Theoryᵢ.Proof`. -/
  derivation : axioms.map Rewriting.emb ⊢ᴸᴶ¹ ↑σ

instance : Entailment (Theoryᵢ L) (Sentenceᵢ L) :=
  ⟨Theoryᵢ.Proof⟩

namespace Theoryᵢ
namespace Proof

variable {T U : Theoryᵢ L} [L.DecidableEq]

/-- The weakening construction in `FFL.FirstOrder.Theoryᵢ.Proof`. -/
def weakening (ss : T ⊆ U) : T ⊢! σ → U ⊢! σ
  | ⟨Γ, hΓ, d⟩ => ⟨Γ, fun ψ hψ ↦ ss (hΓ ψ hψ), d⟩

instance : Entailment.Axiomatized (Theoryᵢ L)
    where
  prfAxm {T} φ
    h :=
    ⟨⦃φ⦄, by simpa using AdjunctiveSet.mem_set_iff.mp h,
      LJ.Derivation.cast (LJ.Derivation.eta (φ : Propositionᵢ L)) (by simp)⟩
  weakening := weakening

/-- The deduct construction in `FFL.FirstOrder.Theoryᵢ.Proof`. -/
def deduct : adjoin φ T ⊢! ψ → T ⊢! φ ⇒ₗ ψ
  | ⟨Γ, hΓ, d⟩ =>
    ⟨Γ.filter (· ≠ φ), by
      intro θ hθ
      have hθΓ : θ ∈ Γ := (Multiset.mem_filter.mp hθ).1
      have hθφ : θ ≠ φ := (Multiset.mem_filter.mp hθ).2
      simpa [hθφ] using hΓ θ hθΓ,
      LJ.Derivation.cast (heq := by rfl) <|
        LJ.Derivation.positiveImply (φ := (φ : Propositionᵢ L)) (ψ := (ψ : Propositionᵢ L)) <|
          LJ.Derivation.contra d
            (((d.traversal.filter (· ≠ (φ : Propositionᵢ L))).cast
                  (by simp [Multiset.filter_map, Rewriting.emb_injective.eq_iff])).succ
              (φ : Propositionᵢ L))
            (by
              intro θ hθ
              rcases Multiset.mem_map.mp hθ with ⟨χ, hχ, rfl⟩
              by_cases h : χ = φ
              · subst χ
                simp
              · exact
                  Multiset.mem_add.mpr <|
                    Or.inl <|
                      Multiset.mem_map_of_mem Rewriting.emb <| Multiset.mem_filter_of_mem hχ h)⟩

/-- The deduct Inv construction in `FFL.FirstOrder.Theoryᵢ.Proof`. -/
def deductInv : T ⊢! φ ⇒ₗ ψ → adjoin φ T ⊢! ψ
  | ⟨Γ, hΓ, d⟩ =>
    ⟨Γ + ⦃φ⦄, by
      intro θ hθ
      rcases Multiset.mem_add.mp hθ with hθ | hθ
      · exact Set.mem_insert_of_mem φ (hΓ θ hθ)
      · exact Or.inl (by simpa using hθ),
      LJ.Derivation.cast (seq := by simp) (heq := by rfl) <|
        LJ.Derivation.cut (φ := ((φ : Propositionᵢ L) ⇒ₗ (ψ : Propositionᵢ L))) (Γ :=
          Γ.map Rewriting.emb) (Δ := ⦃(φ : Propositionᵢ L)⦄) (Ξ := (ψ : Propositionᵢ L))
          (LJ.Derivation.cast d (heq := by rfl))
          (LJ.Derivation.cast (heq := rfl) <|
            LJ.Derivation.negativeImply (φ := (φ : Propositionᵢ L)) (ψ := (ψ : Propositionᵢ L))
              (Γ := ⦃(φ : Propositionᵢ L)⦄) (Δ := 0) (Ξ := (ψ : Propositionᵢ L))
              (LJ.Derivation.eta (φ : Propositionᵢ L))
              (LJ.Derivation.cast (LJ.Derivation.eta (ψ : Propositionᵢ L)) (by simp)
                (by simp)))⟩

instance : Entailment.Deduction (Theoryᵢ L)
    where
  ofInsert := deduct
  inv := deductInv

end Proof
end Theoryᵢ

end FirstOrder
end FFL

end

end PointwiseComposition
