/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.Logic.LogicSymbol
public import LeanPool.PointwiseComposition.Foundation.Vorspiel.AdjunctiveSet

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Forcing relation -/

@[expose] public section

namespace FFL

/-- Data and laws for Forcing Relation in `FFL`. -/
class ForcingRelation (W : Type*) (F : outParam Type*) where
  /-- The Forces construction in `FFL.ForcingRelation`. -/
  Forces : W → F → Prop

/-- The «term ⊩ » construction in `FFL`. -/
infix:45 " ⊩ " => ForcingRelation.Forces

/-- Data and laws for Forcing Exists in `FFL`. -/
class ForcingExists (W : Type*) (α : outParam Type*) where
  /-- The Forces construction in `FFL.ForcingExists`. -/
  Forces : W → α → Prop

/-- The «term ⊩↓ » construction in `FFL`. -/
infix:45 " ⊩↓ " => ForcingExists.Forces

namespace ForcingRelation

variable {W : Type*} {F : Type*} [ForcingRelation W F] [LogicalConnective F] [LogicalNeutral F]

/-- The Not Forces construction in `FFL.ForcingRelation`. -/
abbrev NotForces (w : W) (φ : F) : Prop :=
  ¬w ⊩ φ

/-- The «term ⊮ » construction in `FFL.ForcingRelation`. -/
infix:45 " ⊮ " => NotForces

variable (W)

/-- Data and laws for Basic Semantics in `FFL.ForcingRelation`. -/
class BasicSemantics where
  verum (w : W) : w ⊩ ⊤
  and (w : W) : w ⊩ φ ⋏ ψ ↔ w ⊩ φ ∧ w ⊩ ψ
  or (w : W) : w ⊩ φ ⋎ ψ ↔ w ⊩ φ ∨ w ⊩ ψ

/-- Data and laws for Monotone in `FFL.ForcingRelation`. -/
class Monotone (R : outParam (W → W → Prop)) where
  monotone {w : W} : w ⊩ φ → ∀ v, R w v → v ⊩ φ

/-- Data and laws for Int Kripke in `FFL.ForcingRelation`. -/
class IntKripke (R : outParam (W → W → Prop)) extends BasicSemantics W, Monotone W R where
  imply (w : W) : w ⊩ φ ⇒ₗ ψ ↔ (∀ v, R w v → v ⊩ φ → v ⊩ ψ)
  falsum (w : W) : ¬w ⊩ ⊥
  not (w : W) : w ⊩ ∼φ ↔ (∀ v, R w v → ¬v ⊩ φ)

variable {W}

attribute [grind .] BasicSemantics.verum
attribute [simp, grind .] BasicSemantics.and BasicSemantics.or IntKripke.falsum

attribute [grind .] IntKripke.imply IntKripke.not

@[grind =, simp]
lemma iff (R : W → W → Prop) [IntKripke W R] : w ⊩ (φ ⇔ₗ ψ) ↔ (∀ v, R w v → (v ⊩ φ ↔ v ⊩ ψ)) :=
  by simp [LogicalConnective.iff, IntKripke.imply]; grind

variable (W)

/-- The All Forces construction in `FFL.ForcingRelation`. -/
abbrev AllForces (φ : F) : Prop :=
  ∀ w : W, w ⊩ φ

/-- The «term ∀⊩ » construction in `FFL.ForcingRelation`. -/
infix:45 " ∀⊩ " => AllForces

/-- The All Forces Set construction in `FFL.ForcingRelation`. -/
abbrev AllForcesSet (s : S) [AdjunctiveSet F S] : Prop :=
  ∀ φ ∈ s, W ∀⊩ φ

/-- The «term ∀⊩* » construction in `FFL.ForcingRelation`. -/
infix:45 " ∀⊩* " => AllForcesSet

variable {W}

namespace AllForces

@[simp]
lemma verum [BasicSemantics W] : W ∀⊩ ⊤ :=
  BasicSemantics.verum

@[simp]
lemma and [BasicSemantics W] : W ∀⊩ φ ⋏ ψ ↔ W ∀⊩ φ ∧ W ∀⊩ ψ := by simp [AllForces]; grind

end AllForces

end ForcingRelation

/-!
### Forcing relation for classical logic -/

/-- Data and laws for Weak Forcing Relation in `FFL`. -/
class WeakForcingRelation (ℙ : Type*) (F : outParam Type*) where
  /-- The Weakly Forces construction in `FFL.WeakForcingRelation`. -/
  WeaklyForces : ℙ → F → Prop

/-- The «term ⊩ᶜ » construction in `FFL`. -/
infix:45 " ⊩ᶜ " => WeakForcingRelation.WeaklyForces

namespace WeakForcingRelation

variable {ℙ : Type*} {F : Type*} [WeakForcingRelation ℙ F] [LogicalConnective F]
  [LogicalNeutral F]

/-- The Not Forces construction in `FFL.WeakForcingRelation`. -/
abbrev NotForces (p : ℙ) (φ : F) : Prop :=
  ¬p ⊩ᶜ φ

/-- The «term ⊮ᶜ » construction in `FFL.WeakForcingRelation`. -/
infix:45 " ⊮ᶜ " => NotForces

variable (ℙ)

/-- Data and laws for Basic Semantics in `FFL.WeakForcingRelation`. -/
class BasicSemantics where
  verum (p : ℙ) : p ⊩ᶜ ⊤
  falsum (p : ℙ) : ¬p ⊩ᶜ ⊥
  and (p : ℙ) : p ⊩ᶜ φ ⋏ ψ ↔ p ⊩ᶜ φ ∧ p ⊩ᶜ ψ

/-- Data and laws for Classical Kripke in `FFL.WeakForcingRelation`. -/
class ClassicalKripke (R : outParam (ℙ → ℙ → Prop)) extends BasicSemantics ℙ where
  or (p : ℙ) : p ⊩ᶜ φ ⋎ ψ ↔ ∀ q, R p q → ∃ x, R q x ∧ (x ⊩ᶜ φ ∨ x ⊩ᶜ ψ)
  not (p : ℙ) : p ⊩ᶜ ∼φ ↔ (∀ q, R p q → ¬q ⊩ᶜ φ)
  imply (p : ℙ) : p ⊩ᶜ φ ⇒ₗ ψ ↔ (∀ q, R p q → q ⊩ᶜ φ → q ⊩ᶜ ψ)
  monotone {p : ℙ} : p ⊩ᶜ φ → ∀ q, R p q → q ⊩ᶜ φ
  generic {p : ℙ} : (∀ q, R p q → ∃ r, R q r ∧ r ⊩ᶜ φ) → p ⊩ᶜ φ

variable {ℙ}

attribute [grind .] BasicSemantics.verum
attribute [simp, grind .] BasicSemantics.falsum BasicSemantics.and ClassicalKripke.or
  ClassicalKripke.imply ClassicalKripke.not

variable (ℙ)

/-- The All Forces construction in `FFL.WeakForcingRelation`. -/
abbrev AllForces (φ : F) : Prop :=
  ∀ p : ℙ, p ⊩ᶜ φ

/-- The «term ∀⊩ᶜ » construction in `FFL.WeakForcingRelation`. -/
infix:45 " ∀⊩ᶜ " => AllForces

/-- The All Forces Set construction in `FFL.WeakForcingRelation`. -/
abbrev AllForcesSet (s : S) [AdjunctiveSet F S] : Prop :=
  ∀ φ ∈ s, ℙ ∀⊩ᶜ φ

/-- The «term ∀⊩ᶜ* » construction in `FFL.WeakForcingRelation`. -/
infix:45 " ∀⊩ᶜ* " => AllForcesSet

variable {ℙ}

namespace AllForces

@[simp]
lemma verum [BasicSemantics ℙ] : ℙ ∀⊩ᶜ ⊤ :=
  BasicSemantics.verum

@[simp]
lemma falsum [BasicSemantics ℙ] [Nonempty ℙ] : ¬ℙ ∀⊩ᶜ ⊥ := fun h ↦ by
  simpa using h (Classical.choice inferInstance)

@[simp]
lemma and [BasicSemantics ℙ] : ℙ ∀⊩ᶜ φ ⋏ ψ ↔ ℙ ∀⊩ᶜ φ ∧ ℙ ∀⊩ᶜ ψ := by
  simp [AllForces];
  grind
    /-
    @[simp] lemma or [ClassicalKripke ℙ R] : ℙ ∀⊩ᶜ φ ⋎ ψ ↔ ℙ ∀⊩ᶜ φ ∨ ℙ ∀⊩ᶜ ψ := by
      simp [AllForces]
      constructor
      · intro h
        by_contra! C
        rcases C with ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    -/

end AllForces

end WeakForcingRelation

end FFL

end

end PointwiseComposition
