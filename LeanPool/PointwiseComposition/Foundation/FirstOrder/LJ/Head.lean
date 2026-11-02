/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.Vorspiel.Multiset
public import LeanPool.PointwiseComposition.Foundation.Vorspiel.Option
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Syntax.Intuitionistic.Rew
public import LeanPool.PointwiseComposition.Foundation.Logic.Calculus

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# First-order $\mathbf{LJ}$ -/

@[expose] public section

namespace FFL
namespace FirstOrder

variable {L : Language.{u}}

open Semiformulaᵢ

/-- The Theoryᵢ construction in `FFL.FirstOrder`. -/
abbrev Theoryᵢ (L : Language.{u}) :=
  Set (Sentenceᵢ L)

namespace LJ

/-- The Sequent construction in `FFL.FirstOrder.LJ`. -/
abbrev Sequent (L : Language.{u}) :=
  Multiset (Propositionᵢ L)

/-- The Head construction in `FFL.FirstOrder.LJ`. -/
abbrev Head (L : Language.{u}) :=
  Option (Propositionᵢ L)

namespace Head

/-- The shift construction in `FFL.FirstOrder.LJ.Head`. -/
def shift (Ξ : Head L) : Head L :=
  Ξ.map Rewriting.shift

/-- The rewrite construction in `FFL.FirstOrder.LJ.Head`. -/
def rewrite (f : ℕ → SyntacticTerm L) (Ξ : Head L) : Head L :=
  Ξ.map (Rew.rewrite f ▹ ·)

@[simp]
lemma shift_none : shift (none : Head L) = none :=
  rfl

@[simp]
lemma shift_some (φ : Propositionᵢ L) : shift φ = some (Rewriting.shift φ) :=
  rfl

@[simp]
lemma rewrite_none (f : ℕ → SyntacticTerm L) : rewrite f (none : Head L) = none :=
  rfl

@[simp]
lemma rewrite_some (f : ℕ → SyntacticTerm L) (φ : Propositionᵢ L) :
    rewrite f φ = some (Rew.rewrite f ▹ φ) :=
  rfl

end Head

end LJ

end FirstOrder
end FFL

end

end PointwiseComposition
