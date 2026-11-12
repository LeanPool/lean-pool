/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.FixedPointStep

/-!
# Morphisms of second-order blocks

An arity-preserving map of relation variables induces a morphism of the
blocks' vocabularies (`DescriptiveComplexity.SOBlock.homLHom`), and a sentence
over a base vocabulary expanded by the source block transports to one over
the base expanded by the target block
(`DescriptiveComplexity.SOBlock.realize_homSentence`): realization against an
assignment of the target block is realization against its pullback along the
map (`DescriptiveComplexity.SOBlock.homAssign`).

This is the bookkeeping that reads a formula written for one block inside a
*larger* block containing a copy of it. Its first consumer is the FO(≤, IFP)
→ FO(LFP) translation (`DescriptiveComplexity.FixedPointInflationaryLFP`),
whose output sentence mentions the original relation variables while the
translated program computes them as one group of a larger block; the
invariant-structure simulations of `DescriptiveComplexity.Invariant.Simulation`
want it for the same reason.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace SOBlock

variable {B B' : SOBlock} (f : B.ι → B'.ι) (hf : ∀ i, B'.arity (f i) = B.arity i)

/-- The vocabulary morphism induced by an arity-preserving map of relation
variables. -/
def homLHom : B.lang →ᴸ B'.lang where
  onFunction := fun {_} g => isEmptyElim g
  onRelation := fun {_} r => ⟨f r.1, (hf r.1).trans r.2⟩

/-- The pullback of an assignment of the target block along the map: each
source variable reads its image. -/
def homAssign {A : Type} (σ : B'.Assignment A) : B.Assignment A :=
  fun i x => σ (f i) fun j => x (Fin.cast (hf i) j)

variable {L : Language.{0, 0}} {A : Type} [L.Structure A]

/-- The vocabulary morphism is an expansion between the two induced
structures. -/
private theorem homLHom_isExpansionOn (σ : B'.Assignment A) :
    @LHom.IsExpansionOn _ _ (homLHom f hf (B := B)) A
      (B.structure (B.homAssign f hf σ)) (B'.structure σ) := by
  let := B.structure (B.homAssign f hf σ)
  let := B'.structure σ
  refine ⟨fun {n} g => isEmptyElim g, fun {n} r x => ?_⟩
  rfl

/-- **Transport of a formula along a block morphism**: realization over the
target block's assignment is realization of the original formula over the
pulled-back assignment. -/
private theorem realize_homFormula {α : Type} (σ : B'.Assignment A)
    (φ : (L.sum B.lang).Formula α) (v : α → A) :
    (@Formula.Realize _ A (B'.structure₁ (L := L) σ) _
      ((LHom.sumMap (LHom.id L) (homLHom f hf (B := B))).onFormula φ) v) ↔
      @Formula.Realize _ A (B.structure₁ (L := L) (B.homAssign f hf σ)) _ φ v := by
  let := B.structure (B.homAssign f hf σ)
  let := B'.structure σ
  have := homLHom_isExpansionOn f hf (A := A) σ
  exact LHom.realize_onFormula
    (φ := LHom.sumMap (LHom.id L) (homLHom f hf (B := B))) φ

/-- **Transport of a sentence along a block morphism**: realization over the
target block's assignment is realization of the original sentence over the
pulled-back assignment. -/
theorem realize_homSentence (σ : B'.Assignment A) (φ : (L.sum B.lang).Sentence) :
    (@Sentence.Realize _ A (B'.structure₁ (L := L) σ)
      ((LHom.sumMap (LHom.id L) (homLHom f hf (B := B))).onSentence φ)) ↔
      @Sentence.Realize _ A (B.structure₁ (L := L) (B.homAssign f hf σ)) φ := by
  let := B.structure (B.homAssign f hf σ)
  let := B'.structure σ
  have := homLHom_isExpansionOn f hf (A := A) σ
  exact LHom.realize_onSentence (M := A)
    (φ := LHom.sumMap (LHom.id L) (homLHom f hf (B := B))) (ψ := φ)

end SOBlock

end DescriptiveComplexity
