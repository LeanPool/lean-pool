/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.GeneratedCollapse

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Composition descends to the quotient by the generated congruence. The PA
proofs of associativity and the identity laws make this quotient a monoid
for every theory extending PA. A universal congruence gives a singleton
quotient.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition
namespace GeneratedCongruence

open ProofSearch

/-- PA-functional Sigma-one graphs modulo the generated composition
congruence. -/
def QuotientGraph (T : ArithmeticTheory) :=
  Quotient (graphSetoid T)

/-- The class of a functional graph. -/
def quotientMk (T : ArithmeticTheory) (F : FunctionalGraph) : QuotientGraph T :=
  Quotient.mk (graphSetoid T) F

instance (T : ArithmeticTheory) : Mul (QuotientGraph T) where
  mul :=
    Quotient.lift₂ (fun F G => Quotient.mk (graphSetoid T) (functionalComp F G))
      (fun _ _ _ _ hF hG => Quotient.sound (rel_comp T hF hG))

instance (T : ArithmeticTheory) : One (QuotientGraph T) where
  one := Quotient.mk (graphSetoid T) identityGraph

@[simp]
theorem quotient_mul_mk (T : ArithmeticTheory) (F G : FunctionalGraph) :
    quotientMk T F * quotientMk T G = quotientMk T (functionalComp F G) :=
  rfl

theorem one_mk (T : ArithmeticTheory) : (1 : QuotientGraph T) = quotientMk T identityGraph :=
  rfl

/-- Composition of graph formulas is associative already in PA. -/
theorem comp_associative_uniform (F G H : Graph) :
    Uniform 𝐏𝐀 (comp (comp F G) H) (comp F (comp G H)) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  simp only [models_iff, uniformSentence_eval, comp_eval, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  intro x y
  constructor
  · rintro ⟨z, hHz, w, hGzw, hFwy⟩
    exact ⟨w, ⟨z, hHz, hGzw⟩, hFwy⟩
  · rintro ⟨w, ⟨z, hHz, hGzw⟩, hFwy⟩
    exact ⟨z, hHz, w, hGzw, hFwy⟩

instance quotientMonoid (T : ArithmeticTheory) [𝐏𝐀 ≼ T] : Monoid (QuotientGraph T)
    where
  mul_assoc a b
    c := by
    refine Quotient.inductionOn₃ a b c ?_
    intro F G H
    exact Quotient.sound (rel_of_uniform T (comp_associative_uniform F.val G.val H.val))
  one_mul
    a := by
    refine Quotient.inductionOn a ?_
    intro F
    exact Quotient.sound (rel_of_uniform T (identity_comp F.val))
  mul_one
    a := by
    refine Quotient.inductionOn a ?_
    intro F
    exact Quotient.sound (rel_of_uniform T (comp_right_identity F.val))

/-- If all functional graphs are related, every two quotient elements are
equal. Together with the identity element, this makes the quotient a
singleton. -/
theorem quotient_subsingleton_of_universal (T : ArithmeticTheory)
    (h : ∀ F G : FunctionalGraph, Rel T F G) : Subsingleton (QuotientGraph T) :=
  by
  constructor
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro F G
  exact Quotient.sound (h F G)

end GeneratedCongruence
end FailureOfComposition

end

end PointwiseComposition
