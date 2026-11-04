/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.GeneratedIndexTransport
public import LeanPool.PointwiseComposition.FailureOfComposition.GeneratedQuotient

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
The generated quotient of program indices is a monoid, with multiplication
given by the compiler's composition operation. Interpreting indices as
functional graphs gives a monoid equivalence to the generated graph quotient.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace FailureOfComposition
namespace ProgramIndices

open ProofSearch

noncomputable section

/-- Program indices modulo the generated composition congruence. -/
def GeneratedIndexQuotient (A : Arithmetization) (T : ArithmeticTheory) :=
  Quotient (generatedSetoid A T)

/-- The class of a program index. -/
def generatedIndexMk (A : Arithmetization) (T : ArithmeticTheory) (e : ℕ) :
    GeneratedIndexQuotient A T :=
  Quotient.mk (generatedSetoid A T) e

theorem realizationIndex_respects_generated (A : Arithmetization) (T : ArithmeticTheory)
    [𝐏𝐀 ≼ T] {F G : FunctionalGraph} (h : GeneratedCongruence.Rel T F G) :
    GeneratedRel A T (realizationIndex A F) (realizationIndex A G) :=
  by
  apply graph_implies_generatedRel A T
  exact
    GeneratedCongruence.rel_trans T
      (GeneratedCongruence.rel_of_uniform T (realizationIndex_uniform A F))
      (GeneratedCongruence.rel_trans T h
        (GeneratedCongruence.rel_symm T
          (GeneratedCongruence.rel_of_uniform T (realizationIndex_uniform A G))))

/-- Graph interpretation and chosen PA realizers give inverse maps on the
generated quotients. -/
def generatedQuotientEquiv (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    GeneratedIndexQuotient A T ≃ GeneratedCongruence.QuotientGraph T
    where
  toFun :=
    Quotient.lift (fun e => GeneratedCongruence.quotientMk T ⟨A.graph e, A.functional e⟩)
      (fun _ _ h => Quotient.sound (generatedRel_implies_graph A T h))
  invFun :=
    Quotient.lift (fun F => generatedIndexMk A T (realizationIndex A F))
      (fun _ _ h => Quotient.sound (realizationIndex_respects_generated A T h))
  left_inv
    q := by
    refine Quotient.inductionOn q ?_
    intro e
    exact Quotient.sound (CompositionClosure.base _ _ (realizationIndex_roundtrip A T e))
  right_inv
    q := by
    refine Quotient.inductionOn q ?_
    intro F
    exact Quotient.sound (GeneratedCongruence.rel_of_uniform T (realizationIndex_uniform A F))

@[simp]
theorem generatedQuotientEquiv_mk (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (e : ℕ) :
    generatedQuotientEquiv A T (generatedIndexMk A T e) =
      GeneratedCongruence.quotientMk T ⟨A.graph e, A.functional e⟩ :=
  rfl

@[simp]
theorem generatedQuotientEquiv_symm_mk (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (F : FunctionalGraph) :
    (generatedQuotientEquiv A T).symm (GeneratedCongruence.quotientMk T F) =
      generatedIndexMk A T (realizationIndex A F) :=
  rfl

instance (A : Arithmetization) (T : ArithmeticTheory) : Mul (GeneratedIndexQuotient A T) where
  mul :=
    Quotient.lift₂ (fun e d => generatedIndexMk A T (A.compIndex e d))
      (fun _ _ _ _ he hd => Quotient.sound (CompositionClosure.comp he hd))

instance (A : Arithmetization) (T : ArithmeticTheory) : One (GeneratedIndexQuotient A T) where
  one := generatedIndexMk A T (realizationIndex A GeneratedCongruence.identityGraph)

@[simp]
theorem generatedIndexQuotient_mul_mk (A : Arithmetization) (T : ArithmeticTheory) (e d : ℕ) :
    generatedIndexMk A T e * generatedIndexMk A T d = generatedIndexMk A T (A.compIndex e d) :=
  rfl

theorem generatedIndexQuotient_one_mk (A : Arithmetization) (T : ArithmeticTheory) :
    (1 : GeneratedIndexQuotient A T) =
      generatedIndexMk A T (realizationIndex A GeneratedCongruence.identityGraph) :=
  rfl

theorem generatedQuotientEquiv_mul (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (a b : GeneratedIndexQuotient A T) :
    generatedQuotientEquiv A T (a * b) =
      generatedQuotientEquiv A T a * generatedQuotientEquiv A T b :=
  by
  refine Quotient.inductionOn₂ a b ?_
  intro e d
  exact Quotient.sound (GeneratedCongruence.rel_of_uniform T (A.composition e d))

theorem generatedQuotientEquiv_one (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    generatedQuotientEquiv A T 1 = 1 :=
  Quotient.sound
    (GeneratedCongruence.rel_of_uniform T
      (realizationIndex_uniform A GeneratedCongruence.identityGraph))

instance generatedIndexQuotientMonoid (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    Monoid (GeneratedIndexQuotient A T)
    where
  mul_assoc a b
    c :=
    (generatedQuotientEquiv A T).injective
      (by simp only [generatedQuotientEquiv_mul, mul_assoc])
  one_mul
    a :=
    (generatedQuotientEquiv A T).injective
      (by simp only [generatedQuotientEquiv_mul, generatedQuotientEquiv_one, one_mul])
  mul_one
    a :=
    (generatedQuotientEquiv A T).injective
      (by simp only [generatedQuotientEquiv_mul, generatedQuotientEquiv_one, mul_one])

/-- The index and graph quotients are equivalent as monoids. -/
def generatedQuotientMulEquiv (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    GeneratedIndexQuotient A T ≃* GeneratedCongruence.QuotientGraph T :=
  { generatedQuotientEquiv A T with map_mul' := generatedQuotientEquiv_mul A T }

@[simp]
theorem generatedQuotientMulEquiv_mk (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (e : ℕ) :
    generatedQuotientMulEquiv A T (generatedIndexMk A T e) =
      GeneratedCongruence.quotientMk T ⟨A.graph e, A.functional e⟩ :=
  rfl

/-- Universality on functional graphs also collapses the index quotient. -/
theorem generatedIndexQuotient_subsingleton_of_graph_universal (A : Arithmetization)
    (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (h : ∀ F G : FunctionalGraph, GeneratedCongruence.Rel T F G) :
    Subsingleton (GeneratedIndexQuotient A T) :=
  by
  have := GeneratedCongruence.quotient_subsingleton_of_universal T h
  constructor
  intro a b
  exact (generatedQuotientEquiv A T).injective (Subsingleton.elim _ _)

end

end ProgramIndices
end FailureOfComposition

end

end PointwiseComposition
