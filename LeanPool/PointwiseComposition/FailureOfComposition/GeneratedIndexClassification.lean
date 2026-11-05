/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.GeneratedIndexTransport
public import LeanPool.PointwiseComposition.FailureOfComposition.GeneratedClassification
public import LeanPool.PointwiseComposition.FailureOfComposition.PiOneIndexCharacterization

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Classification of the least composition congruence on program indices.
Sigma-one soundness gives equality of denoted partial functions; otherwise
the generated relation is universal. No effective presentation is required.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace FailureOfComposition
namespace ProgramIndices

open ProofSearch

theorem extensional_implies_generated (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (e d : ℕ) (h : A.evaluation e = A.evaluation d) : GeneratedRel A T e d :=
  (generatedRel_iff_graph A T e d).mpr
    (GeneratedCongruence.extensional_implies_generated T ⟨A.graph e, A.functional e⟩
      ⟨A.graph d, A.functional d⟩ ((extensionalIndex_iff A e d).mp h))

theorem generated_iff_extensional_of_sound (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hT : GeneratedCongruence.SigmaOneSound T) (e d : ℕ) :
    GeneratedRel A T e d ↔ A.evaluation e = A.evaluation d :=
  (generatedRel_iff_graph A T e d).trans
    ((GeneratedCongruence.generated_iff_extensional_of_sound T hT ⟨A.graph e, A.functional e⟩
          ⟨A.graph d, A.functional d⟩).trans
      (extensionalIndex_iff A e d).symm)

theorem generated_universal_of_not_sound (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hT : ¬GeneratedCongruence.SigmaOneSound T) (e d : ℕ) : GeneratedRel A T e d :=
  (generatedRel_iff_graph A T e d).mpr
    (GeneratedCongruence.generated_universal_of_not_sound T hT ⟨A.graph e, A.functional e⟩
      ⟨A.graph d, A.functional d⟩)

/-- The two cases of the generated-congruence theorem, with equality of
actual partial-function denotations in the sound case. -/
theorem generated_congruence_classification (A : Arithmetization) (T : ArithmeticTheory)
    [𝐏𝐀 ≼ T] :
    (GeneratedCongruence.SigmaOneSound T →
        ∀ e d : ℕ, GeneratedRel A T e d ↔ A.evaluation e = A.evaluation d) ∧
      (¬GeneratedCongruence.SigmaOneSound T → ∀ e d : ℕ, GeneratedRel A T e d) :=
  ⟨generated_iff_extensional_of_sound A T, generated_universal_of_not_sound A T⟩

theorem generated_iff_extensional_or_unsound (A : Arithmetization) (T : ArithmeticTheory)
    [𝐏𝐀 ≼ T] (e d : ℕ) :
    GeneratedRel A T e d ↔
      A.evaluation e = A.evaluation d ∨ ¬GeneratedCongruence.SigmaOneSound T :=
  (generatedRel_iff_graph A T e d).trans
    ((GeneratedCongruence.generated_iff_extensional_or_unsound T ⟨A.graph e, A.functional e⟩
          ⟨A.graph d, A.functional d⟩).trans
      (or_congr (extensionalIndex_iff A e d).symm Iff.rfl))

/-- The quotient by the generated congruence has exactly one element if and
only if the ambient theory fails Sigma-one soundness. -/
theorem generated_quotient_subsingleton_iff_not_sound (A : Arithmetization)
    (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    Subsingleton (Quotient (generatedSetoid A T)) ↔ ¬GeneratedCongruence.SigmaOneSound T :=
  by
  constructor
  · intro hsub
    apply (GeneratedCongruence.quotient_subsingleton_iff_not_sound T).mp
    apply GeneratedCongruence.quotient_subsingleton_of_universal T
    intro F G
    have heq :=
      hsub.allEq (Quotient.mk (generatedSetoid A T) (realizationIndex A F))
        (Quotient.mk (generatedSetoid A T) (realizationIndex A G))
    have hrel : GeneratedRel A T (realizationIndex A F) (realizationIndex A G) :=
      Quotient.exact heq
    exact
      GeneratedCongruence.rel_trans T
        (GeneratedCongruence.rel_symm T
          (GeneratedCongruence.rel_of_uniform T (realizationIndex_uniform A F)))
        (GeneratedCongruence.rel_trans T ((generatedRel_iff_graph A T _ _).mp hrel)
          (GeneratedCongruence.rel_of_uniform T (realizationIndex_uniform A G)))
  · intro hT
    constructor
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro e d
    exact Quotient.sound (generated_universal_of_not_sound A T hT e d)

end ProgramIndices
end FailureOfComposition

end

end PointwiseComposition
