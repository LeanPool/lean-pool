/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.GeneratedGraphDefinitions

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
The least composition congruence on indices agrees with the least congruence
on their functional arithmetic graphs. Realization and composition are used
at the level of PA proofs, including for the chosen inverse representatives.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace FailureOfComposition
namespace ProgramIndices

open ProofSearch

noncomputable section

/-- The Generated Rel construction in `FailureOfComposition.ProgramIndices`. -/
def GeneratedRel (A : Arithmetization) (T : ArithmeticTheory) (e d : ℕ) : Prop :=
  CompositionClosure.Generated A.compIndex (PointwiseIndex A T) e d

/-- The generated Setoid construction in `FailureOfComposition.ProgramIndices`. -/
def generatedSetoid (A : Arithmetization) (T : ArithmeticTheory) : Setoid ℕ :=
  CompositionClosure.setoid A.compIndex (PointwiseIndex A T)

private def indexGraph (A : Arithmetization) (e : ℕ) : FunctionalGraph :=
  ⟨A.graph e, A.functional e⟩

/-- Select an index whose arithmetic graph PA proves equal to the given graph. -/
def realizationIndex (A : Arithmetization) (F : FunctionalGraph) : ℕ :=
  Classical.choose (A.realization F.val F.property)

theorem realizationIndex_uniform (A : Arithmetization) (F : FunctionalGraph) :
    Uniform 𝐏𝐀 (A.graph (realizationIndex A F)) F.val :=
  Classical.choose_spec (A.realization F.val F.property)

theorem realizationIndex_pointwise (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (F G : FunctionalGraph) (h : Pointwise T F.val G.val) :
    PointwiseIndex A T (realizationIndex A F) (realizationIndex A G) :=
  by
  apply (pointwiseIndex_iff A T _ _).mpr
  have eqv := pointwise_equivalence T
  exact
    eqv.trans (uniform_to_pointwise T (realizationIndex_uniform A F))
      (eqv.trans h (eqv.symm (uniform_to_pointwise T (realizationIndex_uniform A G))))

theorem realizationIndex_roundtrip (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (e : ℕ) : PointwiseIndex A T (realizationIndex A ⟨A.graph e, A.functional e⟩) e :=
  (pointwiseIndex_iff A T _ _).mpr
    (uniform_to_pointwise T (realizationIndex_uniform A ⟨A.graph e, A.functional e⟩))

theorem realizationIndex_composition (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (F G : FunctionalGraph) :
    PointwiseIndex A T (realizationIndex A (functionalComp F G))
      (A.compIndex (realizationIndex A F) (realizationIndex A G)) :=
  by
  apply (pointwiseIndex_iff A T _ _).mpr
  have eqv := pointwise_equivalence T
  have hl := uniform_to_pointwise T (realizationIndex_uniform A (functionalComp F G))
  have hr :=
    eqv.trans
      (uniform_to_pointwise T (A.composition (realizationIndex A F) (realizationIndex A G)))
      (uniform_to_pointwise T
        (uniform_comp (realizationIndex_uniform A F) (realizationIndex_uniform A G)))
  exact eqv.trans hl (eqv.symm hr)

private theorem indexGraph_composition (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (e d : ℕ) :
    GeneratedCongruence.Rel T (indexGraph A (A.compIndex e d))
      (functionalComp (indexGraph A e) (indexGraph A d)) :=
  GeneratedCongruence.rel_of_uniform T (A.composition e d)

/-- The graph interpretation preserves the generated relation despite being
a composition homomorphism only up to a PA-provable graph equation. -/
theorem generatedRel_implies_graph (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    {e d : ℕ} (h : GeneratedRel A T e d) :
    GeneratedCongruence.Rel T ⟨A.graph e, A.functional e⟩ ⟨A.graph d, A.functional d⟩ :=
  by
  apply h (fun e d => GeneratedCongruence.Rel T (indexGraph A e) (indexGraph A d))
  · constructor
    · exact
        ⟨fun e => GeneratedCongruence.rel_refl T (indexGraph A e), fun h =>
          GeneratedCongruence.rel_symm T h, fun h h' => GeneratedCongruence.rel_trans T h h'⟩
    · intro e e' d d' he hd
      exact
        GeneratedCongruence.rel_trans T (indexGraph_composition A T e d)
          (GeneratedCongruence.rel_trans T (GeneratedCongruence.rel_comp T he hd)
            (GeneratedCongruence.rel_symm T (indexGraph_composition A T e' d')))
  · intro e d hed
    exact GeneratedCongruence.rel_base T ((pointwiseIndex_iff A T e d).mp hed)

/-- Realization transports the graph congruence back to indices. The chosen
realizers differ from the original indices by generating relations already. -/
theorem graph_implies_generatedRel (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    {e d : ℕ}
    (h : GeneratedCongruence.Rel T ⟨A.graph e, A.functional e⟩ ⟨A.graph d, A.functional d⟩) :
    GeneratedRel A T e d :=
  by
  have hlift :
    GeneratedRel A T (realizationIndex A (indexGraph A e))
      (realizationIndex A (indexGraph A d)) :=
    by
    apply h (fun F G => GeneratedRel A T (realizationIndex A F) (realizationIndex A G))
    · constructor
      · exact
          ⟨fun F => CompositionClosure.refl _ _ (realizationIndex A F), fun h =>
            CompositionClosure.symm h, fun h h' => CompositionClosure.trans h h'⟩
      · intro F F' G G' hF hG
        exact
          CompositionClosure.trans
            (CompositionClosure.base _ _ (realizationIndex_composition A T F G))
            (CompositionClosure.trans (CompositionClosure.comp hF hG)
              (CompositionClosure.symm
                (CompositionClosure.base _ _ (realizationIndex_composition A T F' G'))))
    · intro F G hFG
      exact CompositionClosure.base _ _ (realizationIndex_pointwise A T F G hFG)
  exact
    CompositionClosure.trans
      (CompositionClosure.symm (CompositionClosure.base _ _ (realizationIndex_roundtrip A T e)))
      (CompositionClosure.trans hlift
        (CompositionClosure.base _ _ (realizationIndex_roundtrip A T d)))

theorem generatedRel_iff_graph (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (e d : ℕ) :
    GeneratedRel A T e d ↔
      GeneratedCongruence.Rel T ⟨A.graph e, A.functional e⟩ ⟨A.graph d, A.functional d⟩ :=
  ⟨generatedRel_implies_graph A T, graph_implies_generatedRel A T⟩

end

end ProgramIndices
end FailureOfComposition

end

end PointwiseComposition
