/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ProgramIndices
public import LeanPool.PointwiseComposition.FailureOfComposition.PiOneCharacterization

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
The Pi-one characterization at program indices.  Realization transports the
functional graph statements to every index in the given arithmetization;
standard adequacy identifies graph equality with equality of partial functions.
No effective presentation of the ambient theory is required.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition
namespace ProgramIndices

open ProofSearch

/-- Right composition fixes the inner program and replaces the outer one. -/
def RightCompatible (A : Arithmetization) (T : ArithmeticTheory) : Prop :=
  ∀ f h g : ℕ, PointwiseIndex A T f h → PointwiseIndex A T (A.compIndex f g) (A.compIndex h g)

/-- Composition respects pointwise equality in both arguments. -/
def CompositionCongruence (A : Arithmetization) (T : ArithmeticTheory) : Prop :=
  ∀ f f' g g' : ℕ,
    PointwiseIndex A T f f' →
      PointwiseIndex A T g g' → PointwiseIndex A T (A.compIndex f g) (A.compIndex f' g')

/-- The two programs denote the same standard partial function. -/
def ExtensionalIndex (A : Arithmetization) (e d : ℕ) : Prop :=
  A.evaluation e = A.evaluation d

/-- Pointwise provability coincides with equality of denoted partial functions. -/
def AgreesWithExtensional (A : Arithmetization) (T : ArithmeticTheory) : Prop :=
  ∀ e d : ℕ, PointwiseIndex A T e d ↔ ExtensionalIndex A e d

/-- Adequacy turns equality of denotations into standard graph equality. -/
theorem extensionalIndex_iff (A : Arithmetization) (e d : ℕ) :
    ExtensionalIndex A e d ↔ PiOneCharacterization.Extensional (A.graph e) (A.graph d) :=
  by
  constructor
  · intro h x y
    rw [A.adequate, A.adequate]
    rw [show A.evaluation e = A.evaluation d from h]
  · intro h
    funext x
    apply Part.ext
    intro y
    exact (A.adequate e x y).symm.trans ((h x y).trans (A.adequate d x y))

private theorem uniform_extensional {F G : Graph} (h : Uniform 𝐏𝐀 F G) :
    PiOneCharacterization.Extensional F G :=
  by
  have hs : ℕ↓[ℒₒᵣ] ⊧ uniformSentence F G :=
    consequence_iff.mp (Theory.Proof.sound h) ℕ inferInstance
  simpa only [PiOneCharacterization.Extensional, models_iff, uniformSentence_eval] using hs

/-- The composition graph equations transport compatibility to indices. -/
theorem rightCompatible_of_graph (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (h : PiOneCharacterization.RightCompatible T) : RightCompatible A T :=
  by
  intro f i g hfi
  have heq := pointwise_equivalence T
  apply (pointwiseIndex_iff A T _ _).mpr
  exact
    heq.trans (uniform_to_pointwise T (A.composition f g))
      (heq.trans
        (h (A.graph f) (A.graph i) (A.graph g) (A.functional f) (A.functional i)
          (A.functional g) ((pointwiseIndex_iff A T _ _).mp hfi))
        (heq.symm (uniform_to_pointwise T (A.composition i g))))

/-- Realization makes compatibility at indices sufficient for all functional
Sigma-one graphs. -/
theorem rightCompatible_iff_graph (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    RightCompatible A T ↔ PiOneCharacterization.RightCompatible T :=
  by
  constructor
  · intro h F H G hF hH hG hFH
    by_contra hn
    obtain ⟨f, i, g, hfi, hcomp⟩ :=
      index_noncongruence_of_graph_noncongruence A T ⟨F, H, G, hF, hH, hG, hFH, hn⟩
    exact hcomp (h f i g hfi)
  · exact rightCompatible_of_graph A T

/-- Left composition is compatible for every extension of PA. -/
theorem pointwiseIndex_comp_left (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (f g h : ℕ) (hgh : PointwiseIndex A T g h) :
    PointwiseIndex A T (A.compIndex f g) (A.compIndex f h) :=
  by
  have heq := pointwise_equivalence T
  apply (pointwiseIndex_iff A T _ _).mpr
  exact
    heq.trans (uniform_to_pointwise T (A.composition f g))
      (heq.trans
        (PiOneCharacterization.pointwise_comp_left T (A.graph f) (A.graph g) (A.graph h)
          ((pointwiseIndex_iff A T _ _).mp hgh))
        (heq.symm (uniform_to_pointwise T (A.composition f h))))

/-- Automatic left compatibility supplies the other argument of composition. -/
theorem congruence_iff_rightCompatible (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    CompositionCongruence A T ↔ RightCompatible A T :=
  by
  constructor
  · intro h f i g hfi
    exact h f i g g hfi ((indexSetoid A T).refl g)
  · intro h f f' g g' hff' hgg'
    exact (indexSetoid A T).trans (h f f' g hff') (pointwiseIndex_comp_left A T f' g g' hgg')

/-- The full composition property is unchanged by passing to indices. -/
theorem compositionCongruence_iff_graph (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    CompositionCongruence A T ↔ PiOneCharacterization.CompositionCongruence T :=
  (congruence_iff_rightCompatible A T).trans
    ((rightCompatible_iff_graph A T).trans
      (PiOneCharacterization.congruence_iff_rightCompatible T).symm)

/-- The graph and index formulations of agreement with extensional equality
are equivalent; PA proofs of realization are used only via PA soundness. -/
theorem agreesWithExtensional_iff_graph (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    AgreesWithExtensional A T ↔ PiOneCharacterization.AgreesWithExtensional T :=
  by
  constructor
  · intro h F G hF hG
    obtain ⟨e, he⟩ := A.realization F hF
    obtain ⟨d, hd⟩ := A.realization G hG
    have hep := uniform_to_pointwise T he
    have hdp := uniform_to_pointwise T hd
    have hee := uniform_extensional he
    have hde := uniform_extensional hd
    have heq := pointwise_equivalence T
    constructor
    · intro hFG
      have hed : PointwiseIndex A T e d :=
        (pointwiseIndex_iff A T _ _).mpr (heq.trans hep (heq.trans hFG (heq.symm hdp)))
      have hext := (extensionalIndex_iff A e d).mp ((h e d).mp hed)
      intro x y
      exact (hee x y).symm.trans ((hext x y).trans (hde x y))
    · intro hFG
      have hext : PiOneCharacterization.Extensional (A.graph e) (A.graph d) := fun x y =>
        (hee x y).trans ((hFG x y).trans (hde x y).symm)
      have hed := (h e d).mpr ((extensionalIndex_iff A e d).mpr hext)
      exact heq.trans (heq.symm hep) (heq.trans ((pointwiseIndex_iff A T _ _).mp hed) hdp)
  · intro h e d
    exact
      (pointwiseIndex_iff A T e d).trans
        ((h (A.graph e) (A.graph d) (A.functional e) (A.functional d)).trans
          (extensionalIndex_iff A e d).symm)

/-- Right composition is compatible exactly for Pi-one complete theories. -/
theorem rightCompatible_iff_piOneComplete (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    [Consistent T] : RightCompatible A T ↔ PiOneCharacterization.PiOneComplete T :=
  (rightCompatible_iff_graph A T).trans
    (PiOneCharacterization.rightCompatible_iff_piOneComplete T)

/-- Full composition congruence has the same Pi-one completeness criterion. -/
theorem compositionCongruence_iff_piOneComplete (A : Arithmetization) (T : ArithmeticTheory)
    [𝐏𝐀 ≼ T] [Consistent T] :
    CompositionCongruence A T ↔ PiOneCharacterization.PiOneComplete T :=
  (compositionCongruence_iff_graph A T).trans
    (PiOneCharacterization.compositionCongruence_iff_piOneComplete T)

/-- The fourth statement uses equality of actual partial-function denotations. -/
theorem agreesWithExtensional_iff_piOneComplete (A : Arithmetization) (T : ArithmeticTheory)
    [𝐏𝐀 ≼ T] [Consistent T] :
    AgreesWithExtensional A T ↔ PiOneCharacterization.PiOneComplete T :=
  (agreesWithExtensional_iff_graph A T).trans
    (PiOneCharacterization.agreesWithExtensional_iff_piOneComplete T)

/-- For a consistent Pi-one complete extension of PA, pointwise provability
is exactly extensional equality of the interpreted programs. -/
theorem pointwiseIndex_iff_evaluation_eq (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    [Consistent T] (h : PiOneCharacterization.PiOneComplete T) (e d : ℕ) :
    PointwiseIndex A T e d ↔ A.evaluation e = A.evaluation d :=
  ((agreesWithExtensional_iff_piOneComplete A T).mpr h) e d

/-- All four manuscript statements, without an enumerability hypothesis. -/
theorem characterization (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T] [Consistent T] :
    (RightCompatible A T ↔ CompositionCongruence A T) ∧
      (CompositionCongruence A T ↔ PiOneCharacterization.PiOneComplete T) ∧
        (PiOneCharacterization.PiOneComplete T ↔ AgreesWithExtensional A T) :=
  ⟨(congruence_iff_rightCompatible A T).symm, compositionCongruence_iff_piOneComplete A T,
    (agreesWithExtensional_iff_piOneComplete A T).symm⟩

/-- An operation on the quotient inducing program composition exists exactly
when the index relation is a composition congruence. -/
theorem quotient_composition_exists_iff_congruence (A : Arithmetization) (T : ArithmeticTheory)
    [𝐏𝐀 ≼ T] :
    (∃ C : Quotient (indexSetoid A T) → Quotient (indexSetoid A T) → Quotient (indexSetoid A T),
        ∀ e d,
          C (Quotient.mk (indexSetoid A T) e) (Quotient.mk (indexSetoid A T) d) =
            Quotient.mk (indexSetoid A T) (A.compIndex e d)) ↔
      CompositionCongruence A T :=
  FailureOfComposition.quotient_composition_exists_iff (indexSetoid A T) A.compIndex

/-- The obstruction to quotient composition is precisely failure of Pi-one
completeness, even for theories without an effective presentation. -/
theorem no_index_quotient_iff_not_piOneComplete (A : Arithmetization) (T : ArithmeticTheory)
    [𝐏𝐀 ≼ T] [Consistent T] :
    NoIndexQuotientComposition A T ↔ ¬PiOneCharacterization.PiOneComplete T :=
  by
  unfold NoIndexQuotientComposition
  exact
    not_congr
      ((quotient_composition_exists_iff_congruence A T).trans
        (compositionCongruence_iff_piOneComplete A T))

end ProgramIndices
end FailureOfComposition

end

end PointwiseComposition
