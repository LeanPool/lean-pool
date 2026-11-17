/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.PiOneDefinitions

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Elementary composition laws for the Pi-one completeness characterization.
The input quantifier in pointwise provability remains external throughout.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition
namespace PiOneCharacterization

open ProofSearch

/-- Composing on the left by a fixed graph always preserves pointwise
provability. The quantified intermediate value remains inside each proof. -/
theorem pointwise_comp_left (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (F G H : Graph)
    (hGH : Pointwise T G H) : Pointwise T (comp F G) (comp F H) :=
  by
  intro n
  have h : 𝐏𝐀 ⊢ eqAt G H n ⇒ₗ eqAt (comp F G) (comp F H) n :=
    by
    apply complete.{0} 𝐏𝐀
    intro M _ _
    have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
    simp only [Semantics.Imp.models_imply, models_iff, eqAt_eval, Nat.succ_eq_add_one,
      Nat.reduceAdd, comp_eval, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.Fin1.eq_one, Matrix.cons_val_fin_one]
    intro hg z
    exact exists_congr fun y => and_congr (hg y) Iff.rfl
  exact Entailment.mdp (WeakerThan.pbl h) (hGH n)

/-- Standard equality of graph extensions is preserved in both arguments of
composition, without a functionality hypothesis. -/
theorem extensional_comp {F F' G G' : Graph} (hF : Extensional F F') (hG : Extensional G G') :
    Extensional (comp F G) (comp F' G') := by
  intro x z
  simp only [comp_eval, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  exact exists_congr fun y => and_congr (hG x y) (hF y z)

/-- The other variable of composition is automatically compatible, so full
congruence is equivalent to compatibility under right composition. -/
theorem congruence_iff_rightCompatible (T : ArithmeticTheory) [𝐏𝐀 ≼ T] :
    CompositionCongruence T ↔ RightCompatible T :=
  by
  constructor
  · intro h F H G hF hH hG hFH
    exact h F H G G hF hH hG hG hFH ((pointwise_equivalence T).refl G)
  · intro h F F' G G' hF hF' hG _ hFF' hGG'
    exact
      (pointwise_equivalence T).trans (h F F' G hF hF' hG hFF')
        (pointwise_comp_left T F' G G' hGG')

/-- Agreement between pointwise provability and standard graph equality on
functional graphs suffices for compatibility under right composition. -/
theorem rightCompatible_of_pointwise_iff_extensional (T : ArithmeticTheory)
    (h : AgreesWithExtensional T) : RightCompatible T :=
  by
  intro F H G hF hH hG hFH
  apply (h (comp F G) (comp H G) (comp_functional hF hG) (comp_functional hH hG)).mpr
  exact extensional_comp ((h F H hF hH).mp hFH) (fun _ _ => Iff.rfl)

/-- The same agreement gives full compatibility with composition. -/
theorem compositionCongruence_of_pointwise_iff_extensional (T : ArithmeticTheory)
    (h : AgreesWithExtensional T) : CompositionCongruence T :=
  by
  intro F F' G G' hF hF' hG hG' hFF' hGG'
  apply (h (comp F G) (comp F' G') (comp_functional hF hG) (comp_functional hF' hG')).mpr
  exact extensional_comp ((h F F' hF hF').mp hFF') ((h G G' hG hG').mp hGG')

end PiOneCharacterization
end FailureOfComposition

end

end PointwiseComposition
