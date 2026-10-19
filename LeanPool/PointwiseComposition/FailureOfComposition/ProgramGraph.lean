/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteEvaluatorGraph
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteConstructorGraphs

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Program graphs indexed by actual Mathlib program descriptions. -/

@[expose] public section

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition
namespace ProgramGraph

open ConcreteEvaluator

/-- The PCode construction in `FailureOfComposition.ProgramGraph`. -/
abbrev PCode :=
  Nat.Partrec.Code

/-- The Computes construction in `FailureOfComposition.ProgramGraph`. -/
def Computes {M : Type*} [ORingStructure M] (c : PCode) (x y : M) : Prop :=
  (eventualGraph (encode c)).val.Evalb ![x, y]

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

omit [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] in
theorem computes_comp (f g : PCode) (x z : M) :
    Computes (.comp f g) x z ↔ ∃ y : M, Computes g x y ∧ Computes f y z :=
  by
  have he :
    canonicalPartrecCompIndex (encode f) (encode g) = encode (Nat.Partrec.Code.comp f g) := by
    simp only [canonicalPartrecCompIndex, Denumerable.ofNat_encode]
  simpa only [he, Computes] using eventualGraph_comp_eval (encode f) (encode g) x z

theorem computes_zero (x y : M) : Computes .zero x y ↔ y = 0 :=
  by
  simp only [Computes, show encode (Nat.Partrec.Code.zero) = 0 from rfl, eventualGraph_eval,
    numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one]
  simpa [ConcreteWitnessGraphs.baseOutput] using
    ConcreteWitnessGraphs.base_unbounded_computation_iff 0 (by decide) x y

theorem computes_succ (x y : M) : Computes .succ x y ↔ y = x + 1 :=
  by
  simp only [Computes, show encode (Nat.Partrec.Code.succ) = 1 from rfl, eventualGraph_eval,
    numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one]
  simpa [ConcreteWitnessGraphs.baseOutput] using
    ConcreteWitnessGraphs.base_unbounded_computation_iff 1 (by decide) x y

theorem computes_left (x y : M) : Computes .left x y ↔ y = pi₁ x :=
  by
  simp only [Computes, show encode (Nat.Partrec.Code.left) = 2 from rfl, eventualGraph_eval,
    numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one]
  simpa [ConcreteWitnessGraphs.baseOutput] using
    ConcreteWitnessGraphs.base_unbounded_computation_iff 2 (by decide) x y

theorem computes_right (x y : M) : Computes .right x y ↔ y = pi₂ x :=
  by
  simp only [Computes, show encode (Nat.Partrec.Code.right) = 3 from rfl, eventualGraph_eval,
    numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one]
  simpa [ConcreteWitnessGraphs.baseOutput] using
    ConcreteWitnessGraphs.base_unbounded_computation_iff 3 (by decide) x y

theorem computes_id (x y : M) : Computes Nat.Partrec.Code.id x y ↔ y = x :=
  by
  have hu :
    M↓[ℒₒᵣ] ⊧
      ProofSearch.uniformSentence (eventualGraph Kleene.identityIndex) ProofSearch.identity :=
    consequence_iff.mp (Theory.Proof.sound eventualGraph_identity) M inferInstance
  simp only [models_iff, ProofSearch.uniformSentence_eval] at hu
  simpa only [Computes, Kleene.identityIndex, ProofSearch.identity_eval, Matrix.cons_val_zero,
    Matrix.cons_val_one] using hu x y

theorem computes_pair (f g : PCode) (x z : M) :
    Computes (.pair f g) x z ↔ ∃ a b : M, Computes f x a ∧ Computes g x b ∧ z = pair a b :=
  eventualGraph_pair_code_eval f g x z

theorem computes_const (n : ℕ) (x y : M) :
    Computes (Nat.Partrec.Code.const n) x y ↔ y = (n : M) := by
  induction n generalizing x y with
  | zero => simpa only [Nat.Partrec.Code.const, Nat.cast_zero] using computes_zero x y
  | succ n ih =>
    rw [Nat.Partrec.Code.const, computes_comp]
    simp only [ih, computes_succ, exists_eq_left, Nat.cast_add, Nat.cast_one]

omit [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] in
theorem computes_unique (c : PCode) (x y z : M) (hy : Computes c x y) (hz : Computes c x z) :
    y = z :=
  eventualGraph_output_unique (encode c) x y z hy hz

end ProgramGraph
end FailureOfComposition

end

end PointwiseComposition
