/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Incompleteness.StandardProvability

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

/-!
# Consistency predicate
-/



namespace FFL
namespace FirstOrder
namespace Arithmetic
namespace Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁]

section WitnessComparisons

variable {L : Language} [L.Encodable] [L.LORDefinable]

section

variable (T : Theory L) [T.Δ₁] (V)

/-- The Consistent construction in `FFL.FirstOrder.Theory`. -/
def _root_.PointwiseComposition.FFL.FirstOrder.Theory.Consistent : Prop :=
  ¬Provable T (⌜(⊥ : Sentence L)⌝ : V)

variable {V}

/-- The Consistent With construction in `FFL.FirstOrder.Theory`. -/
def _root_.PointwiseComposition.FFL.FirstOrder.Theory.ConsistentWith (φ : V) : Prop :=
  ¬Provable T (neg L φ)

lemma _root_.PointwiseComposition.FFL.FirstOrder.Theory.ConsistentWith.quote_iff
    {σ : Sentence L} : T.ConsistentWith (⌜σ⌝ : V) ↔ ¬Provable T (⌜∼σ⌝ : V) := by
  simp [Theory.ConsistentWith, Sentence.quote_def, Semiformula.quote_def]

section

/-- The consistent construction in `FFL.FirstOrder.Theory`. -/
noncomputable def _root_.PointwiseComposition.FFL.FirstOrder.Theory.consistent : Π₁.Sentence :=
  .mkPi (∼provabilityPred T ⊥)

@[simp]
lemma consistent.defined :
    (T.consistent : ArithmeticSentence).Evalb (M := V) ![] ↔ T.Consistent V := by
  simp [Theory.consistent, Theory.Consistent]

/-- The consistent With construction in `FFL.FirstOrder.Theory`. -/
noncomputable def _root_.PointwiseComposition.FFL.FirstOrder.Theory.consistentWith :
    Π₁.Semisentence 1 :=
  .mkPi (“φ. ∀ nφ, !(negGraph L)nφ φ → ¬!(provable T)nφ”)

instance consistentWith.defined :
    Π₁-Predicate (T.ConsistentWith : V → Prop) via T.consistentWith :=
  .mk fun v ↦ by simp [Theory.ConsistentWith, Theory.consistentWith]

instance consistentWith.definable : Π₁-Predicate (T.ConsistentWith : V → Prop) :=
  (consistentWith.defined T).to_definable

/-- The consistent With Pred construction in `FFL.FirstOrder.Theory`. -/
noncomputable abbrev _root_.PointwiseComposition.FFL.FirstOrder.Theory.consistentWithPred
    (σ : Sentence L) : ArithmeticSentence :=
  T.consistentWith.val/[⌜σ⌝]

/-- The consistent With Pred' construction in `FFL.FirstOrder.Theory`. -/
noncomputable def _root_.PointwiseComposition.FFL.FirstOrder.Theory.consistentWithPred'
    (σ : Sentence L) : Π₁.Sentence :=
  .mkPi (“!T.consistentWith !!(⌜σ⌝)”)

variable {T}

end

/-- The Con construction in `FFL.FirstOrder.Theory`. -/
abbrev _root_.PointwiseComposition.FFL.FirstOrder.Theory.Con : ArithmeticTheory :=
  { T.consistent.val }

/-- The Incon construction in `FFL.FirstOrder.Theory`. -/
abbrev _root_.PointwiseComposition.FFL.FirstOrder.Theory.Incon : ArithmeticTheory :=
  {∼T.consistent.val}

noncomputable instance : T.Con.Δ₁ :=
  Theory.Δ₁.singleton _

noncomputable instance : T.Incon.Δ₁ :=
  Theory.Δ₁.singleton _

end

variable (T : ArithmeticTheory) [T.Δ₁] (V)

theorem consistent_eq : T.consistent = T.standardProvability.con :=
  rfl

@[simp]
lemma standard_consistent : T.Consistent ℕ ↔ Entailment.Consistent T := by
  simp [Theory.Consistent, Entailment.consistent_iff_unprovable_bot]

end WitnessComparisons

end Bootstrapping
end Arithmetic
end FirstOrder
end FFL

namespace FFL
namespace FirstOrder
namespace Arithmetic

open _root_.PointwiseComposition.FFL.FirstOrder.Entailment

variable (T : ArithmeticTheory) [𝐈Σ₁ ≼ T] [T.Δ₁]

instance [ℕ↓[ℒₒᵣ] ⊧* T] : ℕ↓[ℒₒᵣ] ⊧* T ∪ T.Con :=
  by
  have : 𝐑₀ ≼ 𝐈Σ₁ := inferInstance
  have : 𝐑₀ ≼ T := Entailment.WeakerThan.trans this inferInstance
  have : Entailment.Consistent T := ArithmeticTheory.consistent_of_sound T (Eq ⊥) rfl
  simp [models_iff, *]

end Arithmetic
end FirstOrder
end FFL

end

end PointwiseComposition
