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
# Witness comparisons of provability
-/

namespace FFL
namespace FirstOrder
namespace Arithmetic
namespace Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁]

section WitnessComparisons

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable (T : Theory L) [T.Δ₁]

/-- The Provability Comparison LE construction in `FFL.FirstOrder.Theory`. -/
def _root_.PointwiseComposition.FFL.FirstOrder.Theory.ProvabilityComparisonLE (φ ψ : V) :
    Prop :=
  ∃ b, Proof T b φ ∧ ∀ b' < b, ¬Proof T b' ψ

/-- The Provability Comparison LT construction in `FFL.FirstOrder.Theory`. -/
def _root_.PointwiseComposition.FFL.FirstOrder.Theory.ProvabilityComparisonLT (φ ψ : V) :
    Prop :=
  ∃ b, Proof T b φ ∧ ∀ b' ≤ b, ¬Proof T b' ψ

section

/-- The provability Comparison LE construction in `FFL.FirstOrder.Theory`. -/
noncomputable def _root_.PointwiseComposition.FFL.FirstOrder.Theory.provabilityComparisonLE :
    Σ₁.Semisentence 2 :=
  .mkSigma (“φ ψ. ∃ b, !(proof T).sigma b φ ∧ ∀ b' < b, ¬!(proof T).pi b' ψ”)

instance _root_.PointwiseComposition.FFL.FirstOrder.Theory.provability_comparison_le_defined :
    Σ₁-Relation[V] T.ProvabilityComparisonLE via T.provabilityComparisonLE :=
  .mk fun v ↦ by simp [Theory.provabilityComparisonLE, Theory.ProvabilityComparisonLE]

instance _root_.PointwiseComposition.FFL.FirstOrder.Theory.provability_comparison_le_definable :
    Σ₁-Relation[V] T.ProvabilityComparisonLE :=
  T.provability_comparison_le_defined.to_definable

/-- instance for definability tactic -/
instance
  _root_.PointwiseComposition.FFL.FirstOrder.Theory.provability_comparison_le_definable' :
    Σ-[0 + 1]-Relation[V] T.ProvabilityComparisonLE :=
  T.provability_comparison_le_definable

/-- The provability Comparison LT construction in `FFL.FirstOrder.Theory`. -/
noncomputable def _root_.PointwiseComposition.FFL.FirstOrder.Theory.provabilityComparisonLT :
    Σ₁.Semisentence 2 :=
  .mkSigma (“φ ψ. ∃ b, !(proof T).sigma b φ ∧ ∀ b' <⁺ b, ¬!(proof T).pi b' ψ”)

instance _root_.PointwiseComposition.FFL.FirstOrder.Theory.provability_comparison_lt_defined :
    Σ₁-Relation[V] T.ProvabilityComparisonLT via T.provabilityComparisonLT :=
  .mk fun v ↦ by simp [Theory.provabilityComparisonLT, Theory.ProvabilityComparisonLT]

instance _root_.PointwiseComposition.FFL.FirstOrder.Theory.provability_comparison_lt_definable :
    Σ₁-Relation[V] T.ProvabilityComparisonLT :=
  T.provability_comparison_lt_defined.to_definable

/-- instance for definability tactic -/
instance
  _root_.PointwiseComposition.FFL.FirstOrder.Theory.provability_comparison_lt_definable' :
    Σ-[0 + 1]-Relation[V] T.ProvabilityComparisonLT :=
  T.provability_comparison_lt_definable

end

variable {T : Theory L} [T.Δ₁]

namespace ProvabilityComparison

variable {φ ψ χ : V}

local infixl:50 "≼" => T.ProvabilityComparisonLE

local infixl:50 "≺" => T.ProvabilityComparisonLT

local prefix:50 "□" => Provable T

@[grind =>]
lemma le_of_lt : φ ≺ ψ → φ ≼ ψ := by rintro ⟨b, _⟩; exact ⟨b, by grind⟩

@[grind =>]
lemma le_to_provable : φ ≼ ψ → □φ := by rintro ⟨b, hb, _⟩; exact ⟨b, by grind⟩

@[grind =>]
lemma le_trans : φ ≼ ψ → ψ ≼ χ → φ ≼ χ := by rintro ⟨b, hb, h⟩ ⟨d, hd, H⟩; use b; grind;

@[grind =>]
lemma le_antisymm : φ ≼ ψ → ψ ≼ φ → φ = ψ :=
  by
  rintro ⟨b, hb, Hb⟩ ⟨d, hd, Hd⟩
  have : b = d := by
    by_contra ne
    wlog lt : b < d
    · grind;
    have : ¬Proof T b φ := Hd b lt
    contradiction
  have : ({ φ } : V) = { ψ } := by simp [← hb.1, ← hd.1, this]
  simpa using this

lemma iff_le_refl_provable : φ ≼ φ ↔ □φ :=
  by
  constructor
  · exact le_to_provable
  · rintro ⟨b, hb⟩
    have : ∃ b, Proof T b φ ∧ ∀ z < b, ¬Proof T z φ :=
      InductionOnHierarchy.least_number_sigma Σ 1 (P := (Proof T · φ)) (by definability) hb
    rcases this with ⟨b, bd, h⟩
    exact ⟨b, bd, h⟩

@[grind .]
lemma lt_irrefl : ¬φ≺φ := by
  rintro ⟨b, hb, h⟩; have : ¬Proof T b φ := h b (by simp);
  contradiction

@[grind =>]
lemma lt_trans : φ ≺ ψ → ψ ≺ χ → φ ≺ χ := by rintro ⟨b, hb, h⟩ ⟨d, hd, H⟩; use b; grind;

@[grind =>]
lemma not_lt_of_le : φ ≼ ψ → ¬ψ ≺ φ := by grind;

lemma find_minimal_proof_fintype {ι : Type*} [_root_.Finite ι] (φ : ι → V) {i : ι}
    (H : □(φ i)) :
    ∃ j, ∀ k, (φ j) ≼ (φ k) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rcases show ∃ dᵢ, Proof T dᵢ (φ i)from H with ⟨dᵢ, Hdᵢ⟩
  have : ∃ z, (∃ j, Proof T z (φ j)) ∧ ∀ w < z, ∀ x, ¬Proof T w (φ x) := by
    simpa using
      InductionOnHierarchy.least_number_sigma Σ 1 (P := fun z ↦ ∃ j, Proof T z (φ j))
        (HierarchySymbol.Definable.fintype_exs fun j ↦ by definability) (x := dᵢ) ⟨i, Hdᵢ⟩
  rcases this with ⟨z, ⟨j, hj⟩, H⟩
  exact ⟨j, fun k ↦ ⟨z, hj, fun w hw ↦ H w hw k⟩⟩



end ProvabilityComparison

end WitnessComparisons

end Bootstrapping
end Arithmetic
end FirstOrder
end FFL

end

end PointwiseComposition
