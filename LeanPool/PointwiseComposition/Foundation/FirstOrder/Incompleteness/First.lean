/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Incompleteness.StandardProvability
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.R0.Representation
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.CraigTrick

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

/-!
# Gödel's first incompleteness theorem for arithmetic theories stronger than $\mathsf{R_0}$
-/

namespace FFL
namespace FirstOrder
namespace Arithmetic

open FFL.Entailment Bootstrapping Bootstrapping.ObjectArithmetic

/-- Gödel's first incompleteness theorem -/
theorem incomplete (T : ArithmeticTheory) [T.Δ₁] [𝐑₀ ≼ T] [T.SoundOnHierarchy Σ 1] :
    Incomplete T := by
  have con : Consistent T := inferInstance
  let D : ℕ → Prop := fun φ : ℕ ↦
    IsSemiformula ℒₒᵣ 1 φ ∧ Provable T (neg ℒₒᵣ <| subst ℒₒᵣ ?[numeral φ] φ)
  have D_re : REPred D :=
    by
    have :
      Σ₁-Predicate fun φ : ℕ ↦
        IsSemiformula ℒₒᵣ 1 φ ∧ Provable T (neg ℒₒᵣ <| subst ℒₒᵣ ?[numeral φ] φ) :=
      by definability
    exact rePred_iff_sigma1.mpr this
  have D_spec (φ : ArithmeticSemisentence 1) : D ⌜φ⌝ ↔ T ⊢ ∼φ/[⌜φ⌝] := by
    simp [D, ← provable_iff_provable, Sentence.quote_def, Rewriting.emb_subst_eq_subst_coe₁,
      Semiformula.quote_def]
  let δ : ArithmeticSemisentence 1 := codeOfREPred D
  have (n : ℕ) : D n ↔ T ⊢ δ/[↑n] := by
    simpa [Semiformula.coe_subst_eq_subst_coe₁] using rePred_weak_representation D_re
  let π : ArithmeticSentence := δ/[⌜δ⌝]
  have : T ⊢ π ↔ T ⊢ ∼π :=
    calc
      T ⊢ π ↔ T ⊢ δ/[⌜δ⌝] := by rfl
      _ ↔ D ⌜δ⌝ := by simpa using (this ⌜δ⌝).symm
      _ ↔ T ⊢ ∼δ/[⌜δ⌝] := (D_spec δ)
      _ ↔ T ⊢ ∼π := by rfl
  refine incomplete_def.mpr ⟨π, ?_, ?_⟩
  · intro h
    exact
      not_consistent_iff_inconsistent.mpr (inconsistent_of_provable_of_unprovable h (this.mp h))
        inferInstance
  · intro h
    exact
      not_consistent_iff_inconsistent.mpr
        (inconsistent_of_provable_of_unprovable (this.mpr h) h) inferInstance

theorem exists_true_but_unprovable_sentence_of_sigma1sound (T : ArithmeticTheory) [T.Δ₁]
    [𝐑₀ ≼ T] [T.SoundOnHierarchy Σ 1] : ∃ δ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ δ ∧ T ⊬ δ :=
  exists_true_but_unprovable_sentence_of_incomplete (Arithmetic.incomplete T)

instance {T : ArithmeticTheory} [T.RE] [𝐑₀ ≼ T] : 𝐑₀ ≼ T.craig :=
  WeakerThan.trans (𝓣 := T) inferInstance (inferInstance : T ≼ T.craig)

instance {T : ArithmeticTheory} [T.RE] [T.SoundOnHierarchy Σ 1] :
    ArithmeticTheory.SoundOnHierarchy (T.craig) Σ 1 :=
  ArithmeticTheory.SoundOn.of_weakerThan _ T T.craig

/-- Gödel's first incompleteness theorem for r.e. theories -/
theorem incomplete_of_RE (T : ArithmeticTheory) [T.RE] [𝐑₀ ≼ T] [T.SoundOnHierarchy Σ 1] :
    Incomplete T :=
  (Equiv.incomplete_iff (inferInstance : T ≊ T.craig)).mpr (incomplete T.craig)

theorem exists_true_but_unprovable_sentence_of_RE_of_sigma1sound (T : ArithmeticTheory) [T.RE]
    [𝐑₀ ≼ T] [T.SoundOnHierarchy Σ 1] : ∃ δ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ δ ∧ T ⊬ δ :=
  exists_true_but_unprovable_sentence_of_incomplete (incomplete_of_RE T)

instance {T : ArithmeticTheory} [ℕ↓[ℒₒᵣ] ⊧* T] [T.Δ₁] [𝐑₀ ≼ T] [T.SoundOnHierarchy Σ 1] :
    T ≺ 𝐓𝐀 := by
  constructor; · infer_instance
  · obtain ⟨δ, δTrue, δUnprov⟩ := exists_true_but_unprovable_sentence_of_sigma1sound T;
    exact not_weakerThan_iff.mpr ⟨δ, TA.provable_iff.mpr δTrue, δUnprov⟩

end Arithmetic
end FirstOrder
end FFL

end

end PointwiseComposition
