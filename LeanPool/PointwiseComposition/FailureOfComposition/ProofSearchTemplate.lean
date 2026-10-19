/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.Meta.ClProver
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Incompleteness.StandardProvability

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Common arithmetic proof-search obstruction. This module does not use Gödel II.
U is the theory whose proofs are searched; T is the theory of pointwise equality.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping FFL.Entailment

namespace FailureOfComposition
namespace ProofSearch

noncomputable section

/-- The Graph construction in `FailureOfComposition.ProofSearch`. -/
abbrev Graph :=
  Σ₁.Semisentence 2

variable (U : ArithmeticTheory) [U.Δ₁] (σ : ArithmeticSentence)

/-- The proof Target construction in `FailureOfComposition.ProofSearch`. -/
def proofTarget : ∆₁.Semisentence 1 :=
  .mkDelta (.mkSigma (“p. !(proof U).sigma p !!(⌜σ⌝)”)) (.mkPi (“p. !(proof U).pi p !!(⌜σ⌝)”))

/-- The not Proof Target construction in `FailureOfComposition.ProofSearch`. -/
def notProofTarget : Σ₁.Semisentence 1 :=
  .mkSigma (“p. ¬!(proofTarget U σ).pi p”)

/-- The guard construction in `FailureOfComposition.ProofSearch`. -/
def guard : Graph :=
  .mkSigma (“x y. ¬!(proofTarget U σ).pi x ∧ y = x”)

/-- The search construction in `FailureOfComposition.ProofSearch`. -/
def search : Graph :=
  .mkSigma (“x p. !(proofTarget U σ).sigma p ∧ ∀ r < p, ¬!(proofTarget U σ).pi r”)

/-- The identity construction in `FailureOfComposition.ProofSearch`. -/
def identity : Graph :=
  .mkSigma (“x y. y = x”)

/-- The empty construction in `FailureOfComposition.ProofSearch`. -/
def empty : Graph :=
  .mkSigma “x y. ⊥”

/-- The comp construction in `FailureOfComposition.ProofSearch`. -/
def comp (F G : Graph) : Graph :=
  .mkSigma (“x z. ∃ y, !G.val x y ∧ !F.val y z”)

/-- The eq At construction in `FailureOfComposition.ProofSearch`. -/
def eqAt (F G : Graph) (n : ℕ) : ArithmeticSentence :=
  “∀ y, !F.val !!(n)y ↔ !G.val !!(n)y”

/-- The Pointwise construction in `FailureOfComposition.ProofSearch`. -/
def Pointwise (T : ArithmeticTheory) (F G : Graph) : Prop :=
  ∀ n : ℕ, T ⊢ eqAt F G n

/-- The uniform Sentence construction in `FailureOfComposition.ProofSearch`. -/
def uniformSentence (F G : Graph) : ArithmeticSentence :=
  “∀ x y, !F.val x y ↔ !G.val x y”

/-- The Uniform construction in `FailureOfComposition.ProofSearch`. -/
def Uniform (T : ArithmeticTheory) (F G : Graph) : Prop :=
  T ⊢ uniformSentence F G

/-- The functional Sentence construction in `FailureOfComposition.ProofSearch`. -/
def functionalSentence (F : Graph) : ArithmeticSentence :=
  “∀ x y z, (!F.val x y ∧ !F.val x z) → y = z”

/-- The Functional construction in `FailureOfComposition.ProofSearch`. -/
def Functional (F : Graph) : Prop :=
  𝐏𝐀 ⊢ functionalSentence F

section Semantics

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁]

@[simp]
theorem proofTarget_sigma_eval (v : Fin 1 → V) :
    (proofTarget U σ).sigma.val.Evalb v ↔ Proof U (v 0) (⌜σ⌝ : V) := by
  simp only [proofTarget, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_substs,
    HierarchySymbol.Defined.iff_delta_sigma,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Semiterm.val_bvar, Sentence.val_quote]

@[simp]
theorem proofTarget_pi_eval (v : Fin 1 → V) :
    (proofTarget U σ).pi.val.Evalb v ↔ Proof U (v 0) (⌜σ⌝ : V) := by
  simp only [proofTarget, HierarchySymbol.Semiformula.pi_mkDelta,
    HierarchySymbol.Semiformula.val_mkPi, Semiformula.eval_substs,
    HierarchySymbol.Defined.iff_delta_pi,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Semiterm.val_bvar, Sentence.val_quote]

@[simp]
theorem notProofTarget_eval (v : Fin 1 → V) :
    (notProofTarget U σ).val.Evalb v ↔ ¬Proof U (v 0) (⌜σ⌝ : V) := by simp [notProofTarget]

@[simp]
theorem guard_eval (v : Fin 2 → V) :
    (guard U σ).val.Evalb v ↔ ¬Proof U (v 0) (⌜σ⌝ : V) ∧ v 1 = v 0 := by simp [guard]

@[simp]
theorem search_eval (v : Fin 2 → V) :
    (search U σ).val.Evalb v ↔ Proof U (v 1) (⌜σ⌝ : V) ∧ ∀ r < v 1, ¬Proof U r (⌜σ⌝ : V) := by
  simp [search]

omit [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁] in
@[simp]
theorem identity_eval (v : Fin 2 → V) : identity.val.Evalb v ↔ v 1 = v 0 := by simp [identity]

omit [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁] in
@[simp]
theorem empty_eval (v : Fin 2 → V) : empty.val.Evalb v ↔ False := by simp [empty]

omit [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁] in
@[simp]
theorem comp_eval (F G : Graph) (v : Fin 2 → V) :
    (comp F G).val.Evalb v ↔ ∃ y : V, G.val.Evalb ![v 0, y] ∧ F.val.Evalb ![y, v 1] := by
  simp [comp]

@[simp]
theorem eqAt_eval (F G : Graph) (n : ℕ) :
    (eqAt F G n).Evalb (M := V) ![] ↔
      ∀ y : V, F.val.Evalb ![(n : V), y] ↔ G.val.Evalb ![(n : V), y] :=
  by simp [eqAt, numeral_eq_natCast]

omit [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁] in
@[simp]
theorem uniformSentence_eval (F G : Graph) :
    (uniformSentence F G).Evalb (M := V) ![] ↔
      ∀ x y : V, F.val.Evalb ![x, y] ↔ G.val.Evalb ![x, y] :=
  by simp [uniformSentence]

omit [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁] in
@[simp]
theorem functionalSentence_eval (F : Graph) :
    (functionalSentence F).Evalb (M := V) ![] ↔
      ∀ x y z : V, F.val.Evalb ![x, y] → F.val.Evalb ![x, z] → y = z :=
  by simp [functionalSentence]

end Semantics

/-- U does not prove σ, so PA proves every fixed negative proof check. -/
theorem numeral_negative (hσ : U ⊬ σ) (n : ℕ) : 𝐏𝐀 ⊢ (notProofTarget U σ).val/[n] :=
  by
  apply sigma_one_completeness (by simp [notProofTarget])
  simp only [models_iff, Semiformula.eval_substs]
  simp only [notProofTarget_eval]
  intro h
  exact hσ (Bootstrapping.Provable.sound ⟨n, by simpa using h⟩)

/-- An internal bridge for this exact named proof predicate. -/
theorem universal_negative_bridge :
    𝐏𝐀 ⊢ (“(∀ p, ¬!(proofTarget U σ).sigma p) ↔ ¬!(provabilityPred U σ)”) :=
  by
  apply complete.{0} 𝐏𝐀
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  simp [models_iff, provabilityPred, Bootstrapping.Provable]

theorem guard_functional : Functional (guard U σ) :=
  by
  apply complete.{0} 𝐏𝐀
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  exact (guard_eval U σ _).mp hy |>.2 |>.trans ((guard_eval U σ _).mp hz).2.symm

theorem identity_functional : Functional identity :=
  by
  apply complete.{0} 𝐏𝐀
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  simp [models_iff]

theorem search_functional : Functional (search U σ) :=
  by
  apply complete.{0} 𝐏𝐀
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  rw [search_eval] at hy hz
  rcases lt_trichotomy y z with h | h | h
  · exact False.elim (hz.2 y h hy.1)
  · exact h
  · exact False.elim (hy.2 z h hz.1)

theorem guard_pointwise_identity (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (hσ : U ⊬ σ) :
    Pointwise T (guard U σ) identity := by
  intro n
  have h : 𝐏𝐀 ⊢ (notProofTarget U σ).val/[n] ⇒ₗ eqAt (guard U σ) identity n :=
    by
    apply complete.{0} 𝐏𝐀
    intro V _ _
    simp [models_iff, notProofTarget, eqAt, guard, identity, Semiformula.eval_substs]
  exact WeakerThan.pbl (Entailment.mdp h (numeral_negative U σ hσ n))

theorem guard_search_empty : Uniform 𝐏𝐀 (comp (guard U σ) (search U σ)) empty :=
  by
  apply complete.{0} 𝐏𝐀
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  simp only [models_iff, uniformSentence_eval, Nat.succ_eq_add_one, Nat.reduceAdd, comp_eval,
    Fin.isValue, Matrix.cons_val_zero, search_eval, Matrix.cons_val_one, Fin.Fin1.eq_one,
    Matrix.cons_val_fin_one, guard_eval, exists_eq_right_right', empty_eval, iff_false, not_and,
    not_not, and_imp, forall_const]
  intro y hy _
  exact hy

theorem identity_comp (G : Graph) : Uniform 𝐏𝐀 (comp identity G) G :=
  by
  apply complete.{0} 𝐏𝐀
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  simp [models_iff]

theorem search_empty_implies_absence : 𝐏𝐀 ⊢ eqAt (search U σ) empty 0 ⇒ₗ ∼provabilityPred U σ :=
  by
  apply complete.{0} 𝐏𝐀
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  simp only [provabilityPred, Semantics.Imp.models_imply, models_iff, eqAt_eval,
    Nat.succ_eq_add_one, Nat.reduceAdd, Nat.cast_zero, search_eval, Fin.isValue,
    Matrix.cons_val_one, Fin.Fin1.eq_one, Matrix.cons_val_fin_one, empty_eval, iff_false,
    not_and, not_forall, not_not, Semantics.Not.models_not, Semiformula.eval_substs,
    Matrix.comp₁, Sentence.val_quote, HierarchySymbol.Defined.iff, Bootstrapping.Provable,
    not_exists]
  intro h p hp
  obtain ⟨q, hq, hmin⟩ :=
    InductionOnHierarchy.least_number_sigma ∆ 1 (P := fun p : V => Proof U p (⌜σ⌝ : V))
      (by definability) hp
  obtain ⟨r, hr, hpr⟩ := h q hq
  exact hmin r hr hpr

theorem composites_not_pointwise_equal (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hAbs : T ⊬ ∼provabilityPred U σ) :
    ¬Pointwise T (comp (guard U σ) (search U σ)) (comp identity (search U σ)) :=
  by
  intro h
  have himp :
    𝐏𝐀 ⊢
      eqAt (comp (guard U σ) (search U σ)) (comp identity (search U σ)) 0 ⇒ₗ
        eqAt (search U σ) empty 0 :=
    by
    apply complete.{0} 𝐏𝐀
    intro V _ _
    have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
    simp only [Semantics.Imp.models_imply, models_iff, eqAt_eval, Nat.succ_eq_add_one,
      Nat.reduceAdd, Nat.cast_zero, comp_eval, Fin.isValue, Matrix.cons_val_zero, search_eval,
      Matrix.cons_val_one, Fin.Fin1.eq_one, Matrix.cons_val_fin_one, guard_eval,
      exists_eq_right_right', identity_eval, exists_eq_right', and_iff_left_iff_imp, and_imp,
      empty_eval, iff_false, not_and, not_forall, not_not]
    intro h y hy
    by_contra hn
    have hmin : ∀ r < y, ¬Proof U r (⌜σ⌝ : V) := by simpa using hn
    exact h y hy hmin hy
  exact
    hAbs
      (Entailment.mdp (WeakerThan.pbl (search_empty_implies_absence U σ))
        (Entailment.mdp (WeakerThan.pbl himp) (h 0)))

theorem functional_graph_noncongruence (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (hσ : U ⊬ σ)
    (hAbs : T ⊬ ∼provabilityPred U σ) :
    ∃ F I G : Graph,
      Functional F ∧
        Functional I ∧ Functional G ∧ Pointwise T F I ∧ ¬Pointwise T (comp F G) (comp I G) :=
  by
  exact
    ⟨guard U σ, identity, search U σ, guard_functional U σ, identity_functional,
      search_functional U σ, guard_pointwise_identity U σ T hσ,
      composites_not_pointwise_equal U σ T hAbs⟩

end

end ProofSearch
end FailureOfComposition

end

end PointwiseComposition
