/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteEvaluatorGraph

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Functional Sigma-one witnesses for adjoining composition to pointwise equality.
The first witness records the least successful evaluator stage and the input;
the other two read that computation, with an optional second graph condition.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

open CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition
namespace GeneratedWitnessGraphs

open ProofSearch ConcreteEvaluator

/-- The stage Graph construction in `FailureOfComposition.GeneratedWitnessGraphs`. -/
def stageGraph (e : ℕ) : Σ₁.Semisentence 3 :=
  .mkSigma (“s x y. !evalnCertificateFormula.val s !!(e)x y”)

/-- The failure Graph construction in `FailureOfComposition.GeneratedWitnessGraphs`. -/
def failureGraph (e : ℕ) : Graph :=
  .mkSigma (“s x. !evalnGraphFormula.val 0s !!(e)x”)

/-- The least Graph construction in `FailureOfComposition.GeneratedWitnessGraphs`. -/
def leastGraph (e : ℕ) : Graph :=
  .mkSigma (“x s. (∃ y, !(stageGraph e).val s x y) ∧ ∀ r < s, !(failureGraph e).val r x”)

/-- The HGraph construction in `FailureOfComposition.GeneratedWitnessGraphs`. -/
def HGraph (e : ℕ) : Graph :=
  .mkSigma (“x n. ∃ s, !(leastGraph e).val x s ∧ !pairDef n s x”)

/-- The BGraph construction in `FailureOfComposition.GeneratedWitnessGraphs`. -/
def BGraph (e : ℕ) : Graph :=
  .mkSigma (“n y. ∃ s x, !pairDef n s x ∧ !(stageGraph e).val s x y”)

/-- The AGraph construction in `FailureOfComposition.GeneratedWitnessGraphs`. -/
def AGraph (e : ℕ) (G : Graph) : Graph :=
  .mkSigma (“n y. ∃ s x, !pairDef n s x ∧ !(stageGraph e).val s x y ∧ !G.val x y”)

/-- The intersection construction in `FailureOfComposition.GeneratedWitnessGraphs`. -/
def intersection (F G : Graph) : Graph :=
  .mkSigma (“x y. !F.val x y ∧ !G.val x y”)

section Semantics

variable {M : Type*} [ORingStructure M]

section

variable [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

@[simp]
theorem stageGraph_eval (e : ℕ) (s x y : M) :
    (stageGraph e).val.Evalb ![s, x, y] ↔
      Semiformula.Evalb ![s, (e : M), x, y]
        (evalnCertificateFormula : ArithmeticSemisentence 4) :=
  by simp [stageGraph, numeral_eq_natCast]

@[simp]
theorem failureGraph_eval (e : ℕ) (s x : M) :
    (failureGraph e).val.Evalb ![s, x] ↔
      Semiformula.Evalb ![0, s, (e : M), x] (code codeHistoryEvaluator) :=
  by simp [failureGraph, evalnGraphFormula, numeral_eq_natCast]

theorem stage_of_history (e : ℕ) (s x y : M) :
    (stageGraph e).val.Evalb ![s, x, y] ↔
      Semiformula.Evalb ![y + 1, s, (e : M), x] (code codeHistoryEvaluator) :=
  by rw [stageGraph_eval, evalnCertificateFormula_eval_history_iff]

end

section

variable [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

theorem history_total (e : ℕ) (s x : M) :
    ∃ z : M, Semiformula.Evalb ![z, s, (e : M), x] (code codeHistoryEvaluator) :=
  eval_codeHistoryEvaluator_exists s (e : M) x

end

section

variable [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

theorem stage_implies_eventual (e : ℕ) (s x y : M) (h : (stageGraph e).val.Evalb ![s, x, y]) :
    (eventualGraph e).val.Evalb ![x, y] :=
  by
  apply (eventualGraph_eval e _).mpr
  refine ⟨s, ?_⟩
  simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using
    (stageGraph_eval e s x y).mp h

end

section

variable [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

theorem stage_unique (e : ℕ) (s x a b : M) (ha : (stageGraph e).val.Evalb ![s, x, a])
    (hb : (stageGraph e).val.Evalb ![s, x, b]) : a = b :=
  eventualGraph_output_unique e x a b (stage_implies_eventual e s x a ha)
    (stage_implies_eventual e s x b hb)

theorem failure_iff_no_stage (e : ℕ) (s x : M) :
    (failureGraph e).val.Evalb ![s, x] ↔ ¬∃ y : M, (stageGraph e).val.Evalb ![s, x, y] :=
  by
  constructor
  · intro hzero
    rintro ⟨y, hy⟩
    have he : y + 1 = 0 :=
      eval_unique ((stage_of_history e s x y).mp hy) ((failureGraph_eval e s x).mp hzero)
    exact (ne_of_gt (lt_of_le_of_lt (Arithmetic.zero_le y) (lt_add_one y))) he
  · intro hn
    obtain ⟨z, hz⟩ := history_total e s x
    have hz0 : z = 0 :=
      le_antisymm
        (not_lt.mp
          (fun hpos =>
            hn
              ⟨z - 1,
                (stage_of_history e s x (z - 1)).mpr
                  (by
                    rw [Arithmetic.sub_add_self_of_le (Arithmetic.one_le_of_zero_lt z hpos)]
                    exact hz)⟩))
        (Arithmetic.zero_le z)
    exact (failureGraph_eval e s x).mpr (by simpa only [hz0] using hz)

end

section

variable [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

@[simp]
theorem leastGraph_eval (e : ℕ) (x s : M) :
    (leastGraph e).val.Evalb ![x, s] ↔
      (∃ y : M, (stageGraph e).val.Evalb ![s, x, y]) ∧
        ∀ r < s, (failureGraph e).val.Evalb ![r, x] :=
  by simp [leastGraph]

@[simp]
theorem HGraph_eval (e : ℕ) (x n : M) :
    (HGraph e).val.Evalb ![x, n] ↔ ∃ s : M, (leastGraph e).val.Evalb ![x, s] ∧ n = pair s x :=
  by simp [HGraph]

@[simp]
theorem BGraph_pair_eval (e : ℕ) (s x y : M) :
    (BGraph e).val.Evalb ![pair s x, y] ↔ (stageGraph e).val.Evalb ![s, x, y] := by
  simp [BGraph]

@[simp]
theorem AGraph_pair_eval (e : ℕ) (G : Graph) (s x y : M) :
    (AGraph e G).val.Evalb ![pair s x, y] ↔
      (stageGraph e).val.Evalb ![s, x, y] ∧ G.val.Evalb ![x, y] :=
  by simp [AGraph]

end

@[simp]
theorem intersection_eval (F G : Graph) (x y : M) :
    (intersection F G).val.Evalb ![x, y] ↔ F.val.Evalb ![x, y] ∧ G.val.Evalb ![x, y] := by
  simp [intersection]

section

variable [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

theorem leastGraph_unique (e : ℕ) (x s t : M) (hs : (leastGraph e).val.Evalb ![x, s])
    (ht : (leastGraph e).val.Evalb ![x, t]) : s = t :=
  by
  obtain ⟨hs, hmins⟩ := (leastGraph_eval e x s).mp hs
  obtain ⟨ht, hmint⟩ := (leastGraph_eval e x t).mp ht
  rcases lt_trichotomy s t with h | h | h
  · exact False.elim ((failure_iff_no_stage e s x).mp (hmint s h) hs)
  · exact h
  · exact False.elim ((failure_iff_no_stage e t x).mp (hmins t h) ht)

theorem leastGraph_exists (e : ℕ) (x y : M) (hy : (eventualGraph e).val.Evalb ![x, y]) :
    ∃ s : M, (leastGraph e).val.Evalb ![x, s] ∧ (stageGraph e).val.Evalb ![s, x, y] :=
  by
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  obtain ⟨s, hs⟩ := (eventualGraph_eval e _).mp hy
  have hs' : (stageGraph e).val.Evalb ![s, x, y] :=
    by
    apply (stageGraph_eval e s x y).mpr
    simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using hs
  let P : M → Prop := fun s => ∃ z : M, (stageGraph e).val.Evalb ![s, x, z]
  have hP : Σ₁-Predicate P :=
    by
    refine ⟨.mkSigma (“s. ∃ z, !(Rew.emb ▹ (stageGraph e).val)s&x z”), ?_⟩
    intro v
    simp [P, Semiformula.eval_emb]
  obtain ⟨t, ⟨z, hz⟩, hmin⟩ := InductionOnHierarchy.least_number_sigma Σ 1 hP ⟨y, hs'⟩
  have hzy : z = y := eventualGraph_output_unique e x z y (stage_implies_eventual e t x z hz) hy
  subst z
  refine ⟨t, (leastGraph_eval e x t).mpr ⟨⟨y, hz⟩, ?_⟩, hz⟩
  intro r hr
  exact (failure_iff_no_stage e r x).mpr (hmin r hr)

theorem B_comp_H_eval (e : ℕ) (x y : M) :
    (comp (BGraph e) (HGraph e)).val.Evalb ![x, y] ↔ (eventualGraph e).val.Evalb ![x, y] :=
  by
  rw [comp_eval]
  constructor
  · rintro ⟨n, hn, hb⟩
    obtain ⟨s, _, rfl⟩ := (HGraph_eval e x n).mp hn
    exact stage_implies_eventual e s x y ((BGraph_pair_eval e s x y).mp hb)
  · intro h
    obtain ⟨s, hs, hy⟩ := leastGraph_exists e x y h
    exact ⟨pair s x, (HGraph_eval e x _).mpr ⟨s, hs, rfl⟩, (BGraph_pair_eval e s x y).mpr hy⟩

theorem A_comp_H_eval (e : ℕ) (G : Graph) (x y : M) :
    (comp (AGraph e G) (HGraph e)).val.Evalb ![x, y] ↔
      (intersection (eventualGraph e) G).val.Evalb ![x, y] :=
  by
  rw [comp_eval, intersection_eval]
  constructor
  · rintro ⟨n, hn, ha⟩
    obtain ⟨s, _, rfl⟩ := (HGraph_eval e x n).mp hn
    obtain ⟨hs, hg⟩ := (AGraph_pair_eval e G s x y).mp ha
    exact ⟨stage_implies_eventual e s x y hs, hg⟩
  · rintro ⟨he, hg⟩
    obtain ⟨s, hs, hy⟩ := leastGraph_exists e x y he
    exact
      ⟨pair s x, (HGraph_eval e x _).mpr ⟨s, hs, rfl⟩,
        (AGraph_pair_eval e G s x y).mpr ⟨hy, hg⟩⟩

end

end Semantics

theorem intersection_functional (F G : Graph) (hF : Functional F) :
    Functional (intersection F G) := by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have hf : M↓[ℒₒᵣ] ⊧ functionalSentence F :=
    consequence_iff.mp (Theory.Proof.sound hF) M inferInstance
  rw [models_iff, functionalSentence_eval] at hf ⊢
  intro x y z hy hz
  exact hf x y z ((intersection_eval F G x y).mp hy).1 ((intersection_eval F G x z).mp hz).1

theorem intersection_comm_uniform (F G : Graph) :
    Uniform 𝐏𝐀 (intersection F G) (intersection G F) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  intro x y
  simp only [intersection_eval, and_comm]

theorem HGraph_functional (e : ℕ) : Functional (HGraph e) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  rw [models_iff, functionalSentence_eval]
  intro x a b ha hb
  obtain ⟨s, hs, rfl⟩ := (HGraph_eval e x a).mp ha
  obtain ⟨t, ht, rfl⟩ := (HGraph_eval e x b).mp hb
  rw [leastGraph_unique e x s t hs ht]

theorem BGraph_functional (e : ℕ) : Functional (BGraph e) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  rw [models_iff, functionalSentence_eval]
  intro n a b ha hb
  rw [← pair_unpair n, BGraph_pair_eval] at ha hb
  exact stage_unique e (pi₁ n) (pi₂ n) a b ha hb

theorem AGraph_functional (e : ℕ) (G : Graph) : Functional (AGraph e G) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  rw [models_iff, functionalSentence_eval]
  intro n a b ha hb
  rw [← pair_unpair n, AGraph_pair_eval] at ha hb
  exact stage_unique e (pi₁ n) (pi₂ n) a b ha.1 hb.1

theorem B_comp_H (e : ℕ) : Uniform 𝐏𝐀 (comp (BGraph e) (HGraph e)) (eventualGraph e) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  rw [models_iff, uniformSentence_eval]
  exact B_comp_H_eval e

theorem A_comp_H (e : ℕ) (G : Graph) :
    Uniform 𝐏𝐀 (comp (AGraph e G) (HGraph e)) (intersection (eventualGraph e) G) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  rw [models_iff, uniformSentence_eval]
  exact A_comp_H_eval e G

end GeneratedWitnessGraphs
end FailureOfComposition

end

end PointwiseComposition
