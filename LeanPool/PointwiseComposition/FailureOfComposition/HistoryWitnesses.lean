/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteEvaluatorGraph
public import Mathlib.Tactic.FinCases

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Arithmetic programs for the direct computation-search obstruction. The checked
function is the existing history evaluator at the diagonal input. All graph
equations in this file concern arbitrary PA-model inputs, not only numerals.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

open Nat.ArithPart₁

open CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition
namespace HistoryWitnesses

open ProofSearch

/-- The history Code construction in `FailureOfComposition.HistoryWitnesses`. -/
def historyCode (d : ℕ) : Code 1 :=
  codeHistoryEvaluator.comp ![Code.proj 0, codeConst d, codeConst d]

/-- The guard Code construction in `FailureOfComposition.HistoryWitnesses`. -/
def guardCode (d : ℕ) : Code 1 :=
  codeBind (codeLift (historyCode d)).rfind (Code.proj 1)

/-- The search Code construction in `FailureOfComposition.HistoryWitnesses`. -/
def searchCode (d : ℕ) : Code 1 :=
  codeRfindPos ((historyCode d).comp ![Code.proj 0])

/-- The raw History Graph construction in `FailureOfComposition.HistoryWitnesses`. -/
def rawHistoryGraph (d : ℕ) : Graph :=
  .mkSigma (code (historyCode d)) (code_sigma_one (historyCode d))

/-- The history Graph construction in `FailureOfComposition.HistoryWitnesses`. -/
def historyGraph (d : ℕ) : Graph :=
  (rawHistoryGraph d).rew (Rew.subst ![(#1 : ArithmeticSemiterm Empty 2), #0])

/-- The guard Graph construction in `FailureOfComposition.HistoryWitnesses`. -/
def guardGraph (d : ℕ) : Graph :=
  .mkSigma (“x y. !(historyGraph d).val x 0 ∧ y = x”)

/-- The search Graph construction in `FailureOfComposition.HistoryWitnesses`. -/
def searchGraph (d : ℕ) : Graph :=
  .mkSigma
    (“x y. (∃ z, 0 < z ∧ !(historyGraph d).val y z) ∧ ∀ r < y, !(historyGraph d).val r 0”)

variable {M : Type*} [ORingStructure M]

private theorem historyGraph_code_eval (d : ℕ) (s z : M) :
    (historyGraph d).val.Evalb ![s, z] ↔ Semiformula.Evalb ![z, s] (code (historyCode d)) :=
  by
  have hb :
    (fun x : Fin 2 =>
        Semiterm.val ![s, z] (Empty.elim : Empty → M)
          ((Rew.subst ![(#1 : ArithmeticSemiterm Empty 2), #0]) (#x : Semiterm ℒₒᵣ Empty 2))) =
      ![z, s] :=
    by
    funext x
    refine Fin.cases ?_ ?_ x
    · simp
    · intro i
      refine Fin.cases ?_ (fun j => Fin.elim0 j) i
      simp
  have hf :
    (fun x : Empty =>
        Semiterm.val ![s, z] (Empty.elim : Empty → M)
          ((Rew.subst ![(#1 : ArithmeticSemiterm Empty 2), #0]) (&x))) =
      Empty.elim :=
    funext (fun x => x.elim)
  simp only [historyGraph, rawHistoryGraph, HierarchySymbol.Semiformula.val_rew,
    HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_rew, Function.comp_def, hb, hf]

@[simp]
theorem guardGraph_eval (d : ℕ) (v : Fin 2 → M) :
    (guardGraph d).val.Evalb v ↔ (historyGraph d).val.Evalb ![v 0, 0] ∧ v 1 = v 0 := by
  simp [guardGraph]

@[simp]
theorem searchGraph_eval (d : ℕ) (v : Fin 2 → M) :
    (searchGraph d).val.Evalb v ↔
      (∃ z : M, 0 < z ∧ (historyGraph d).val.Evalb ![v 1, z]) ∧
        ∀ r < v 1, (historyGraph d).val.Evalb ![r, 0] :=
  by simp [searchGraph]

theorem eval_rfind_iff {n : ℕ} (c : Code (n + 1)) (y : M) (v : Fin n → M) :
    Semiformula.Evalb (y :> v) (code c.rfind) ↔
      Semiformula.Evalb ((0 : M) :> y :> v) (code c) ∧
        ∀ r < y, ∃ z : M, z ≠ 0 ∧ Semiformula.Evalb (z :> r :> v) (code c) :=
  by
  have bridge {k : ℕ} (a : Code k) (v : Fin (k + 1) → M) :
    Semiformula.Evalb v (code a) ↔ Semiformula.Evalf v (codeAux a) := by
    simp [code, Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def]
  simp only [bridge]
  simp [codeAux, Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons']

theorem historyCode_eval [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (d : ℕ) (s z : M) :
    Semiformula.Evalb ![z, s] (code (historyCode d)) ↔
      Semiformula.Evalb ![z, s, (d : M), (d : M)] (code codeHistoryEvaluator) :=
  by
  rw [historyCode, eval_comp_iff]
  constructor
  · rintro ⟨v, hv, hi⟩
    have h0 := (eval_proj_iff 0 (v 0) ![s]).mp (hi 0)
    have h1 := (eval_codeConst_iff d (v 1) ![s]).mp (hi 1)
    have h2 := (eval_codeConst_iff d (v 2) ![s]).mp (hi 2)
    have he : v = ![s, (d : M), (d : M)] := by ext i; fin_cases i <;> simp_all
    simpa only [he] using hv
  · intro h
    refine ⟨![s, (d : M), (d : M)], h, ?_⟩
    intro i
    fin_cases i
    · exact (eval_proj_iff _ _ _).mpr rfl
    · exact eval_codeConst d ![s]
    · exact eval_codeConst d ![s]

@[simp]
theorem historyGraph_eval [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (d : ℕ) (s z : M) :
    (historyGraph d).val.Evalb ![s, z] ↔
      Semiformula.Evalb ![z, s, (d : M), (d : M)] (code codeHistoryEvaluator) :=
  by exact (historyGraph_code_eval d s z).trans (historyCode_eval d s z)

theorem history_total [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (d : ℕ) (s : M) :
    ∃ z : M, (historyGraph d).val.Evalb ![s, z] := by
  simpa using eval_codeHistoryEvaluator_exists s (d : M) (d : M)

theorem history_unique [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (d : ℕ) (s a b : M)
    (ha : (historyGraph d).val.Evalb ![s, a]) (hb : (historyGraph d).val.Evalb ![s, b]) :
    a = b :=
  eval_unique ((historyGraph_eval d s a).mp ha) ((historyGraph_eval d s b).mp hb)

theorem headHistory_eval (d : ℕ) (s x z : M) :
    Semiformula.Evalb ![z, s, x] (code ((historyCode d).comp ![Code.proj 0])) ↔
      Semiformula.Evalb ![z, s] (code (historyCode d)) :=
  by
  rw [eval_comp_iff]
  constructor
  · rintro ⟨v, hv, hi⟩
    have h0 : v 0 = s := (eval_proj_iff _ _ _).mp (hi 0)
    have he : v = ![s] := by ext i; fin_cases i; exact h0
    simpa only [he] using hv
  · intro h
    exact ⟨![s], h, fun i => by fin_cases i; exact (eval_proj_iff _ _ _).mpr rfl⟩

theorem guardCode_eval [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (d : ℕ) (x y : M) :
    Semiformula.Evalb ![y, x] (code (guardCode d)) ↔ (guardGraph d).val.Evalb ![x, y] :=
  by
  simp only [guardCode, eval_codeBind_iff, eval_proj_iff, eval_rfind_iff, eval_codeLift_iff,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [guardGraph_eval, historyGraph_code_eval]
  constructor
  · rintro ⟨_, ⟨h, _⟩, hy⟩
    exact ⟨h, hy⟩
  · rintro ⟨h, hy⟩
    refine ⟨0, ⟨h, ?_⟩, hy⟩
    intro r hr
    exact False.elim ((not_lt_of_ge (Arithmetic.zero_le r)) hr)

theorem searchCode_eval [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (d : ℕ) (x y : M) :
    Semiformula.Evalb ![y, x] (code (searchCode d)) ↔ (searchGraph d).val.Evalb ![x, y] :=
  by
  rw [searchCode, eval_codeRfindPos_iff]
  rw [searchGraph_eval]
  exact
    and_congr
      (exists_congr fun z =>
        and_congr Iff.rfl
          ((headHistory_eval d y x z).trans (historyGraph_code_eval d y z).symm))
      (forall_congr' fun r =>
        imp_congr Iff.rfl
          ((headHistory_eval d r x 0).trans (historyGraph_code_eval d r 0).symm))

theorem guard_functional (d : ℕ) : Functional (guardGraph d) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  simp only [models_iff, functionalSentence_eval, guardGraph_eval, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  intro x y z hy hz
  exact hy.2.trans hz.2.symm

theorem search_functional (d : ℕ) : Functional (searchGraph d) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  obtain ⟨⟨a, ha, hay⟩, hminy⟩ := (searchGraph_eval d _).mp hy
  obtain ⟨⟨b, hb, hbz⟩, hminz⟩ := (searchGraph_eval d _).mp hz
  rcases lt_trichotomy y z with h | h | h
  · exact False.elim ((ne_of_gt ha) (history_unique d y a 0 hay (hminz y h)))
  · exact h
  · exact False.elim ((ne_of_gt hb) (history_unique d z b 0 hbz (hminy z h)))

theorem guard_search_empty (d : ℕ) : Uniform 𝐏𝐀 (comp (guardGraph d) (searchGraph d)) empty :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  simp only [comp_eval, empty_eval, iff_false]
  rintro ⟨z, hz, hg⟩
  obtain ⟨⟨a, ha, haz⟩, _⟩ := (searchGraph_eval d _).mp hz
  have h0 := ((guardGraph_eval d _).mp hg).1
  exact (ne_of_gt ha) (history_unique d z a 0 haz h0)

end HistoryWitnesses
end FailureOfComposition

end

end PointwiseComposition
