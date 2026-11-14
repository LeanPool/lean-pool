/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ArithmeticCodeCompiler
public import LeanPool.PointwiseComposition.FailureOfComposition.HistoryWitnesses

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Fair search and disjunction for the concrete program numbering. The searched
arithmetic tests are total history-evaluator computations, so a divergent
candidate does not prevent the search from reaching a different candidate.
All graph laws hold at arbitrary elements of every PA model.
-/

@[expose] public section

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open Nat.ArithPart₁

open CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition
namespace SigmaOneSearch

open ProgramGraph ArithmeticCodeCompiler ConcreteEvaluator

/-- The history At construction in `FailureOfComposition.SigmaOneSearch`. -/
def historyAt {n : ℕ} (c : PCode) (s x : Code n) : Code n :=
  codeHistoryEvaluator.comp ![s, codeConst (encode c), x]

/-- The success At construction in `FailureOfComposition.SigmaOneSearch`. -/
def successAt {n : ℕ} (c : PCode) (s x : Code n) : Code n :=
  codeEq (historyAt c s x) (Code.one n)

/-- The exists Test construction in `FailureOfComposition.SigmaOneSearch`. -/
def existsTest (c : PCode) : Code 2 :=
  successAt c (codeUnpair₁ (Code.proj 0)) (codePair (codeUnpair₂ (Code.proj 0)) (Code.proj 1))

/-- The union Test construction in `FailureOfComposition.SigmaOneSearch`. -/
def unionTest (c d : PCode) : Code 2 :=
  codeOr (successAt c (Code.proj 0) (Code.proj 1)) (successAt d (Code.proj 0) (Code.proj 1))

/-- Return the candidate from the least successful stage/candidate pair. -/
def candidateSearch (c : PCode) : PCode :=
  unaryCompile (codeBind (codeRfindPos (existsTest c)) (codeUnpair₂ (Code.proj 0)))

/-- Existential projection, with output zero on its domain. -/
def existsProgram (c : PCode) : PCode :=
  .comp .zero (candidateSearch c)

/-- Disjunction, with output zero if either program returns zero. -/
def unionProgram (c d : PCode) : PCode :=
  unaryCompile (codeBind (codeRfindPos (unionTest c d)) (Code.zero 2))

variable {M : Type*} [ORingStructure M]

private theorem historyAt_eval [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {n : ℕ} (c : PCode) (ds dx : Code n)
    (s x z : M) (v : Fin n → M) (hs : Semiformula.Evalb (s :> v) (code ds))
    (hx : Semiformula.Evalb (x :> v) (code dx)) :
    Semiformula.Evalb (z :> v) (code (historyAt c ds dx)) ↔
      Semiformula.Evalb ![z, s, (encode c : M), x] (code codeHistoryEvaluator) :=
  by
  rw [historyAt, eval_comp_iff]
  constructor
  · rintro ⟨w, hw, hi⟩
    have h0 := eval_unique (hi 0) hs
    have h1 := eval_unique (hi 1) (eval_codeConst (encode c) v)
    have h2 := eval_unique (hi 2) hx
    have he : w = ![s, (encode c : M), x] := by ext i; fin_cases i <;> simp_all
    simpa only [he] using hw
  · intro h
    refine ⟨![s, (encode c : M), x], h, ?_⟩
    intro i
    fin_cases i
    · exact hs
    · exact eval_codeConst (encode c) v
    · exact hx

private theorem computes_iff_stage [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (c : PCode) (x y : M) :
    Computes c x y ↔
      ∃ s : M,
        Semiformula.Evalb ![s, (encode c : M), x, y]
          (evalnCertificateFormula : ArithmeticSemisentence 4) :=
  by
  simp only [ProgramGraph.Computes, eventualGraph_eval, numeral_eq_natCast_app,
    Matrix.cons_val_zero, Matrix.cons_val_one]

variable [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

private theorem successAt_eval {n : ℕ} (c : PCode) (ds dx : Code n) (s x z : M) (v : Fin n → M)
    (hs : Semiformula.Evalb (s :> v) (code ds)) (hx : Semiformula.Evalb (x :> v) (code dx)) :
    Semiformula.Evalb (z :> v) (code (successAt c ds dx)) ↔
      ((Semiformula.Evalb ![s, (encode c : M), x, 0]
            (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
          z = 1) ∨
        (¬Semiformula.Evalb ![s, (encode c : M), x, 0]
              (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
          z = 0)) :=
  by
  have hh := historyAt_eval c ds dx s x (1 : M) v hs hx
  have hc :
    Semiformula.Evalb ((1 : M) :> v) (code (historyAt c ds dx)) ↔
      Semiformula.Evalb ![s, (encode c : M), x, 0]
        (evalnCertificateFormula : ArithmeticSemisentence 4) :=
    by
    rw [evalnCertificateFormula_eval_history_iff]
    simpa only [zero_add] using hh
  rw [successAt, eval_codeEq_iff]
  constructor
  · rintro ⟨a, b, ha, hb, hcase⟩
    have hb1 := (eval_one_iff b v).mp hb
    subst b
    rcases hcase with ⟨rfl, hz⟩ | ⟨ha1, hz⟩
    · exact Or.inl ⟨hc.mp ha, hz⟩
    · exact Or.inr ⟨fun h => ha1 (eval_unique ha (hc.mpr h)), hz⟩
  · intro hcase
    obtain ⟨a, ha⟩ := eval_codeHistoryEvaluator_exists s (encode c : M) x
    have ha' := (historyAt_eval c ds dx s x a v hs hx).mpr ha
    refine ⟨a, 1, ha', (eval_one_iff 1 v).mpr rfl, ?_⟩
    rcases hcase with ⟨h, hz⟩ | ⟨h, hz⟩
    · exact Or.inl ⟨eval_unique ha' (hc.mpr h), hz⟩
    · exact Or.inr ⟨fun ha1 => h (hc.mp (by simpa only [ha1] using ha')), hz⟩

private theorem successAt_total {n : ℕ} (c : PCode) (ds dx : Code n) (s x : M) (v : Fin n → M)
    (hs : Semiformula.Evalb (s :> v) (code ds)) (hx : Semiformula.Evalb (x :> v) (code dx)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (successAt c ds dx)) := by
  classical
  by_cases h :
    Semiformula.Evalb ![s, (encode c : M), x, 0]
      (evalnCertificateFormula : ArithmeticSemisentence 4)
  · exact ⟨1, (successAt_eval c ds dx s x 1 v hs hx).mpr (Or.inl ⟨h, rfl⟩)⟩
  · exact ⟨0, (successAt_eval c ds dx s x 0 v hs hx).mpr (Or.inr ⟨h, rfl⟩)⟩

/-- Minimization of a total arithmetic test has a result exactly when some
candidate has a positive value. Least-number induction is internal to PA. -/
private theorem positive_search_domain (d : Code 2) (x : M)
    (htotal : ∀ a : M, ∃ z : M, Semiformula.Evalb ![z, a, x] (code d)) :
    (∃ w : M, Semiformula.Evalb ![w, x] (code (codeRfindPos d))) ↔
      ∃ w z : M, 0 < z ∧ Semiformula.Evalb ![z, w, x] (code d) :=
  by
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, ((eval_codeRfindPos_iff d w ![x]).mp hw).1⟩
  · rintro ⟨w, hw⟩
    let P : M → Prop := fun w => ∃ z : M, 0 < z ∧ Semiformula.Evalb ![z, w, x] (code d)
    have hP : Σ₁-Predicate P :=
      by
      refine ⟨.mkSigma (“w. ∃ z, 0 < z ∧ !(Rew.emb ▹ code d)z w&x”), ?_⟩
      intro v
      simp [P, Semiformula.eval_emb]
    obtain ⟨w', hw', hmin⟩ := InductionOnHierarchy.least_number_sigma Σ 1 hP hw
    refine ⟨w', (eval_codeRfindPos_iff d w' ![x]).mpr ⟨hw', ?_⟩⟩
    intro r hr
    obtain ⟨z, hz⟩ := htotal r
    have hz0 : z = 0 :=
      le_antisymm (not_lt.mp (fun hp => hmin r hr ⟨z, hp, hz⟩)) (Arithmetic.zero_le z)
    simpa only [hz0] using hz

/-- A packed witness records a stage and a candidate accepted by c with output zero. -/
def packedSuccess (c : PCode) (x w : M) : Prop :=
  Semiformula.Evalb ![pi₁ w, (encode c : M), pair (pi₂ w) x, 0]
    (evalnCertificateFormula : ArithmeticSemisentence 4)

private theorem existsTest_eval (c : PCode) (w x z : M) :
    Semiformula.Evalb ![z, w, x] (code (existsTest c)) ↔
      ((packedSuccess c x w ∧ z = 1) ∨ (¬packedSuccess c x w ∧ z = 0)) :=
  by
  have hw : Semiformula.Evalb (w :> ![w, x]) (code (Code.proj (0 : Fin 2))) :=
    (eval_proj_iff _ _ _).mpr rfl
  exact
    successAt_eval c _ _ (pi₁ w) (pair (pi₂ w) x) z ![w, x] (eval_codeUnpair₁ _ _ _ hw)
      (eval_codePair _ _ _ _ ![w, x] (eval_codeUnpair₂ _ _ _ hw)
        ((eval_proj_iff _ _ _).mpr rfl))

private theorem existsTest_total (c : PCode) (w x : M) :
    ∃ z : M, Semiformula.Evalb ![z, w, x] (code (existsTest c)) := by
  classical
  by_cases h : packedSuccess c x w
  · exact ⟨1, (existsTest_eval c w x 1).mpr (Or.inl ⟨h, rfl⟩)⟩
  · exact ⟨0, (existsTest_eval c w x 0).mpr (Or.inr ⟨h, rfl⟩)⟩

private theorem existsTest_positive (c : PCode) (w x : M) :
    (∃ z : M, 0 < z ∧ Semiformula.Evalb ![z, w, x] (code (existsTest c))) ↔
      packedSuccess c x w :=
  by
  simp only [existsTest_eval]
  constructor
  · rintro ⟨z, hz, (⟨h, _⟩ | ⟨_, rfl⟩)⟩
    · exact h
    · exact False.elim ((Arithmetic.lt_irrefl 0) hz)
  · intro h
    exact ⟨1, Arithmetic.zero_lt_one, Or.inl ⟨h, rfl⟩⟩

private theorem existsTest_zero (c : PCode) (w x : M) :
    Semiformula.Evalb ![0, w, x] (code (existsTest c)) ↔ ¬packedSuccess c x w :=
  by
  rw [existsTest_eval]
  simp

private theorem existsSearch_domain (c : PCode) (x : M) :
    (∃ w : M, Semiformula.Evalb ![w, x] (code (codeRfindPos (existsTest c)))) ↔
      ∃ a : M, Computes c (pair a x) 0 :=
  by
  rw [positive_search_domain _ x (fun w => existsTest_total c w x)]
  simp only [existsTest_positive]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨pi₂ w, (computes_iff_stage c _ 0).mpr ⟨pi₁ w, hw⟩⟩
  · rintro ⟨a, ha⟩
    obtain ⟨s, hs⟩ := (computes_iff_stage c _ 0).mp ha
    refine ⟨pair s a, ?_⟩
    simpa only [packedSuccess, pi₁_pair, pi₂_pair] using hs

/-- Exact witness-selection graph: select the candidate belonging to the least
successful stage/candidate pair in the arithmetic model. -/
theorem computes_candidateSearch (c : PCode) (x a : M) :
    Computes (candidateSearch c) x a ↔
      ∃ w : M, packedSuccess c x w ∧ (∀ r < w, ¬packedSuccess c x r) ∧ a = pi₂ w :=
  by
  rw [candidateSearch, computes_unaryCompile, eval_codeBind_iff]
  have hproj (w : M) :
    Semiformula.Evalb ![a, w, x] (code (codeUnpair₂ (Code.proj (0 : Fin 2)))) ↔ a = pi₂ w :=
    by
    have h := eval_codeUnpair₂ (Code.proj (0 : Fin 2)) w ![w, x] ((eval_proj_iff _ _ _).mpr rfl)
    constructor
    · intro ha
      exact eval_unique ha h
    · rintro rfl
      exact h
  simp only [hproj, eval_codeRfindPos_iff, existsTest_positive, existsTest_zero]
  exact exists_congr fun w => and_assoc

/-- Every returned candidate is accepted by the original semidecision program. -/
theorem candidateSearch_sound (c : PCode) (x a : M) (h : Computes (candidateSearch c) x a) :
    Computes c (pair a x) 0 :=
  by
  obtain ⟨w, hw, _, rfl⟩ := (computes_candidateSearch c x a).mp h
  exact (computes_iff_stage c _ 0).mpr ⟨pi₁ w, hw⟩

/-- Fair search terminates if and only if an accepted candidate exists. -/
theorem candidateSearch_domain (c : PCode) (x : M) :
    (∃ a : M, Computes (candidateSearch c) x a) ↔ ∃ a : M, Computes c (pair a x) 0 :=
  by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, candidateSearch_sound c x a ha⟩
  · intro h
    obtain ⟨w, hw⟩ := (existsSearch_domain c x).mpr h
    refine ⟨pi₂ w, (computes_candidateSearch c x _).mpr ⟨w, ?_, ?_, rfl⟩⟩
    · exact (existsTest_positive c w x).mp ((eval_codeRfindPos_iff _ _ _).mp hw).1
    · intro r hr
      exact (existsTest_zero c r x).mp (((eval_codeRfindPos_iff _ _ _).mp hw).2 r hr)

/-- Existential quantification of a semidecision predicate, with output zero. -/
theorem computes_existsProgram (c : PCode) (x y : M) :
    Computes (existsProgram c) x y ↔ y = 0 ∧ ∃ a : M, Computes c (pair a x) 0 :=
  by
  rw [existsProgram, ProgramGraph.computes_comp]
  simp only [ProgramGraph.computes_zero, exists_and_right]
  rw [candidateSearch_domain]
  exact and_comm

/-- With at most one accepted candidate, witness selection realizes the full
functional relation, rather than merely choosing some accepted candidate. -/
theorem candidateSearch_of_functional (c : PCode) (x a : M)
    (hunique : ∀ b d : M, Computes c (pair b x) 0 → Computes c (pair d x) 0 → b = d) :
    Computes (candidateSearch c) x a ↔ Computes c (pair a x) 0 :=
  by
  constructor
  · exact candidateSearch_sound c x a
  · intro ha
    obtain ⟨b, hb⟩ := (candidateSearch_domain c x).mpr ⟨a, ha⟩
    have hba := hunique b a (candidateSearch_sound c x b hb) ha
    simpa only [hba] using hb

private theorem unionTest_eval (c d : PCode) (s x z : M) :
    Semiformula.Evalb ![z, s, x] (code (unionTest c d)) ↔
      (((Semiformula.Evalb ![s, (encode c : M), x, 0]
              (evalnCertificateFormula : ArithmeticSemisentence 4) ∨
            Semiformula.Evalb ![s, (encode d : M), x, 0]
              (evalnCertificateFormula : ArithmeticSemisentence 4)) ∧
          z = 1) ∨
        (¬(Semiformula.Evalb ![s, (encode c : M), x, 0]
                (evalnCertificateFormula : ArithmeticSemisentence 4) ∨
              Semiformula.Evalb ![s, (encode d : M), x, 0]
                (evalnCertificateFormula : ArithmeticSemisentence 4)) ∧
          z = 0)) :=
  by
  have ht (e : PCode) (a : M) :=
    successAt_eval e (Code.proj (0 : Fin 2)) (Code.proj 1) s x a ![s, x]
      ((eval_proj_iff _ _ _).mpr rfl) ((eval_proj_iff _ _ _).mpr rfl)
  rw [unionTest, eval_codeOr_iff]
  simp only [ht]
  by_cases hc :
        Semiformula.Evalb ![s, (encode c : M), x, 0]
          (evalnCertificateFormula : ArithmeticSemisentence 4) <;>
      by_cases hd :
        Semiformula.Evalb ![s, (encode d : M), x, 0]
          (evalnCertificateFormula : ArithmeticSemisentence 4) <;>
    simp [hc, hd]

private theorem unionTest_total (c d : PCode) (s x : M) :
    ∃ z : M, Semiformula.Evalb ![z, s, x] (code (unionTest c d)) := by
  classical
  by_cases h :
    Semiformula.Evalb ![s, (encode c : M), x, 0]
        (evalnCertificateFormula : ArithmeticSemisentence 4) ∨
      Semiformula.Evalb ![s, (encode d : M), x, 0]
        (evalnCertificateFormula : ArithmeticSemisentence 4)
  · exact ⟨1, (unionTest_eval c d s x 1).mpr (Or.inl ⟨h, rfl⟩)⟩
  · exact ⟨0, (unionTest_eval c d s x 0).mpr (Or.inr ⟨h, rfl⟩)⟩

private theorem unionTest_positive (c d : PCode) (s x : M) :
    (∃ z : M, 0 < z ∧ Semiformula.Evalb ![z, s, x] (code (unionTest c d))) ↔
      (Semiformula.Evalb ![s, (encode c : M), x, 0]
          (evalnCertificateFormula : ArithmeticSemisentence 4) ∨
        Semiformula.Evalb ![s, (encode d : M), x, 0]
          (evalnCertificateFormula : ArithmeticSemisentence 4)) :=
  by
  simp only [unionTest_eval]
  constructor
  · rintro ⟨z, hz, (⟨h, _⟩ | ⟨_, rfl⟩)⟩
    · exact h
    · exact False.elim ((Arithmetic.lt_irrefl 0) hz)
  · intro h
    exact ⟨1, Arithmetic.zero_lt_one, Or.inl ⟨h, rfl⟩⟩

private theorem unionSearch_domain (c d : PCode) (x : M) :
    (∃ w : M, Semiformula.Evalb ![w, x] (code (codeRfindPos (unionTest c d)))) ↔
      Computes c x 0 ∨ Computes d x 0 :=
  by
  rw [positive_search_domain _ x (fun s => unionTest_total c d s x)]
  simp only [unionTest_positive, exists_or, computes_iff_stage]

/-- Fair disjunction of semidecision predicates, with output zero. -/
theorem computes_unionProgram (c d : PCode) (x y : M) :
    Computes (unionProgram c d) x y ↔ y = 0 ∧ (Computes c x 0 ∨ Computes d x 0) :=
  by
  rw [unionProgram, computes_unaryCompile, eval_codeBind_iff]
  simp only [eval_zero_iff, exists_and_right]
  rw [unionSearch_domain]
  exact and_comm

end SigmaOneSearch
end FailureOfComposition

end

end PointwiseComposition
