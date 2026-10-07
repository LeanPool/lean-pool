/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Borisov.Construction
public import LeanPool.SmallUndecidableGroups.Borisov.Model.ConverseCore
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Group.Commute.Hom

/-!
# FinalModel

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability

open CommutatorLemmas

namespace BorisovFinalModel

open BorisovCStage
open BorisovContextNormalForm
open BorisovConverseCore
open BorisovHNNModel
open HNNLemmas

noncomputable section

variable (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)

/-- The composite inclusion from the rewriting-rule HNN extension to the final group. -/
def cStageToFinal : Gamma2 datum hfree →* FinalStage datum hfree :=
  (toFinalStage datum hfree).comp (toTStage datum hfree)

/-- The image of the generator `d` in the final iterated-HNN model. -/
def modelD : FinalStage datum hfree :=
  cStageToFinal datum hfree (of3 datum hfree d3)

/-- The image of the generator `e` in the final iterated-HNN model. -/
def modelE : FinalStage datum hfree :=
  cStageToFinal datum hfree (of3 datum hfree e3)

/-- The image of the first stable generator in the final iterated-HNN model. -/
def modelS1 : FinalStage datum hfree :=
  cStageToFinal datum hfree (of3 datum hfree firstStableInStageThree)

/-- The image of the second stable generator in the final iterated-HNN model. -/
def modelS2 : FinalStage datum hfree :=
  cStageToFinal datum hfree (of3 datum hfree secondStableInStageThree)

/-- The image of the rule-transport generator `c` in the final model. -/
def modelC : FinalStage datum hfree :=
  cStageToFinal datum hfree (c datum hfree)

/-- The image of the generator `t` in the final model. -/
def modelT : FinalStage datum hfree :=
  toFinalStage datum hfree (tLetter datum hfree)

/-- The final-model generator `k`. -/
def modelK : FinalStage datum hfree :=
  kLetter datum hfree

/-- Generator order `d,e,s₁,s₂,c,t,k`, matching `Borisov.presentation`. -/
def modelGenerator : Fin 7 → FinalStage datum hfree :=
  ![modelD datum hfree, modelE datum hfree,
    modelS1 datum hfree, modelS2 datum hfree,
    modelC datum hfree, modelT datum hfree, modelK datum hfree]

@[simp] theorem eval_dWord :
    Word.eval (modelGenerator datum hfree) Borisov.dWord = modelD datum hfree := by
  simp [Borisov.dWord, modelGenerator]

@[simp] theorem eval_eWord :
    Word.eval (modelGenerator datum hfree) Borisov.eWord = modelE datum hfree := by
  simp [Borisov.eWord, modelGenerator]

@[simp] theorem eval_s1Word :
    Word.eval (modelGenerator datum hfree) Borisov.s1Word = modelS1 datum hfree := by
  simp [Borisov.s1Word, modelGenerator]

@[simp] theorem eval_s2Word :
    Word.eval (modelGenerator datum hfree) Borisov.s2Word = modelS2 datum hfree := by
  simp [Borisov.s2Word, modelGenerator]

@[simp] theorem eval_cWord :
    Word.eval (modelGenerator datum hfree) Borisov.cWord = modelC datum hfree := by
  simp [Borisov.cWord, modelGenerator]

@[simp] theorem eval_tWord :
    Word.eval (modelGenerator datum hfree) Borisov.tWord = modelT datum hfree := by
  simp [Borisov.tWord, modelGenerator]

@[simp] theorem eval_kWord :
    Word.eval (modelGenerator datum hfree) Borisov.kWord = modelK datum hfree := by
  simp [Borisov.kWord, modelGenerator]

theorem eval_positiveWord (w : List (Fin 2)) :
    Word.eval (modelGenerator datum hfree) (Borisov.positiveWord w) =
      cStageToFinal datum hfree (positive2 datum hfree w) := by
  simp only [Borisov.positiveWord, Word.eval_substitutePositive,
    eval_s1Word, eval_s2Word]
  change
    (w.map fun i => if i = 0 then modelS1 datum hfree else modelS2 datum hfree).prod =
      cStageToFinal datum hfree
        (of3 datum hfree
          ((w.map fun i =>
            if i = 0 then firstStableInStageThree else secondStableInStageThree).prod))
  induction w with
  | nil => simp
  | cons i w ih =>
      simp only [List.map_cons, List.prod_cons, map_mul]
      rw [ih]
      fin_cases i <;> rfl

private theorem model_d_four_mul_s1 :
    modelD datum hfree ^ 4 * modelS1 datum hfree =
      modelS1 datum hfree * modelD datum hfree := by
  simpa [modelD, modelS1, map_mul, map_pow] using
    congrArg (cStageToFinal datum hfree)
      (congrArg (of3 datum hfree) gamma3_d_four_mul_s1)

private theorem model_e_mul_s1 :
    modelE datum hfree * modelS1 datum hfree =
      modelS1 datum hfree * modelE datum hfree ^ 4 := by
  simpa [modelE, modelS1, map_mul, map_pow] using
    congrArg (cStageToFinal datum hfree)
      (congrArg (of3 datum hfree) gamma3_e_mul_s1)

private theorem model_d_four_mul_s2 :
    modelD datum hfree ^ 4 * modelS2 datum hfree =
      modelS2 datum hfree * modelD datum hfree := by
  simpa [modelD, modelS2, map_mul, map_pow] using
    congrArg (cStageToFinal datum hfree)
      (congrArg (of3 datum hfree) gamma3_d_four_mul_s2)

private theorem model_e_mul_s2 :
    modelE datum hfree * modelS2 datum hfree =
      modelS2 datum hfree * modelE datum hfree ^ 4 := by
  simpa [modelE, modelS2, map_mul, map_pow] using
    congrArg (cStageToFinal datum hfree)
      (congrArg (of3 datum hfree) gamma3_e_mul_s2)

private theorem conjugation_of_transport {G : Type*} [Group G]
    (d s : G) (h : d ^ 4 * s = s * d) :
    s⁻¹ * d ^ 4 * s = d := by
  calc
    s⁻¹ * d ^ 4 * s = s⁻¹ * (d ^ 4 * s) := by simp [mul_assoc]
    _ = s⁻¹ * (s * d) := by rw [h]
    _ = d := by simp

private theorem conjugation_e_of_transport {G : Type*} [Group G]
    (e s : G) (h : e * s = s * e ^ 4) :
    s⁻¹ * e * s = e ^ 4 := by
  calc
    s⁻¹ * e * s = s⁻¹ * (e * s) := by simp [mul_assoc]
    _ = s⁻¹ * (s * e ^ 4) := by rw [h]
    _ = e ^ 4 := by simp

private theorem model_c_commutes_s1 :
    Commute (modelS1 datum hfree) (modelC datum hfree) :=
  (c_commutes_stable datum hfree 0).map (cStageToFinal datum hfree)

private theorem model_c_commutes_s2 :
    Commute (modelS2 datum hfree) (modelC datum hfree) :=
  (c_commutes_stable datum hfree 1).map (cStageToFinal datum hfree)

private theorem model_c_simulation (i : Fin 3) :
    (modelC datum hfree)⁻¹ *
        modelD datum hfree ^ (i.val + 1) *
        Word.eval (modelGenerator datum hfree)
          (Borisov.positiveWord (datum.F i)) *
        modelE datum hfree ^ (i.val + 1) * modelC datum hfree =
      modelD datum hfree ^ (i.val + 1) *
        Word.eval (modelGenerator datum hfree)
          (Borisov.positiveWord (datum.E i)) *
        modelE datum hfree ^ (i.val + 1) := by
  have h := congrArg (cStageToFinal datum hfree)
    (c_simulation datum hfree i)
  rw [eval_positiveWord, eval_positiveWord]
  simpa [a3, b3, positive2, modelC, modelD, modelE,
    cStageToFinal, map_mul, map_inv, map_pow, mul_assoc] using h

private theorem model_t_commutes_c :
    Commute (modelT datum hfree) (modelC datum hfree) := by
  have hc : c datum hfree ∈ CD datum hfree :=
    Subgroup.subset_closure (by simp)
  have h := (centralizerOf_commute_stable_iff
    (CD datum hfree) (c datum hfree)).2 hc
  exact h.symm.map (toFinalStage datum hfree)

private theorem model_t_commutes_d :
    Commute (modelT datum hfree) (modelD datum hfree) := by
  have hd : of3 datum hfree d3 ∈ CD datum hfree :=
    Subgroup.subset_closure (by simp)
  have h := (centralizerOf_commute_stable_iff
    (CD datum hfree) (of3 datum hfree d3)).2 hd
  exact h.symm.map (toFinalStage datum hfree)

private theorem mapped_CE_mem_K {x : Gamma2 datum hfree}
    (hx : x ∈ CE datum hfree) :
    toTStage datum hfree x ∈ KSubgroup datum hfree := by
  apply Subgroup.subset_closure
  exact Or.inl ⟨x, hx, rfl⟩

private theorem model_k_commutes_c :
    Commute (modelK datum hfree) (modelC datum hfree) := by
  have hc : c datum hfree ∈ CE datum hfree :=
    Subgroup.subset_closure (by simp)
  have hmem := mapped_CE_mem_K datum hfree hc
  exact ((centralizerOf_commute_stable_iff
    (KSubgroup datum hfree) (toTStage datum hfree (c datum hfree))).2 hmem).symm

private theorem model_k_commutes_e :
    Commute (modelK datum hfree) (modelE datum hfree) := by
  have he : of3 datum hfree e3 ∈ CE datum hfree :=
    Subgroup.subset_closure (by simp)
  have hmem := mapped_CE_mem_K datum hfree he
  exact ((centralizerOf_commute_stable_iff
    (KSubgroup datum hfree)
      (toTStage datum hfree (of3 datum hfree e3))).2 hmem).symm

private theorem model_k_commutes_p :
    Commute (modelK datum hfree)
      (finalConjugatedT datum hfree datum.P) := by
  have hmem : conjugatedT datum hfree datum.P ∈ KSubgroup datum hfree := by
    apply Subgroup.subset_closure
    exact Or.inr rfl
  exact ((centralizerOf_commute_stable_iff
    (KSubgroup datum hfree) (conjugatedT datum hfree datum.P)).2 hmem).symm

theorem model_relators :
    ∀ r ∈ (Borisov.presentation datum).relSet,
      FreeGroup.lift (modelGenerator datum hfree) r = 1 := by
  rintro r ⟨i, rfl⟩
  change Word.eval (modelGenerator datum hfree)
    ((Borisov.presentation datum).relator i) = 1
  fin_cases i
  · change Word.eval (modelGenerator datum hfree)
      (Borisov.sDRelator Borisov.s1Word) = 1
    rw [Borisov.sDRelator, Word.eval_relation_eq_one_iff]
    simpa [mul_assoc] using
      conjugation_of_transport _ _ (model_d_four_mul_s1 datum hfree)
  · change Word.eval (modelGenerator datum hfree)
      (Borisov.sERelator Borisov.s1Word) = 1
    rw [Borisov.sERelator, Word.eval_relation_eq_one_iff]
    simpa [mul_assoc] using
      conjugation_e_of_transport _ _ (model_e_mul_s1 datum hfree)
  · change Word.eval (modelGenerator datum hfree)
      (Borisov.sDRelator Borisov.s2Word) = 1
    rw [Borisov.sDRelator, Word.eval_relation_eq_one_iff]
    simpa [mul_assoc] using
      conjugation_of_transport _ _ (model_d_four_mul_s2 datum hfree)
  · change Word.eval (modelGenerator datum hfree)
      (Borisov.sERelator Borisov.s2Word) = 1
    rw [Borisov.sERelator, Word.eval_relation_eq_one_iff]
    simpa [mul_assoc] using
      conjugation_e_of_transport _ _ (model_e_mul_s2 datum hfree)
  · change Word.eval (modelGenerator datum hfree)
      (Word.commutator Borisov.s1Word Borisov.cWord) = 1
    simp only [Word.eval_commutator]
    exact (inverse_commutator_eq_one_iff_commute _ _).mpr (model_c_commutes_s1 datum hfree)
  · change Word.eval (modelGenerator datum hfree)
      (Word.commutator Borisov.s2Word Borisov.cWord) = 1
    simp only [Word.eval_commutator]
    exact (inverse_commutator_eq_one_iff_commute _ _).mpr (model_c_commutes_s2 datum hfree)
  · change Word.eval (modelGenerator datum hfree)
      (Borisov.simulationRelator datum 0) = 1
    rw [Borisov.simulationRelator, Word.eval_relation_eq_one_iff]
    simpa [mul_assoc] using model_c_simulation datum hfree 0
  · change Word.eval (modelGenerator datum hfree)
      (Borisov.simulationRelator datum 1) = 1
    rw [Borisov.simulationRelator, Word.eval_relation_eq_one_iff]
    simpa [mul_assoc] using model_c_simulation datum hfree 1
  · change Word.eval (modelGenerator datum hfree)
      (Borisov.simulationRelator datum 2) = 1
    rw [Borisov.simulationRelator, Word.eval_relation_eq_one_iff]
    simpa [mul_assoc] using model_c_simulation datum hfree 2
  · change Word.eval (modelGenerator datum hfree)
      (Word.commutator Borisov.tWord Borisov.cWord) = 1
    simp only [Word.eval_commutator]
    exact (inverse_commutator_eq_one_iff_commute _ _).mpr (model_t_commutes_c datum hfree)
  · change Word.eval (modelGenerator datum hfree)
      (Word.commutator Borisov.tWord Borisov.dWord) = 1
    simp only [Word.eval_commutator]
    exact (inverse_commutator_eq_one_iff_commute _ _).mpr (model_t_commutes_d datum hfree)
  · change Word.eval (modelGenerator datum hfree)
      (Word.commutator Borisov.kWord Borisov.cWord) = 1
    simp only [Word.eval_commutator]
    exact (inverse_commutator_eq_one_iff_commute _ _).mpr (model_k_commutes_c datum hfree)
  · change Word.eval (modelGenerator datum hfree)
      (Word.commutator Borisov.kWord Borisov.eWord) = 1
    simp only [Word.eval_commutator]
    exact (inverse_commutator_eq_one_iff_commute _ _).mpr (model_k_commutes_e datum hfree)
  · change Word.eval (modelGenerator datum hfree)
      (Word.commutator Borisov.kWord (Borisov.pWord datum)) = 1
    simp only [Word.eval_commutator]
    have hp : Word.eval (modelGenerator datum hfree) (Borisov.pWord datum) =
        finalConjugatedT datum hfree datum.P := by
      rw [Borisov.pWord, Word.eval_product]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        Word.eval_inverse, eval_positiveWord, eval_tWord, mul_one]
      simp [modelT, finalConjugatedT, conjugatedT, conjugatedStable,
        centralizerOf, toTStage, tLetter, cStageToFinal, map_mul, map_inv,
        mul_assoc]
    simpa [hp] using
      (inverse_commutator_eq_one_iff_commute _ _).mpr (model_k_commutes_p datum hfree)

/-- The canonical homomorphism from Borisov's finite presentation to the
semantic iterated-HNN model. -/
def toFinalModel : (Borisov.presentation datum).Group →* FinalStage datum hfree :=
  PresentedGroup.toGroup (model_relators datum hfree)

@[simp] theorem toFinalModel_of (i : Fin 7) :
    toFinalModel datum hfree (PresentedGroup.of i) = modelGenerator datum hfree i := by
  simp [toFinalModel]

theorem toFinalModel_evalWord (w : Borisov.BorisovWord) :
    toFinalModel datum hfree ((Borisov.presentation datum).evalWord w) =
      Word.eval (modelGenerator datum hfree) w := by
  rw [FP.evalWord, Word.map_eval]
  apply congrArg (fun q : Fin 7 → FinalStage datum hfree => Word.eval q w)
  funext i
  exact toFinalModel_of datum hfree i

theorem eval_testWord :
    Word.eval (modelGenerator datum hfree) (Borisov.testWord Q) =
      (finalConjugatedT datum hfree Q)⁻¹ * (modelK datum hfree)⁻¹ *
        finalConjugatedT datum hfree Q * modelK datum hfree := by
  rw [Borisov.testWord, Word.eval_commutator]
  simp only [Word.eval_product, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Word.eval_inverse, eval_positiveWord, eval_tWord,
    eval_kWord, mul_one]
  simp [finalConjugatedT, conjugatedT, conjugatedStable, centralizerOf,
    toTStage, tLetter, modelT, modelK, cStageToFinal, map_mul, map_inv,
    mul_assoc]

/-- Borisov's converse criterion follows from the subgroup intersections and
the positive-`c` pinch induction. -/
theorem criterion_converse_of_borisov_inputs
    (hinter : BaseIntersections datum)
    (hlemma4 : BorisovLemma4 datum hfree)
    (Q : List (Fin 2)) :
    (Borisov.presentation datum).wordProblem (Borisov.testWord Q) →
      ThueEq (Thue.systemOf datum.F datum.E) Q datum.P := by
  intro hword
  have hpresented : (Borisov.presentation datum).evalWord
      (Borisov.testWord Q) = 1 :=
    ((Borisov.presentation datum).wordProblem_iff_evalWord_eq_one
      (Borisov.testWord Q)).mp hword
  have hmodel := congrArg (toFinalModel datum hfree) hpresented
  have hmodel' : Word.eval (modelGenerator datum hfree)
      (Borisov.testWord Q) = 1 := by
    rw [← toFinalModel_evalWord datum hfree]
    simpa using hmodel
  have htest :
      (finalConjugatedT datum hfree Q)⁻¹ * (kLetter datum hfree)⁻¹ *
          finalConjugatedT datum hfree Q * kLetter datum hfree = 1 := by
    rw [eval_testWord] at hmodel'
    simpa [modelK] using hmodel'
  exact model_test_eq_one_imp_thueEq datum hfree hinter hlemma4 Q htest

end

end BorisovFinalModel
end Undecidability
