/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BooleanEvaluationWitness.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BooleanTruthReading

/-!
# Boolean Evaluation Witness
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BooleanExpressionTruth
open TransitiveNameModel BoundedSetTheory BooleanExpressionCertificate

def GoodTruth (K B R Y : ZFSet.{0}) : Prop :=
  Y ⊆ K ∧ ∀ t ∈ K, t ∈ Y ↔ step K B R Y t

theorem GoodTruth.agrees {K B R Y : ZFSet.{0}} (hK : Transitive K) (hy : GoodTruth K B R Y) :
    ∀ t ∈ K, t ∈ Y ↔ value B R t := by
  have hp : BoundedTruthRecursion.Partial formula (parameters K B R) K K Y :=
    ⟨hK,fun _ h => h,hy.1,fun t ht => (hy.2 t ht).trans (formula_spec K B R Y t).symm⟩
  intro t ht
  exact (BoundedTruthRecursion.partial_sound formula (parameters K B R) K K Y (valueSet K B R)
    (formula_local K B R) hp (valueSet_fixed K B R hK) t ht).trans
      (ZFSet.mem_sep.trans (and_iff_right ht))

theorem valueSet_good (K B R : ZFSet.{0}) (hK : Transitive K) : GoodTruth K B R (valueSet K B R) :=
  ⟨fun _ h => (ZFSet.mem_sep.mp h).1,
    fun t ht => (valueSet_fixed K B R hK t ht).trans (formula_spec K B R _ t)⟩

def Evaluated (c B Q S R K Y U : ZFSet.{0}) : Prop :=
  Transitive K ∧ GoodTruth K B R Y ∧ ∃ g ∈ K, Certificate c B Q S K g ∧
    ∃ t ∈ K, ZFSet.pair t U ∈ g ∧ t ∈ Y

def truthSlots (t Y K B R z0 z1 z2 : ℕ) : ℕ → ℕ
  | 0 => t
  | 1 => Y
  | 2 => K
  | 3 => B
  | 4 => R
  | 5 => z0
  | 6 => z1
  | _ => z2

def truthAt (t Y K B R z0 z1 z2 : ℕ) : Formula := formula.rename (truthSlots t Y K B R z0 z1 z2)

theorem truthAt_spec (t Y K B R z0 z1 z2 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) (h2 : e z2 = natSet 2) :
    (truthAt t Y K B R z0 z1 z2).Eval e ↔ step (e K) (e B) (e R) (e Y) (e t) := by
  have eq : e ∘ truthSlots t Y K B R z0 z1 z2 = cons (e t) (cons (e Y) (parameters (e K) (e B) (e
    R))) := by
    funext i
    rcases i with _|_|_|_|_|_|_|i
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact h0
    · exact h1
    · exact h2
  rw [truthAt,Formula.eval_rename_comp,eq,formula_spec]

def goodTruthFormula (K B R Y z0 z1 z2 : ℕ) : Formula :=
  .conj (.subset Y K) (.allMem K (.iff (.member 0 (Y+1))
    (truthAt 0 (Y+1) (K+1) (B+1) (R+1) (z0+1) (z1+1) (z2+1))))

theorem goodTruthFormula_spec (K B R Y z0 z1 z2 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) (h2 : e z2 = natSet 2) :
    (goodTruthFormula K B R Y z0 z1 z2).Eval e ↔ GoodTruth (e K) (e B) (e R) (e Y) := by
  simp only [goodTruthFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,Formula.eval_iff,
    cons_zero,cons_succ,GoodTruth]
  apply and_congr Iff.rfl
  apply forall_congr'; intro t
  apply imp_congr_right; intro _
  exact iff_congr Iff.rfl (truthAt_spec _ _ _ _ _ _ _ _ _ h0 h1 h2)

def evaluatedFormula (c B Q S R K Y U z0 z1 z2 : ℕ) : Formula :=
  .conj (.transitive K) (.conj (goodTruthFormula K B R Y z0 z1 z2)
    (.existsMem K (.conj (certificateFormula (c+1) (B+1) (Q+1) (S+1) (K+1) 0 (z0+1) (z1+1) (z2+1))
      (.existsMem (K+1) (.conj (.pairMem 0 (U+2) 1) (.member 0 (Y+2)))))))

theorem evaluatedFormula_spec (c B Q S R K Y U z0 z1 z2 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) (h2 : e z2 = natSet 2) :
    (evaluatedFormula c B Q S R K Y U z0 z1 z2).Eval e ↔
      Evaluated (e c) (e B) (e Q) (e S) (e R) (e K) (e Y) (e U) := by
  simp only [evaluatedFormula,Formula.Eval,Formula.eval_transitive,Formula.eval_pairMem,
    cons_zero,cons_succ,Evaluated]
  apply and_congr Iff.rfl
  apply and_congr (goodTruthFormula_spec _ _ _ _ _ _ _ _ h0 h1 h2)
  apply exists_congr; intro g
  apply and_congr_right; intro _
  exact and_congr (certificateFormula_spec _ _ _ _ _ _ _ _ _ _ h0 h1 h2) Iff.rfl

def evaluationParameters (W c B Q S R : ZFSet.{0}) : ℕ → ZFSet.{0} :=
  cons W (cons c (cons B (cons Q (cons S (cons R
    (cons (natSet 0) (cons (natSet 1) (fun _ => natSet 2))))))))

def evaluationBody : Formula := .existsMem 2 (evaluatedFormula 4 5 6 7 8 0 1 2 9 10 11)

theorem evaluationBody_realize (N W c B Q S R Y U : ZFSet.{0}) (hN : Transitive N)
    (he : ∀ i, evaluationParameters W c B Q S R i ∈ N) (hY : Y ∈ N) (hU : U ∈ N) :
    evaluationBody.Realize N (cons Y (cons U (evaluationParameters W c B Q S R))) ↔
      ∃ K ∈ W, Evaluated c B Q S R K Y U := by
  rw [Formula.absolute _ N hN _ (by
    intro i
    rcases i with _ | _ | i
    · exact hY
    · exact hU
    · exact he i)]
  change (∃ K ∈ W, (evaluatedFormula 4 5 6 7 8 0 1 2 9 10 11).Eval
    (cons K (cons Y (cons U (evaluationParameters W c B Q S R))))) ↔ _
  apply exists_congr; intro K
  apply and_congr_right; intro _
  exact evaluatedFormula_spec _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl

end TuringRigidity.BooleanExpressionTruth

end OAI
