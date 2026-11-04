/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ProgramGraph
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteConstructorGraphs
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteRecursionGraph

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Arithmetic correctness of the compiled program operations.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open CategoricalRiceShapiro.Evaluator

open Encodable _root_.Nat.Partrec

namespace FailureOfComposition
namespace ConcreteEvaluator

/-- Mathlib program performing addition on the two components of its input. -/
def addProgram : Code :=
  .prec Code.id (.comp .succ (.comp .right .right))

/-- Mathlib program performing multiplication on the two input components. -/
def mulProgram : Code :=
  .prec .zero (.comp addProgram (.pair .left (.comp .right .right)))

/-- Mathlib program for truncated predecessor. -/
def predProgram : Code :=
  .comp (.prec .zero (.comp .left .right)) (.pair .zero Code.id)

/-- Mathlib program for truncated subtraction of the input components. -/
def subProgram : Code :=
  .prec Code.id (.comp predProgram (.comp .right .right))

/-- Mathlib program returning one at zero and zero at positive inputs. -/
def isZeroProgram : Code :=
  .comp (.prec (Code.const 1) .zero) (.pair .zero Code.id)

/-- Mathlib program deciding strict order of the input components. -/
def ltProgram : Code :=
  .comp isZeroProgram (.comp subProgram (.pair (.comp .succ .left) .right))

/-- Mathlib program deciding equality of the input components. -/
def eqProgram : Code :=
  .comp isZeroProgram
    (.comp addProgram (.pair subProgram (.comp subProgram (.pair .right .left))))

open ProgramGraph

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]

/-- Full PA induction with arbitrary model parameters in its defining formula. -/
theorem pa_formula_induction {P : M → Prop} (φ : ArithmeticSemiformula M 1)
    (hφ : ∀ x, P x ↔ φ.Eval ![x] id) (hz : P 0) (hs : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  classical
  have := models_inductionScheme_univ (M := M)
  have : Inhabited M := ⟨0⟩
  exact
    InductionScheme.succ_induction (C := Set.univ)
      (by
        refine ⟨φ.enumerateFVar, Rew.rewriteMap φ.idxOfFVar ▹ φ, trivial, ?_⟩
        intro x
        simp only [hφ, Nat.succ_eq_add_one, Nat.reduceAdd, Semiformula.eval_rewriteMap]
        exact
          Semiformula.eval_iff_of_funEqOn φ
            (by
              intro z hz
              simp [Semiformula.enumerateFVar_idxOfFVar
                    (Semiformula.mem_fvarList_iff_hasFreeVariable.mpr hz)]))
      hz hs

variable [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

@[simp]
theorem runs_pair (f g : Code) (x z : M) :
    Computes (.pair f g) x z ↔ ∃ a b, Computes f x a ∧ Computes g x b ∧ z = pair a b :=
  eventualGraph_pair_code_eval f g x z

attribute [local simp] computes_zero computes_succ computes_left computes_right computes_comp
  computes_id computes_const

@[simp]
theorem runs_prec_zero (f g : Code) (a y : M) :
    Computes (.prec f g) (pair a 0) y ↔ Computes f a y := by
  simpa only [Computes, ProgramGraph.Computes,
    CategoricalRiceShapiro.PartialRecursive.canonicalPartrecPrecIndex,
    Denumerable.ofNat_encode] using
    eventualGraph_prec_zero_eval (M := M) (encode f) (encode g) a y

@[simp]
theorem runs_prec_succ (f g : Code) (a b y : M) :
    Computes (.prec f g) (pair a (b + 1)) y ↔
      ∃ z, Computes (.prec f g) (pair a b) z ∧ Computes g (pair a (pair b z)) y :=
  by
  simpa only [Computes, ProgramGraph.Computes,
    CategoricalRiceShapiro.PartialRecursive.canonicalPartrecPrecIndex,
    Denumerable.ofNat_encode] using
    eventualGraph_prec_succ_eval (M := M) (encode f) (encode g) a b y

private theorem runs_add_induction (c : Code) (a : M) (hz : Computes c (pair a 0) a)
    (hs : ∀ b, Computes c (pair a b) (a + b) → Computes c (pair a (b + 1)) (a + b + 1)) :
    ∀ b, Computes c (pair a b) (a + b) :=
  by
  let G : ArithmeticSemiformula M 2 := Rew.emb ▹ (eventualGraph (encode c)).val
  let B : ArithmeticSemiformula M 3 := Rew.emb ▹ pairDef.val
  refine
    pa_formula_induction (P := fun b : M => Computes c (pair a b) (a + b))
      (“b. ∃ w, !B w&a b ∧ !G w(&a + b)”) ?_ ?_ ?_
  · intro b
    simp [Computes, ProgramGraph.Computes, G, B, Semiformula.eval_emb, pair_defined.iff]
  · simpa using hz
  · intro b hb
    simpa [add_assoc] using hs b hb

theorem computes_add (a b : M) : Computes addProgram (pair a b) (a + b) :=
  by
  apply runs_add_induction addProgram a
  · simp only [addProgram, runs_prec_zero, computes_id]
  · intro b hb
    apply (runs_prec_succ _ _ _ _ _).mpr
    refine ⟨a + b, hb, ?_⟩
    simp only [computes_comp, computes_succ, computes_right, pi₂_pair, exists_eq_left]

@[simp]
theorem computes_add_iff (a b z : M) : Computes addProgram (pair a b) z ↔ z = a + b :=
  ⟨fun h => computes_unique _ _ _ _ h (computes_add a b), fun h => h ▸ computes_add a b⟩

theorem computes_mul (a b : M) : Computes mulProgram (pair a b) (a * b) :=
  by
  let G : ArithmeticSemiformula M 2 := Rew.emb ▹ (eventualGraph (encode mulProgram)).val
  let B : ArithmeticSemiformula M 3 := Rew.emb ▹ pairDef.val
  have h : ∀ b : M, Computes mulProgram (pair a b) (a * b) :=
    by
    refine
      pa_formula_induction (P := fun b : M => Computes mulProgram (pair a b) (a * b))
        (“b. ∃ w, !B w&a b ∧ !G w(&a * b)”) ?_ ?_ ?_
    · intro b
      simp [Computes, ProgramGraph.Computes, G, B, Semiformula.eval_emb, pair_defined.iff]
    · simp only [mulProgram, runs_prec_zero, computes_zero, mul_zero]
    · intro b hb
      apply (runs_prec_succ _ _ _ _ _).mpr
      refine ⟨a * b, hb, ?_⟩
      simp only [computes_comp, computes_pair, computes_left, computes_right, pi₁_pair,
        pi₂_pair, exists_eq_left]
      simp [mul_add, add_comm]
  exact h b

@[simp]
theorem computes_mul_iff (a b z : M) : Computes mulProgram (pair a b) z ↔ z = a * b :=
  ⟨fun h => computes_unique _ _ _ _ h (computes_mul a b), fun h => h ▸ computes_mul a b⟩

private theorem computes_pred_rec (b : M) :
    Computes (.prec .zero (.comp .left .right)) (pair 0 b) (b - 1) :=
  by
  let c : Code := .prec .zero (.comp .left .right)
  let G : ArithmeticSemiformula M 2 := Rew.emb ▹ (eventualGraph (encode c)).val
  let B : ArithmeticSemiformula M 3 := Rew.emb ▹ pairDef.val
  let S : ArithmeticSemiformula M 3 := Rew.emb ▹ subDef.val
  have h : ∀ b : M, Computes c (pair 0 b) (b - 1) :=
    by
    refine
      pa_formula_induction (P := fun b : M => Computes c (pair 0 b) (b - 1))
        (“b. ∃ w z, !B w 0 b ∧ !S z b 1 ∧ !G w z”) ?_ ?_ ?_
    · intro b
      simp [Computes, ProgramGraph.Computes, G, B, S, Semiformula.eval_emb, pair_defined.iff,
        sub_defined.iff]
    · simp only [c, runs_prec_zero, computes_zero, Arithmetic.zero_sub]
    · intro b hb
      apply (runs_prec_succ _ _ _ _ _).mpr
      refine ⟨b - 1, hb, ?_⟩
      simp only [computes_comp, computes_left, computes_right, pi₁_pair, pi₂_pair,
        exists_eq_left, add_sub_self]
  exact h b

theorem computes_pred (b : M) : Computes predProgram b (b - 1) :=
  by
  rw [predProgram, computes_comp]
  refine ⟨pair 0 b, ?_, computes_pred_rec b⟩
  simp only [computes_pair, computes_zero, computes_id]
  exact ⟨0, _, rfl, rfl, rfl⟩

@[simp]
theorem computes_pred_iff (b z : M) : Computes predProgram b z ↔ z = b - 1 :=
  ⟨fun h => computes_unique _ _ _ _ h (computes_pred b), fun h => h ▸ computes_pred b⟩

theorem computes_sub (a b : M) : Computes subProgram (pair a b) (a - b) :=
  by
  let G : ArithmeticSemiformula M 2 := Rew.emb ▹ (eventualGraph (encode subProgram)).val
  let B : ArithmeticSemiformula M 3 := Rew.emb ▹ pairDef.val
  let S : ArithmeticSemiformula M 3 := Rew.emb ▹ subDef.val
  have h : ∀ b : M, Computes subProgram (pair a b) (a - b) :=
    by
    refine
      pa_formula_induction (P := fun b : M => Computes subProgram (pair a b) (a - b))
        (“b. ∃ w z, !B w&a b ∧ !S z&a b ∧ !G w z”) ?_ ?_ ?_
    · intro b
      simp [Computes, ProgramGraph.Computes, G, B, S, Semiformula.eval_emb, pair_defined.iff,
        sub_defined.iff]
    · simp only [subProgram, runs_prec_zero, computes_id, Arithmetic.sub_zero]
    · intro b hb
      apply (runs_prec_succ _ _ _ _ _).mpr
      refine ⟨a - b, hb, ?_⟩
      simp only [computes_comp, computes_right, pi₂_pair, exists_eq_left, computes_pred_iff,
        Arithmetic.sub_sub]
  exact h b

@[simp]
theorem computes_sub_iff (a b z : M) : Computes subProgram (pair a b) z ↔ z = a - b :=
  ⟨fun h => computes_unique _ _ _ _ h (computes_sub a b), fun h => h ▸ computes_sub a b⟩

private theorem computes_isZero_rec_total (b : M) :
    ∃ z, Computes (.prec (Code.const 1) .zero) (pair 0 b) z :=
  by
  let c : Code := .prec (Code.const 1) .zero
  let G : ArithmeticSemiformula M 2 := Rew.emb ▹ (eventualGraph (encode c)).val
  let B : ArithmeticSemiformula M 3 := Rew.emb ▹ pairDef.val
  have h : ∀ b : M, ∃ z, Computes c (pair 0 b) z :=
    by
    refine
      pa_formula_induction (P := fun b : M => ∃ z, Computes c (pair 0 b) z)
        (“b. ∃ z w, !B w 0 b ∧ !G w z”) ?_ ?_ ?_
    · intro b
      simp [Computes, ProgramGraph.Computes, G, B, Semiformula.eval_emb, pair_defined.iff]
    · exact ⟨1, by simp only [c, runs_prec_zero, computes_const, Nat.cast_one]⟩
    · intro b hb
      obtain ⟨z, hz⟩ := hb
      exact ⟨0, (runs_prec_succ _ _ _ _ _).mpr ⟨z, hz, (computes_zero _ _).mpr rfl⟩⟩
  exact h b

theorem computes_isZero_zero : Computes isZeroProgram (0 : M) 1 :=
  by
  rw [isZeroProgram, computes_comp]
  refine ⟨pair 0 0, ?_, ?_⟩
  · simp only [computes_pair, computes_zero, computes_id]
    exact ⟨0, _, rfl, rfl, rfl⟩
  · simp only [runs_prec_zero, computes_const, Nat.cast_one]

theorem computes_isZero_succ (b : M) : Computes isZeroProgram (b + 1) 0 :=
  by
  rw [isZeroProgram, computes_comp]
  refine ⟨pair 0 (b + 1), ?_, ?_⟩
  · simp only [computes_pair, computes_zero, computes_id]
    exact ⟨0, _, rfl, rfl, rfl⟩
  · obtain ⟨z, hz⟩ := computes_isZero_rec_total b
    exact (runs_prec_succ _ _ _ _ _).mpr ⟨z, hz, (computes_zero _ _).mpr rfl⟩

@[simp]
theorem computes_isZero_iff (b z : M) :
    Computes isZeroProgram b z ↔ (b = 0 ∧ z = 1) ∨ (b ≠ 0 ∧ z = 0) :=
  by
  rcases zero_or_succ b with rfl | ⟨b, rfl⟩
  · simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false]
    exact
      ⟨fun h => computes_unique _ _ _ _ h computes_isZero_zero, fun h =>
        h ▸ computes_isZero_zero⟩
  · have hn : b + 1 ≠ 0 := ne_of_gt (lt_of_le_of_lt (Arithmetic.zero_le b) (lt_add_one b))
    simp only [ne_eq, hn, false_and, not_false_eq_true, true_and, false_or]
    exact
      ⟨fun h => computes_unique _ _ _ _ h (computes_isZero_succ b), fun h =>
        h ▸ computes_isZero_succ b⟩

@[simp]
theorem computes_lt_iff (a b z : M) :
    Computes ltProgram (pair a b) z ↔ (a < b ∧ z = 1) ∨ (¬a < b ∧ z = 0) := by
  simp [ltProgram, computes_comp, computes_left, computes_right, computes_succ, pi₁_pair,
    pi₂_pair, exists_eq_left, computes_sub_iff, computes_isZero_iff, sub_eq_zero_iff_le,
    ← lt_iff_succ_le]

@[simp]
theorem computes_eq_iff (a b z : M) :
    Computes eqProgram (pair a b) z ↔ (a = b ∧ z = 1) ∨ (a ≠ b ∧ z = 0) :=
  by
  have hz : (a - b) + (b - a) = 0 ↔ a = b :=
    by
    constructor
    · intro h
      have h₁ : a - b = 0 :=
        le_antisymm (h ▸ (show a - b ≤ a - b + (b - a) from le_self_add)) (Arithmetic.zero_le _)
      have h₂ : b - a = 0 :=
        le_antisymm (h ▸ (show b - a ≤ a - b + (b - a) from le_add_self)) (Arithmetic.zero_le _)
      exact le_antisymm (sub_eq_zero_iff_le.mp h₁) (sub_eq_zero_iff_le.mp h₂)
    · rintro rfl
      simp
  simp [eqProgram, computes_comp, computes_left, computes_right, pi₁_pair, pi₂_pair,
    exists_eq_left, computes_sub_iff, computes_add_iff, computes_isZero_iff, hz]

end ConcreteEvaluator
end FailureOfComposition

end

end PointwiseComposition
