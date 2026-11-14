/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ArithmeticProgramOperations
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteMinimizationGraph

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Sequential bounded universal semidecision in arbitrary models of PA.
Each body call must return zero. A primitive-recursion program combines these
calls, and PA induction proves its graph equation also at nonstandard bounds. -/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open Encodable _root_.Nat.Partrec

namespace FailureOfComposition
namespace BoundedSemidecision

open ProgramGraph ConcreteEvaluator

private theorem forall_lt_succ_iff {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    (P : M → Prop) (b : M) : (∀ k : M, k < b + 1 → P k) ↔ (∀ k : M, k < b → P k) ∧ P b :=
  by
  constructor
  · intro h
    exact ⟨fun k hk => h k (lt_trans hk (lt_add_one b)), h b (lt_add_one b)⟩
  · rintro ⟨h, hb⟩ k hk
    rcases lt_or_eq_of_le (Arithmetic.lt_succ_iff_le.mp hk) with hlt | rfl
    · exact h k hlt
    · exact hb

/-- Return zero precisely on input zero; diverge on every other input. -/
def zeroOnlyProgram : Code :=
  .comp (.rfind' .left) (.pair Code.id .zero)

/-- Run a program and accept precisely its zero output. -/
def acceptZeroProgram (c : Code) : Code :=
  .comp zeroOnlyProgram c

/-- The recursion step supplies `pair candidate environment` to the body. -/
def boundedStepProgram (c : Code) : Code :=
  .comp (acceptZeroProgram c) (.pair (.comp .left .right) .left)

/-- Check every candidate below the bound, with input `pair environment bound`. -/
def boundedAllProgram (c : Code) : Code :=
  .prec .zero (boundedStepProgram c)

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

@[simp]
theorem computes_zeroOnly (x y : M) : Computes zeroOnlyProgram x y ↔ x = 0 ∧ y = 0 :=
  by
  have hr := eventualGraph_rfind_code_eval (M := M) .left x y
  change
    Computes (.rfind' .left) (pair x 0) y ↔
      Computes .left (pair x y) 0 ∧
        ∀ k : M, k < y → ∃ z : M, z ≠ 0 ∧ Computes .left (pair x k) z at hr
  simp only [computes_left, pi₁_pair] at hr
  rw [zeroOnlyProgram, computes_comp]
  simp only [computes_pair, computes_id, computes_zero]
  simp only [exists_and_left, exists_eq_left]
  rw [hr]
  constructor
  · rintro ⟨hx, hall⟩
    refine ⟨hx.symm, ?_⟩
    by_contra hy
    have hpos : (0 : M) < y := lt_of_le_of_ne (Arithmetic.zero_le y) (Ne.symm hy)
    obtain ⟨z, hz, rfl⟩ := hall 0 hpos
    exact hz hx.symm
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, fun k hk => False.elim ((not_lt_of_ge (Arithmetic.zero_le k)) hk)⟩

@[simp]
theorem computes_acceptZero (c : Code) (x y : M) :
    Computes (acceptZeroProgram c) x y ↔ y = 0 ∧ Computes c x 0 :=
  by
  simp only [acceptZeroProgram, computes_comp, computes_zeroOnly]
  constructor
  · rintro ⟨z, hz, rfl, rfl⟩
    exact ⟨rfl, hz⟩
  · rintro ⟨rfl, h⟩
    exact ⟨0, h, rfl, rfl⟩

@[simp]
theorem computes_boundedStep (c : Code) (a k z y : M) :
    Computes (boundedStepProgram c) (pair a (pair k z)) y ↔ y = 0 ∧ Computes c (pair k a) 0 :=
  by
  simp only [boundedStepProgram, computes_comp, computes_pair, computes_left, computes_right,
    pi₁_pair, pi₂_pair, exists_eq_left, computes_acceptZero]
  simp only [exists_and_left, exists_eq_left]

/-- The complete graph equation for bounded universal semidecision. No
termination or zero-output assumption on the body program is required. -/
theorem computes_boundedAll (c : Code) (a b y : M) :
    Computes (boundedAllProgram c) (pair a b) y ↔
      y = 0 ∧ ∀ k : M, k < b → Computes c (pair k a) 0 :=
  by
  let F : ArithmeticSemiformula M 2 :=
    Rew.emb ▹ (eventualGraph (encode (boundedAllProgram c))).val
  let G : ArithmeticSemiformula M 2 := Rew.emb ▹ (eventualGraph (encode c)).val
  let B : ArithmeticSemiformula M 3 := Rew.emb ▹ pairDef.val
  have h :
    ∀ b : M,
      ∀ y : M,
        Computes (boundedAllProgram c) (pair a b) y ↔
          y = 0 ∧ ∀ k : M, k < b → Computes c (pair k a) 0 :=
    by
    refine
      pa_formula_induction (P := fun b : M =>
        ∀ y : M,
          Computes (boundedAllProgram c) (pair a b) y ↔
            y = 0 ∧ ∀ k : M, k < b → Computes c (pair k a) 0)
        (“b. ∀ y, (∃ w, !B w&a b ∧ !F w y) ↔ y = 0 ∧ ∀ k < b, ∃ w, !B w k&a ∧ !G w 0”) ?_ ?_ ?_
    · intro b
      simp [ProgramGraph.Computes, F, G, B, Semiformula.eval_emb, pair_defined.iff]
    · intro y
      simp only [boundedAllProgram, runs_prec_zero, computes_zero]
      exact
        ⟨fun hy => ⟨hy, fun k hk => False.elim ((not_lt_of_ge (Arithmetic.zero_le k)) hk)⟩,
          And.left⟩
    · intro b ih y
      rw [boundedAllProgram, runs_prec_succ]
      change
        (∃ z,
            Computes (boundedAllProgram c) (pair a b) z ∧
              Computes (boundedStepProgram c) (pair a (pair b z)) y) ↔
          _
      simp only [ih, computes_boundedStep, forall_lt_succ_iff]
      constructor
      · rintro ⟨z, ⟨rfl, hprev⟩, hy, hb⟩
        exact ⟨hy, hprev, hb⟩
      · rintro ⟨hy, hprev, hb⟩
        exact ⟨0, ⟨rfl, hprev⟩, hy, hb⟩
  exact h b y

end BoundedSemidecision
end FailureOfComposition

end

end PointwiseComposition
