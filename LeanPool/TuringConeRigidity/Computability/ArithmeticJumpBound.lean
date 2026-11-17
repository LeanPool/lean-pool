/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticJumpBound.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticPresentationProperty

/-!
# Arithmetic Jump Bound
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.UniformArithmetic
open ArithmeticHierarchy OracleJump UniformOracle
noncomputable section

theorem form_mono {Y n s P} (h : Form Y n s P) {m : ℕ} (hnm : n ≤ m) :
    Form Y m s P := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero => exact h
  | succ k ih => exact ih.raise

theorem Arith.normal_form {P} (h : Arith P) :
    ∃ k, ∀ O Y, (∀ i, Reduces (O i) Y) → Sigma Y k (P O) := by
  induction h with
  | pure P hP =>
    refine ⟨0,fun O Y _ => ?_⟩
    classical
    exact total_primrec (Primrec.ite hP (Primrec.const 1) (Primrec.const 0))
  | query i =>
    refine ⟨0,fun O Y h => ?_⟩
    have hh := RecursiveIn.iff_nat.mp (h i)
    exact hh.of_eq (fun v => by simp [oracleFunction])
  | neg h ih =>
    obtain ⟨k,hk⟩ := ih
    exact ⟨k+1,fun O Y h => (hk O Y h).neg.switch⟩
  | and h g ih ig =>
    obtain ⟨k,hk⟩ := ih
    obtain ⟨l,hl⟩ := ig
    exact ⟨max k l,fun O Y h =>
      (form_mono (hk O Y h) (le_max_left _ _)).and
        (form_mono (hl O Y h) (le_max_right _ _))⟩
  | ex h ih =>
    obtain ⟨k,hk⟩ := ih
    exact ⟨k+1,fun O Y h => (hk O Y h).raise.ex⟩
  | comp f h hf ih =>
    obtain ⟨k,hk⟩ := ih
    exact ⟨k,fun O Y h => (hk O Y h).comp hf⟩

theorem Arith.jump_bound {P} (h : Arith P) :
    ∃ k, ∀ O Y, (∀ i, Reduces (O i) Y) → RecursivePred (iterate Y k) (P O) := by
  obtain ⟨k,hk⟩ := h.normal_form
  exact ⟨k,fun O Y hY => form_recursive (hk O Y hY)⟩

theorem arithmetic_comprehension (M : Set Oracle)
    (hdown : ∀ {A B}, B ∈ M → Reduces A B → A ∈ M)
    (hjump : ∀ {A}, A ∈ M → jump A ∈ M)
    {P} (h : Arith P) (O : Oracles) {Y : Oracle} (hY : Y ∈ M)
    (hO : ∀ i, Reduces (O i) Y) :
    (fun v => @decide (P O v) (Classical.propDecidable _)) ∈ M := by
  classical
  obtain ⟨k,hk⟩ := h.jump_bound
  have hm : ∀ n, iterate Y n ∈ M := by
    intro n
    induction n with
    | zero => exact hY
    | succ n ih => exact hjump ih
  apply hdown (hm k)
  apply RecursiveIn.iff_nat.mpr
  exact (hk O Y hO).of_eq (fun v => by simp [oracleFunction])

end
end TuringRigidity.UniformArithmetic

end OAI
