/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Machine.PostMachineThue
public import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# TM0PostAdapter

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability

open Turing

namespace TM0PostAdapter

/-- A write instruction of `TM0` is simulated by writing while moving right,
then returning left. -/
inductive Phase (Q : Type*)
  | normal (q : Q)
  | returnLeft (q : Q)

instance {Q : Type*} [Finite Q] : Finite (Phase Q) :=
  Finite.of_injective
    (fun s => match s with
      | Phase.normal q => (false, q)
      | Phase.returnLeft q => (true, q))
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- Convert Mathlib's atomic move-or-write `TM0` into the combined
write-and-move binary machine used by Post's rewriting construction. -/
def machine {Q : Type*} [Inhabited Q] (M : TM0.Machine Bool Q) :
    PostMachine.Machine (Phase Q)
  | Phase.normal q, a =>
      match M q a with
      | none => none
      | some (q', TM0.Stmt.move d) =>
          some ⟨Phase.normal q', a,
            match d with
            | Turing.Dir.left => PostMachine.Direction.left
            | Turing.Dir.right => PostMachine.Direction.right⟩
      | some (q', TM0.Stmt.write b) =>
          some ⟨Phase.returnLeft q', b, PostMachine.Direction.right⟩
  | Phase.returnLeft q, a =>
      some ⟨Phase.normal q, a, PostMachine.Direction.left⟩

/-- Finite-list initial configuration corresponding to `TM0.init`. -/
def init {Q : Type*} [Inhabited Q] (input : List Bool) :
    PostMachine.Config (Phase Q) :=
  match input with
  | [] => ⟨Phase.normal default, [], false, []⟩
  | a :: right => ⟨Phase.normal default, [], a, right⟩

/-- The finite-list tape represents Mathlib's quotient tape; trailing blank
cells are therefore harmless. -/
def Represents {Q : Type*}
    (c : TM0.Cfg Bool Q) (d : PostMachine.Config (Phase Q)) : Prop :=
  ∃ q, d.state = Phase.normal q ∧ c.q = q ∧
    c.Tape = Turing.Tape.mk₂ d.left (d.head :: d.right)

private theorem init_represents {Q : Type*} [Inhabited Q] (input : List Bool) :
    Represents (TM0.init input) (init input : PostMachine.Config (Phase Q)) := by
  cases input with
  | nil =>
      exact ⟨default, rfl, rfl, rfl⟩
  | cons a right =>
      exact ⟨default, rfl, rfl, rfl⟩

/-- One atomic `TM0` step is simulated by one combined step for a move and by
two combined steps for a write. -/
theorem respects {Q : Type*} [Inhabited Q] (M : TM0.Machine Bool Q) :
    StateTransition.Respects (TM0.step M) (PostMachine.step (machine M))
      Represents := by
  intro c d hcd
  rcases hcd with ⟨q, hdq, hcq, htape⟩
  rcases c with ⟨qc, tape⟩
  rcases d with ⟨phase, left, a, right⟩
  change phase = Phase.normal q at hdq
  change qc = q at hcq
  subst phase
  subst qc
  change tape = Turing.Tape.mk₂ left (a :: right) at htape
  subst tape
  cases htrans : M q a with
  | none =>
      simp [TM0.step, Turing.Tape.mk₂, Turing.Tape.mk',
        PostMachine.step, machine, htrans]
  | some cmd =>
      rcases cmd with ⟨q', stmt⟩
      cases stmt with
      | move dir =>
          simp only [TM0.step, Turing.Tape.mk₂, Turing.Tape.mk',
            Turing.ListBlank.head_mk, List.headI_cons, htrans, Option.map_some]
          cases dir with
          | left =>
              cases left with
              | nil =>
                  refine ⟨⟨Phase.normal q', [], false, a :: right⟩, ?_, ?_⟩
                  · exact ⟨q', rfl, rfl, by
                      simp [Turing.Tape.mk₂, Turing.Tape.move, Turing.Tape.mk']⟩
                  · exact Relation.TransGen.single (by
                      simp [PostMachine.step, machine, htrans])
              | cons b left =>
                  refine ⟨⟨Phase.normal q', left, b, a :: right⟩, ?_, ?_⟩
                  · exact ⟨q', rfl, rfl, by
                      simp [Turing.Tape.mk₂, Turing.Tape.move, Turing.Tape.mk']⟩
                  · exact Relation.TransGen.single (by
                      simp [PostMachine.step, machine, htrans])
          | right =>
              cases right with
              | nil =>
                  refine ⟨⟨Phase.normal q', a :: left, false, []⟩, ?_, ?_⟩
                  · exact ⟨q', rfl, rfl, by
                      simp [Turing.Tape.mk₂, Turing.Tape.move, Turing.Tape.mk']⟩
                  · exact Relation.TransGen.single (by
                      simp [PostMachine.step, machine, htrans])
              | cons b right =>
                  refine ⟨⟨Phase.normal q', a :: left, b, right⟩, ?_, ?_⟩
                  · exact ⟨q', rfl, rfl, by
                      simp [Turing.Tape.mk₂, Turing.Tape.move, Turing.Tape.mk']⟩
                  · exact Relation.TransGen.single (by
                      simp [PostMachine.step, machine, htrans])
      | write b =>
          simp only [TM0.step, Turing.Tape.mk₂, Turing.Tape.mk',
            Turing.ListBlank.head_mk, List.headI_cons, htrans, Option.map_some]
          cases right with
          | nil =>
              refine ⟨⟨Phase.normal q', left, b, [false]⟩, ?_, ?_⟩
              · exact ⟨q', rfl, rfl, by
                  simp only [Turing.Tape.write, Turing.Tape.mk₂,
                    Turing.Tape.mk', Turing.ListBlank.head_mk,
                    Turing.ListBlank.tail_mk, List.headI_cons,
                    List.tail_cons]
                  congr 1
                  exact Quotient.sound' (Or.inl ⟨1, rfl⟩)⟩
              · have h₁ :
                    ⟨Phase.returnLeft q', b :: left, false, []⟩ ∈
                      PostMachine.step (machine M)
                        ⟨Phase.normal q, left, a, []⟩ := by
                  simp [PostMachine.step, machine, htrans]
                have h₂ :
                    ⟨Phase.normal q', left, b, [false]⟩ ∈
                      PostMachine.step (machine M)
                        ⟨Phase.returnLeft q', b :: left, false, []⟩ := by
                  simp [PostMachine.step, machine]
                have path₁ : StateTransition.Reaches₁
                    (PostMachine.step (machine M))
                    ⟨Phase.normal q, left, a, []⟩
                    ⟨Phase.returnLeft q', b :: left, false, []⟩ :=
                  Relation.TransGen.single h₁
                exact path₁.tail h₂
          | cons x right =>
              refine ⟨⟨Phase.normal q', left, b, x :: right⟩, ?_, ?_⟩
              · exact ⟨q', rfl, rfl, by
                  simp [Turing.Tape.mk₂, Turing.Tape.write, Turing.Tape.mk']⟩
              · have h₁ :
                    ⟨Phase.returnLeft q', b :: left, x, right⟩ ∈
                      PostMachine.step (machine M)
                        ⟨Phase.normal q, left, a, x :: right⟩ := by
                  simp [PostMachine.step, machine, htrans]
                have h₂ :
                    ⟨Phase.normal q', left, b, x :: right⟩ ∈
                      PostMachine.step (machine M)
                        ⟨Phase.returnLeft q', b :: left, x, right⟩ := by
                  simp [PostMachine.step, machine]
                have path₁ : StateTransition.Reaches₁
                    (PostMachine.step (machine M))
                    ⟨Phase.normal q, left, a, x :: right⟩
                    ⟨Phase.returnLeft q', b :: left, x, right⟩ :=
                  Relation.TransGen.single h₁
                exact path₁.tail h₂

/-- The combined machine has the same halting domain as the Mathlib machine. -/
theorem eval_dom_iff {Q : Type*} [Inhabited Q]
    (M : TM0.Machine Bool Q) (input : List Bool) :
    (StateTransition.eval (PostMachine.step (machine M)) (init input)).Dom ↔
      (TM0.eval M input).Dom := by
  rw [TM0.eval]
  simpa using StateTransition.tr_eval_dom (respects M) (init_represents input)

theorem terminates_iff_tm0_eval_dom {Q : Type*} [Inhabited Q]
    (M : TM0.Machine Bool Q) (input : List Bool) :
    MachineThue.Terminates (PostMachine.step (machine M)) (init input) ↔
      (TM0.eval M input).Dom :=
  MachineThue.terminates_iff_eval_dom.trans (eval_dom_iff M input)

/-- Direct fixed-target Thue characterization of Mathlib `TM0` halting. -/
theorem thue_iff_tm0_eval_dom {Q : Type*} [Inhabited Q]
    (M : TM0.Machine Bool Q) (input : List Bool) :
    ThueEq (PostMachine.system (machine M))
        (PostMachine.encode (init input))
        (PostMachine.target : List (PostMachine.Symbol (Phase Q))) ↔
      (TM0.eval M input).Dom :=
  (PostMachine.terminates_iff (machine M) (init input)).symm.trans
    (terminates_iff_tm0_eval_dom M input)

theorem thue_system_finite {Q : Type*} [Inhabited Q] [Finite Q]
    (M : TM0.Machine Bool Q) :
    Set.Finite (PostMachine.system (machine M)) :=
  PostMachine.system_finite _

end TM0PostAdapter

end Undecidability
