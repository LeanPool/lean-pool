/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maxence Faldor, Moritz Firsching
-/
module

public import LeanPool.CryptidsGoldbach.Machines

/-!
# Goldbach21

21-state Turing machine halting-equivalent to the 25-state Goldbach machine.
-/

@[expose] public section

namespace ConjectureMachines.Goldbach21

open Turing StateTransition

/-- The original 25-state transition table used for the reference execution. -/
abbrev refM : Machine 25 2 := Machines.goldbach25
/-- The compressed 21-state transition table. -/
abbrev candM : Machine 21 2 := Machines.goldbach21

/-- 25-state Goldbach reference machine (`goldbach_25`, Yao & Leng 2024). -/
abbrev reference : BundledMachine 2 := Machines.goldbach25.bundle

/-- 21-state Goldbach candidate machine (`goldbach_21`). -/
abbrev candidate : BundledMachine 2 := Machines.goldbach21.bundle

theorem candidate_fewer_states : candidate.states < reference.states := by
  decide

/-- A 25-state intermediate machine with the candidate search order and redundant states. -/
def edited : Machine 25 2 := Machine.ofRows [
  [some (0, .right, 11), some (1, .right, 3)],
  [some (1, .right, 18), some (1, .right, 1)],
  [some (1, .left, 11), some (0, .right, 5)],
  [none, some (1, .right, 4)],
  [some (0, .left, 16), some (1, .right, 6)],
  [some (1, .left, 18), some (1, .right, 5)],
  [some (0, .right, 7), some (0, .left, 7)],
  [some (0, .left, 14), some (1, .left, 22)],
  [some (0, .right, 9), some (0, .left, 8)],
  [some (1, .right, 0), some (0, .left, 9)],
  [some (0, .right, 11), some (0, .right, 18)],
  [some (1, .right, 11), some (0, .right, 12)],
  [some (1, .right, 13), some (1, .right, 12)],
  [some (0, .left, 14), some (0, .left, 20)],
  [some (1, .left, 15), some (1, .left, 14)],
  [some (1, .left, 16), some (0, .left, 23)],
  [some (1, .left, 18), some (1, .left, 16)],
  [some (0, .right, 7), some (1, .left, 18)],
  [some (0, .right, 2), some (0, .left, 19)],
  [some (0, .right, 0), some (1, .left, 19)],
  [some (1, .left, 21), some (1, .left, 20)],
  [some (0, .left, 22), some (0, .left, 9)],
  [some (0, .right, 0), some (0, .left, 22)],
  [some (1, .right, 24), some (1, .left, 23)],
  [some (1, .right, 3), some (1, .right, 24)]
]

/-- Embed the 21 candidate states into the reachable states of the intermediate machine. -/
def embed (q : Fin 21) : Fin 25 :=
  if q.val = 0 then ⟨2, by omega⟩
  else if q.val = 1 then ⟨0, by omega⟩
  else if q.val = 2 then ⟨23, by omega⟩
  else if q.val < 8 then ⟨q.val, by omega⟩
  else if q.val = 8 then ⟨9, by omega⟩
  else if q.val < 15 then ⟨q.val + 2, by omega⟩
  else if q.val = 15 then ⟨24, by omega⟩
  else ⟨q.val + 2, by omega⟩

theorem transition_embed (q : Fin 21) (a : Fin 2) :
    edited.transition (embed q) a =
      (candM.transition q a).map fun t => (t.1, t.2.1, embed t.2.2) := by
  revert q a; decide

theorem step_embed (q : Fin 21) (T : Tape (Fin 2)) :
    step edited ⟨embed q, T⟩ =
      (step candM ⟨q, T⟩).map fun c => ⟨embed c.state, c.tape⟩ := by
  simp only [step, transition_embed, Option.map_map]
  rcases candM.transition q T.head with _ | ⟨a, d, q'⟩ <;> rfl

theorem respects_embed :
    Respects (step candM) (step edited)
      fun c₁ c₂ => c₂ = ⟨embed c₁.state, c₁.tape⟩ := by
  intro c₁ c₂ h
  subst h
  obtain ⟨q, T⟩ := c₁
  rcases e : step candM ⟨q, T⟩ with _ | c
  · simpa [step_embed] using e
  · exact ⟨⟨embed c.state, c.tape⟩, rfl,
      Relation.TransGen.single (by simp [step_embed, e])⟩

theorem candidate_iff_edited :
    Halts candM ↔ (eval (step edited) ⟨2, default⟩).Dom :=
  (StateTransition.tr_eval_dom respects_embed rfl).symm

/-- Execute exactly `n` transitions, returning `none` if a transition halts early. -/
def nSteps (M : Machine 25 2) (n : ℕ) : Cfg 25 2 → Option (Cfg 25 2) :=
  Nat.rec (motive := fun _ => Cfg 25 2 → Option (Cfg 25 2))
    (fun c => some c)
    (fun _ ih c => (step M c).bind ih)
    n

@[simp]
theorem nSteps_zero (M : Machine 25 2) (c : Cfg 25 2) :
    nSteps M 0 c = some c := rfl

@[simp]
theorem nSteps_succ (M : Machine 25 2) (n : ℕ) (c : Cfg 25 2) :
    nSteps M (n + 1) c = (step M c).bind (nSteps M n) := rfl

attribute [eqns nSteps_zero nSteps_succ] nSteps

theorem nSteps_reaches {M : Machine 25 2} {n : ℕ} {c c' : Cfg 25 2}
    (h : nSteps M n c = some c') : Reaches (step M) c c' := by
  induction n generalizing c with
  | zero =>
    injection h with h'
    subst h'
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    simp only [nSteps, Option.bind_eq_some_iff] at h
    obtain ⟨c₁, hstep, hrest⟩ := h
    exact Relation.ReflTransGen.head hstep (ih hrest)

theorem nSteps_eval_dom {M : Machine 25 2} {n : ℕ} {c c' : Cfg 25 2}
    (h : nSteps M n c = some c') :
    (eval (step M) c).Dom ↔ (eval (step M) c').Dom := by
  rw [StateTransition.reaches_eval (nSteps_reaches h)]

theorem nSteps_add {M : Machine 25 2} (m n : ℕ) (c : Cfg 25 2) :
    nSteps M (m + n) c = (nSteps M m c).bind (nSteps M n) := by
  induction m generalizing c with
  | zero => simp [nSteps]
  | succ m ih =>
    rw [Nat.succ_add, nSteps, nSteps]
    cases step M c <;> simp [ih]

theorem nSteps_bind_eq {M : Machine 25 2} {m n : ℕ} {c c₁ c₂ : Cfg 25 2}
    (h₁ : nSteps M m c = some c₁) (h₂ : nSteps M n c₁ = some c₂) :
    nSteps M (m + n) c = some c₂ := by
  rw [nSteps_add, h₁, Option.bind_some, h₂]

theorem step_nSteps {M : Machine 25 2} {n : ℕ} {c c₁ c₂ : Cfg 25 2}
    (h₁ : step M c = some c₁) (h₂ : nSteps M n c₁ = some c₂) :
    nSteps M (n + 1) c = some c₂ := by
  rw [nSteps, h₁, Option.bind_some, h₂]

theorem step_one {M : Machine 25 2} {c c₁ : Cfg 25 2} (h : step M c = some c₁) :
    nSteps M 1 c = some c₁ := by
  rw [nSteps, h]; rfl

theorem mk_append_replicate_zero (l : List (Fin 2)) (n : ℕ) :
    ListBlank.mk (l ++ List.replicate n 0) = ListBlank.mk l :=
  Quotient.sound' (Or.inr ⟨n, rfl⟩)

theorem boot_reference_47 :
    nSteps refM 47 init =
      some ⟨19, ⟨1, ListBlank.mk [1, 1], ListBlank.mk [0, 1]⟩⟩ := by
  have h : nSteps refM 47 init =
      some ⟨19, ⟨1, ListBlank.mk ([1, 1] ++ List.replicate 2 0), ListBlank.mk [0, 1]⟩⟩ := rfl
  rw [h, mk_append_replicate_zero]

theorem boot_edited_125 :
    nSteps edited 125 ⟨2, default⟩ =
      some ⟨0, ⟨1, ListBlank.mk [], ListBlank.mk [1, 1, 0, 1, 1, 1]⟩⟩ := by
  have h : nSteps edited 125 ⟨2, default⟩ =
      some ⟨0, ⟨1, ListBlank.mk ([] ++ List.replicate 2 0),
        ListBlank.mk ([1, 1, 0, 1, 1, 1] ++ List.replicate 1 0)⟩⟩ := rfl
  rw [h, mk_append_replicate_zero, mk_append_replicate_zero]

/-- A tape whose head is the first cell of the left list, facing the right list. -/
def Tape.mkL (L R : ListBlank (Fin 2)) : Tape (Fin 2) :=
  ⟨L.head, L.tail, R⟩

@[simp]
theorem Tape.mkL_cons (a : Fin 2) (L R : ListBlank (Fin 2)) :
    Tape.mkL (L.cons a) R = ⟨a, L, R⟩ := by
  simp [Tape.mkL]

@[simp]
theorem Tape.mk'_cons (a : Fin 2) (L R : ListBlank (Fin 2)) :
    Tape.mk' L (R.cons a) = ⟨a, L, R⟩ := by
  simp [Tape.mk']

theorem step_right {M : Machine 25 2} {q q' : Fin 25} {a b : Fin 2}
    (h : M.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', ⟨R.head, L.cons b, R.tail⟩⟩ := by
  simp [step, h, Tape.write, Tape.move]

theorem step_right_cons {M : Machine 25 2} {q q' : Fin 25} {a b c : Fin 2}
    (h : M.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, ⟨a, L, R.cons c⟩⟩ = some ⟨q', ⟨c, L.cons b, R⟩⟩ := by
  simp [step, h, Tape.write, Tape.move]

theorem step_mkL_left {M : Machine 25 2} {q q' : Fin 25} {a b : Fin 2}
    (h : M.transition q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, h, Tape.mkL, Tape.write, Tape.move]

theorem step_mkL_right {M : Machine 25 2} {q q' : Fin 25} {a b : Fin 2}
    (h : M.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_right {M : Machine 25 2} {q q' : Fin 25} {a b : Fin 2}
    (h : M.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, h, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_left {M : Machine 25 2} {q q' : Fin 25} {a b : Fin 2}
    (h : M.transition q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem append_replicate_cons (k : ℕ) (b : Fin 2) (L : ListBlank (Fin 2)) :
    ListBlank.append (List.replicate k b) (L.cons b) =
      ListBlank.append (List.replicate (k + 1) b) L := by
  rw [List.replicate_succ', ListBlank.append_assoc, ListBlank.append, ListBlank.append]

theorem append_replicate_add (m n : ℕ) (b : Fin 2) (L : ListBlank (Fin 2)) :
    ListBlank.append (List.replicate m b) (ListBlank.append (List.replicate n b) L) =
      ListBlank.append (List.replicate (m + n) b) L := by
  rw [← ListBlank.append_assoc, ← List.replicate_add]

theorem nSteps_mkL_left_scan {M : Machine 25 2} {q : Fin 25} {a b : Fin 2}
    (h : M.transition q a = some (b, .left, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps M k ⟨q, Tape.mkL (ListBlank.append (List.replicate k a) L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append (List.replicate k b) R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mkL_left h]
    simp only [Option.bind_some]
    rw [ih (R.cons b), append_replicate_cons]

theorem nSteps_mk'_right_scan {M : Machine 25 2} {q : Fin 25} {a b : Fin 2}
    (h : M.transition q a = some (b, .right, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps M k ⟨q, Tape.mk' L (ListBlank.append (List.replicate k a) R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append (List.replicate k b) L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mk'_right h]
    simp only [Option.bind_some]
    rw [ih (L.cons b), append_replicate_cons]

/-- The all-blank one-sided binary tape. -/
def B0 : ListBlank (Fin 2) := ListBlank.mk []

@[simp]
theorem B0_cons_zero : B0.cons 0 = B0 :=
  mk_append_replicate_zero [] 1

/-- Two unary counters, of lengths `B` and `A`, separated by zero cells. -/
def counterTape (A B : ℕ) (L_base : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  ListBlank.append (List.replicate B 1)
    ((ListBlank.append (List.replicate A 1) (L_base.cons 0)).cons 0)

theorem sim_state6_d_ref (k : ℕ) (L_base R_rest : ListBlank (Fin 2)) :
    let L_cnt := ListBlank.append (List.replicate (k + 2) 1) (L_base.cons 0)
    let R_mid := R_rest.cons 0
    nSteps refM (2 + ((k + 2) + 2)) ⟨6, Tape.mk' (L_cnt.cons 1) (R_rest.cons 1)⟩ =
      some ⟨10, Tape.mk' ((L_base.cons 0).cons 1)
        (ListBlank.append (0 :: (List.replicate k 0 ++ [1])) R_mid)⟩ := by
  dsimp only
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_left (b := 0) (q' := 7) rfl _ _)
      (step_one (step_mkL_left (b := 1) (q' := 8) rfl _ _))) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 8) (a := 1) (b := 0) rfl (k + 2) _ _) ?_
  rw [List.replicate_succ, List.replicate_succ, ListBlank.append, ListBlank.append]
  refine step_nSteps (step_mkL_right (b := 0) (q' := 9) rfl _ _) ?_
  apply step_one
  simpa [ListBlank.append_assoc] using
    step_mk'_right (M := refM) (q := 9) (q' := 10) (a := 0) (b := 1) rfl
      (L_base.cons 0) (ListBlank.append (0 :: List.replicate k 0) ((R_rest.cons 0).cons 1))

theorem sim_state6_d_edit (k : ℕ) (L_base R_rest : ListBlank (Fin 2)) :
    let L_cnt := ListBlank.append (List.replicate (k + 2) 1) (L_base.cons 0)
    let R_mid := R_rest.cons 0
    nSteps edited (2 + ((k + 2) + (2 + ((k + 1) + (6 + (k + 1))))))
      ⟨6, Tape.mk' (L_cnt.cons 1) ((R_rest.cons 1).cons 1)⟩ =
      some ⟨0, Tape.mk' ((L_base.cons 0).cons 1)
        (ListBlank.append (0 :: (List.replicate k 0 ++ [1])) (R_mid.cons 1))⟩ := by
  dsimp only
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_left (b := 0) (q' := 7) rfl _ _)
      (step_one (step_mkL_left (b := 1) (q' := 22) rfl _ _))) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 22) (a := 1) (b := 0) rfl (k + 2) _ _) ?_
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right (b := 0) (q' := 0) rfl _ _)
      (step_one (step_mk'_right (b := 0) (q' := 11) rfl _ _))) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 11) (a := 0) (b := 1) rfl (k + 1) _ _) ?_
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_right (b := 0) (q' := 12) rfl _ _)
      (step_nSteps (step_mk'_right (b := 1) (q' := 13) rfl _ _)
        (step_nSteps (step_mk'_left (b := 0) (q' := 20) rfl _ _)
          (step_nSteps (step_mkL_left (b := 1) (q' := 20) rfl _ _)
            (step_nSteps (step_mkL_left (b := 1) (q' := 21) rfl _ _)
              (step_one (step_mkL_left (b := 0) (q' := 9) rfl _ _))))))) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 9) (a := 1) (b := 0) rfl k _ _) ?_
  rw [append_replicate_cons, List.replicate_succ, ListBlank.append]
  apply step_one
  simpa [ListBlank.append_assoc] using
    step_mkL_right (M := edited) (q := 9) (q' := 0) (a := 0) (b := 1) rfl
      (L_base.cons 0) (ListBlank.append (0 :: List.replicate k 0) (((R_rest.cons 0).cons 1).cons 1))

theorem sim_state6_accept_ref (k : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    let L_cnt := ListBlank.append (List.replicate (k + 2) 1) (L_base.cons 0)
    step refM ⟨6, Tape.mk' (L_cnt.cons 1) (R_end.cons 0)⟩ =
      some ⟨5, Tape.mkL (L_cnt.cons 1) (R_end.cons 0)⟩ :=
  step_mk'_left (a := 0) (b := 0) (q' := 5) rfl _ _

theorem sim_state6_accept_edit (k : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    let L_cnt := ListBlank.append (List.replicate (k + 2) 1) (L_base.cons 0)
    nSteps edited (2 + ((k + 2) + (2 + ((k + 1) + (6 + (k + (1 + (k + 3))))))))
      ⟨6, Tape.mk' (L_cnt.cons 1) ((R_end.cons 0).cons 1)⟩ =
      some ⟨6, Tape.mk' ((L_cnt.cons 1).cons 1) (R_end.cons 0)⟩ := by
  dsimp only
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_left (b := 0) (q' := 7) rfl _ _)
      (step_one (step_mkL_left (b := 1) (q' := 22) rfl _ _))) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 22) (a := 1) (b := 0) rfl (k + 2) _ _) ?_
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right (b := 0) (q' := 0) rfl _ _)
      (step_one (step_mk'_right (b := 0) (q' := 11) rfl _ _))) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 11) (a := 0) (b := 1) rfl (k + 1) _ _) ?_
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_right (b := 0) (q' := 12) rfl _ _)
      (step_nSteps (step_mk'_right (b := 1) (q' := 13) rfl _ _)
        (step_nSteps (step_mk'_left (b := 0) (q' := 14) rfl _ _)
          (step_nSteps (step_mkL_left (b := 1) (q' := 14) rfl _ _)
            (step_nSteps (step_mkL_left (b := 1) (q' := 15) rfl _ _)
              (step_one (step_mkL_left (b := 0) (q' := 23) rfl _ _))))))) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 23) (a := 1) (b := 1) rfl k _ _) ?_
  refine nSteps_bind_eq (step_one (step_mkL_right (b := 1) (q' := 24) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 24) (a := 1) (b := 1) rfl k _ _) ?_
  rw [append_replicate_cons]
  refine step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl _ _) ?_
  refine step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl _ _) ?_
  exact step_one (step_mk'_right (b := 1) (q' := 6) rfl _ _)

theorem sim_state19_to_0_ref (L₁ R₁ : ListBlank (Fin 2)) :
    nSteps refM 2 ⟨19, ⟨1, L₁, R₁.cons 0⟩⟩ =
      some ⟨0, Tape.mk' ((L₁.cons 1).cons 0) R₁⟩ :=
  step_nSteps (step_right_cons (q' := 2) rfl L₁ R₁)
    (step_one (step_right (q' := 0) rfl (L₁.cons 1) R₁))

theorem sim_state19_to_0_mkL_ref (L₁ R₁ : ListBlank (Fin 2)) :
    nSteps refM 2 ⟨19, Tape.mkL (L₁.cons 1) (R₁.cons 0)⟩ =
      some ⟨0, Tape.mk' ((L₁.cons 1).cons 0) R₁⟩ := by
  simp only [Tape.mkL_cons]
  exact sim_state19_to_0_ref L₁ R₁

theorem sim_state0_p1 (L₁ L₂ R₁ R₂ : ListBlank (Fin 2)) :
    nSteps refM 2 ⟨0, Tape.mk' L₁ ((R₁.cons 0).cons 1)⟩ =
      some ⟨16, Tape.mkL (L₁.cons 1) (R₁.cons 0)⟩ ∧
    nSteps edited 3 ⟨0, Tape.mk' L₂ (((R₂.cons 0).cons 1).cons 1)⟩ =
      some ⟨16, Tape.mkL ((L₂.cons 1).cons 1) (R₂.cons 0)⟩ := by
  constructor
  · exact step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl L₁ (R₁.cons 0))
      (step_one (step_mk'_left (a := 0) (b := 0) (q' := 16) rfl (L₁.cons 1) R₁))
  · exact step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl L₂ ((R₂.cons 0).cons 1))
      (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl (L₂.cons 1) (R₂.cons 0))
        (step_one (step_mk'_left (a := 0) (b := 0) (q' := 16) rfl ((L₂.cons 1).cons 1) R₂)))

theorem sim_state0_p2_ref (L₁ R₁ : ListBlank (Fin 2)) :
    nSteps refM 3 ⟨0, Tape.mk' L₁ (((R₁.cons 0).cons 1).cons 1)⟩ =
      some ⟨5, Tape.mkL ((L₁.cons 1).cons 1) (R₁.cons 0)⟩ :=
  step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl L₁ ((R₁.cons 0).cons 1))
    (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl (L₁.cons 1) (R₁.cons 0))
      (step_one (step_mk'_left (a := 0) (b := 0) (q' := 5) rfl ((L₁.cons 1).cons 1) R₁)))

theorem sim_state0_p2_edit (L₂ R₂ : ListBlank (Fin 2)) :
    nSteps edited 3 ⟨0, Tape.mk' L₂ ((((R₂.cons 0).cons 1).cons 1).cons 1)⟩ =
      some ⟨6, Tape.mk' (((L₂.cons 1).cons 1).cons 1) (R₂.cons 0)⟩ :=
  step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl L₂ (((R₂.cons 0).cons 1).cons 1))
    (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl (L₂.cons 1) ((R₂.cons 0).cons 1))
      (step_one (step_mk'_right (b := 1) (q' := 6) rfl ((L₂.cons 1).cons 1) (R₂.cons 0))))

theorem sim_state0_p_ge3 (L₁ L₂ R₁ R₂ : ListBlank (Fin 2)) :
    nSteps refM 3 ⟨0, Tape.mk' L₁ (((R₁.cons 1).cons 1).cons 1)⟩ =
      some ⟨6, Tape.mk' (((L₁.cons 1).cons 1).cons 1) R₁⟩ ∧
    nSteps edited 3 ⟨0, Tape.mk' L₂ ((((R₂.cons 1).cons 1).cons 1).cons 1)⟩ =
      some ⟨6, Tape.mk' (((L₂.cons 1).cons 1).cons 1) (R₂.cons 1)⟩ := by
  constructor
  · exact step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl L₁ ((R₁.cons 1).cons 1))
      (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl (L₁.cons 1) (R₁.cons 1))
        (step_one (step_mk'_right (b := 1) (q' := 6) rfl ((L₁.cons 1).cons 1) R₁)))
  · exact step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl L₂ (((R₂.cons 1).cons 1).cons 1))
      (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl (L₂.cons 1) ((R₂.cons 1).cons 1))
        (step_one (step_mk'_right (b := 1) (q' := 6) rfl ((L₂.cons 1).cons 1) (R₂.cons 1))))

theorem nSteps_state16_to_19_right {M : Machine 25 2}
    (h16_1 : M.transition 16 1 = some (1, .left, 16))
    (h16_0 : M.transition 16 0 = some (1, .left, 17))
    (h17_1 : M.transition 17 1 = some (0, .left, 19))
    (d : ℕ) (L_p1 R_p2 : ListBlank (Fin 2)) :
    nSteps M (d + 2)
      ⟨16, Tape.mkL (ListBlank.append (List.replicate d 1) ((L_p1.cons 1).cons 0)) R_p2⟩ =
      some ⟨19, Tape.mkL L_p1 (((ListBlank.append (List.replicate d 1) R_p2).cons 1).cons 0)⟩ := by
  refine nSteps_bind_eq (nSteps_mkL_left_scan h16_1 d _ _) ?_
  refine step_nSteps (step_mkL_left h16_0 _ _) ?_
  exact step_one (step_mkL_left h17_1 _ _)

theorem nSteps_state16_to_19_left {M : Machine 25 2}
    (h16_1 : M.transition 16 1 = some (1, .left, 16))
    (h16_0 : M.transition 16 0 = some (1, .left, 17))
    (h17_0 : M.transition 17 0 = some (0, .right, 10))
    (h10_1 : M.transition 10 1 = some (0, .right, 18))
    (h18_1 : M.transition 18 1 = some (1, .right, 18))
    (h18_0 : M.transition 18 0 = some (1, .left, 17))
    (h17_1 : M.transition 17 1 = some (0, .left, 19))
    (d m : ℕ) (L_blank R_p2 : ListBlank (Fin 2)) :
    nSteps M (d + (3 + ((d + m + 1) + 2)))
      ⟨16, Tape.mkL (ListBlank.append (List.replicate d 1) ((L_blank.cons 0).cons 0))
        (ListBlank.append (List.replicate (m + 1) 1) (R_p2.cons 0))⟩ =
      some ⟨19, Tape.mkL (ListBlank.append (List.replicate (d + m) 1) ((L_blank.cons 0).cons 0))
        ((R_p2.cons 1).cons 0)⟩ := by
  refine nSteps_bind_eq (nSteps_mkL_left_scan h16_1 d _ _) ?_
  have h_rep : ListBlank.append (List.replicate d 1)
      (ListBlank.append (List.replicate (m + 1) 1) (R_p2.cons 0)) =
      ListBlank.append (List.replicate (d + m + 1) 1) (R_p2.cons 0) := by
    rw [← ListBlank.append_assoc, ← List.replicate_add, Nat.add_assoc]
  rw [h_rep]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_left h16_0 _ _)
      (step_nSteps (step_mkL_right h17_0 _ _)
        (step_one (step_mk'_right h10_1 _ _)))) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan h18_1 (d + m + 1) _ _) ?_
  refine step_nSteps (step_mk'_left h18_0 _ _) ?_
  rw [List.replicate_succ, ListBlank.append]
  exact step_one (step_mkL_left h17_1 _ _)

theorem nSteps_pass_11_to_13 {M : Machine 25 2}
    (h11_1 : M.transition 11 1 = some (0, .right, 12))
    (h12_1 : M.transition 12 1 = some (1, .right, 12))
    (h12_0 : M.transition 12 0 = some (1, .right, 13))
    (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps M (1 + (m + 1))
      ⟨11, Tape.mk' L ((ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1)⟩ =
      some ⟨13, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) R⟩ := by
  refine nSteps_bind_eq (step_one (step_mk'_right h11_1 _ _)) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan h12_1 m _ _) ?_
  exact step_one (step_mk'_right h12_0 _ _)

theorem nSteps_pass_13_one_to_21 {M : Machine 25 2}
    (h13_1 : M.transition 13 1 = some (0, .left, 20))
    (h20_1 : M.transition 20 1 = some (1, .left, 20))
    (h20_0 : M.transition 20 0 = some (1, .left, 21))
    (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps M (1 + ((m + 1) + 1))
      ⟨13, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) (R.cons 1)⟩ =
      some ⟨21, Tape.mkL L ((ListBlank.append (List.replicate (m + 1) 1) (R.cons 0)).cons 1)⟩ := by
  refine nSteps_bind_eq (step_one (step_mk'_left h13_1 _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan h20_1 (m + 1) _ _) ?_
  exact step_one (step_mkL_left h20_0 _ _)

theorem nSteps_pass_13_zero_to_15 {M : Machine 25 2} {b14 : Fin 2}
    (h13_0 : M.transition 13 0 = some (0, .left, 14))
    (h14_1 : M.transition 14 1 = some (1, .left, 14))
    (h14_0 : M.transition 14 0 = some (b14, .left, 15))
    (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps M (1 + ((m + 1) + 1))
      ⟨13, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) (R.cons 0)⟩ =
      some ⟨15,
        Tape.mkL L ((ListBlank.append (List.replicate (m + 1) 1) (R.cons 0)).cons b14)⟩ := by
  refine nSteps_bind_eq (step_one (step_mk'_left h13_0 _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan h14_1 (m + 1) _ _) ?_
  exact step_one (step_mkL_left h14_0 _ _)

theorem nSteps_pass_21_b0_to_11 {M : Machine 25 2} {q_mid : Fin 25}
    (h21_0 : M.transition 21 0 = some (0, .left, 22))
    (h22_1 : M.transition 22 1 = some (0, .left, 22))
    (h22_0 : M.transition 22 0 = some (0, .right, q_mid))
    (hq_0 : M.transition q_mid 0 = some (0, .right, 11))
    (h11_0 : M.transition 11 0 = some (1, .right, 11))
    (A : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps M (1 + (A + (2 + A)))
      ⟨21, Tape.mkL (counterTape A 0 L_base) R⟩ =
      some ⟨11, Tape.mk' (counterTape 0 A L_base) R⟩ := by
  unfold counterTape
  simp only [List.replicate_zero, ListBlank.append]
  refine nSteps_bind_eq (step_one (step_mkL_left h21_0 _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan h22_1 A _ _) ?_
  rw [append_replicate_cons]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right h22_0 _ _)
      (step_one (by
        rw [List.replicate_succ, ListBlank.append]
        exact step_mk'_right hq_0 _ _))) ?_
  exact nSteps_mk'_right_scan h11_0 A _ _

theorem nSteps_pass_21_bsucc_to_11 {M : Machine 25 2} {q_mid : Fin 25}
    (h21_1 : M.transition 21 1 = some (0, .left, 9))
    (h9_1 : M.transition 9 1 = some (0, .left, 9))
    (h9_0 : M.transition 9 0 = some (1, .right, q_mid))
    (hq_0 : M.transition q_mid 0 = some (0, .right, 11))
    (h11_0 : M.transition 11 0 = some (1, .right, 11))
    (A b : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps M (1 + (b + (2 + b)))
      ⟨21, Tape.mkL (counterTape A (b + 1) L_base) R⟩ =
      some ⟨11, Tape.mk' (counterTape (A + 1) b L_base) R⟩ := by
  unfold counterTape
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq (step_one (step_mkL_left h21_1 _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan h9_1 b _ _) ?_
  rw [append_replicate_cons]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right h9_0 _ _)
      (step_one (by
        rw [List.replicate_succ, ListBlank.append]
        exact step_mk'_right hq_0 _ _))) ?_
  exact nSteps_mk'_right_scan h11_0 b _ _

theorem nSteps_pass_15_bsucc_to_6_ref (A b : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps refM (1 + (b + (1 + ((b + 1) + 2))))
      ⟨15, Tape.mkL (counterTape A (b + 1) L_base) ((R.cons 1).cons 0)⟩ =
      some ⟨6, Tape.mk'
        ((ListBlank.append (List.replicate (A + b + 3) 1) (L_base.cons 0)).cons 1) R⟩ := by
  unfold counterTape
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq (step_one (step_mkL_left (b := 1) (q' := 23) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 23) (a := 1) (b := 1) rfl b _ _) ?_
  rw [append_replicate_cons]
  refine nSteps_bind_eq (step_one (step_mkL_right (b := 1) (q' := 24) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 24) (a := 1) (b := 1) rfl (b + 1) _ _) ?_
  have h_cnt : ListBlank.append (List.replicate (b + 1) 1)
      ((ListBlank.append (List.replicate A 1) (L_base.cons 0)).cons 1) =
      ListBlank.append (List.replicate (A + b + 2) 1) (L_base.cons 0) := by
    rw [append_replicate_cons, append_replicate_add]
    have : b + 1 + 1 + A = A + b + 2 := by omega
    rw [this]
  rw [h_cnt]
  refine step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl _ _) ?_
  exact step_one (step_mk'_right (b := 1) (q' := 6) rfl _ _)

theorem nSteps_pass_15_bsucc_to_6_edit (A b : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps edited (1 + (b + (1 + (b + 3))))
      ⟨15, Tape.mkL (counterTape A (b + 1) L_base) ((R.cons 1).cons 1)⟩ =
      some ⟨6, Tape.mk'
        ((ListBlank.append (List.replicate (A + b + 3) 1) (L_base.cons 0)).cons 1) R⟩ := by
  unfold counterTape
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq (step_one (step_mkL_left (b := 0) (q' := 23) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 23) (a := 1) (b := 1) rfl b _ _) ?_
  refine nSteps_bind_eq (step_one (step_mkL_right (b := 1) (q' := 24) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 24) (a := 1) (b := 1) rfl b _ _) ?_
  have h_cnt : ListBlank.append (List.replicate b 1)
      ((ListBlank.append (List.replicate A 1) (L_base.cons 0)).cons 1) =
      ListBlank.append (List.replicate (A + b + 1) 1) (L_base.cons 0) := by
    rw [append_replicate_cons, append_replicate_add]
    have : b + 1 + A = A + b + 1 := by omega
    rw [this]
  rw [h_cnt]
  refine step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl _ _) ?_
  refine step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl _ _) ?_
  exact step_one (step_mk'_right (b := 1) (q' := 6) rfl _ _)

theorem nSteps_pass_15_b0_to_16_ref (A m : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    nSteps refM (2 + (A + 1))
      ⟨15, Tape.mkL (counterTape A 0 L_base)
        ((ListBlank.append (List.replicate (m + 1) 1) (R_end.cons 0)).cons 0)⟩ =
      some ⟨16, Tape.mkL (L_base.cons 0)
        (ListBlank.append (List.replicate (A + m + 3) 1) (R_end.cons 0))⟩ := by
  unfold counterTape
  simp only [List.replicate_zero, ListBlank.append]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right (b := 1) (q' := 7) rfl _ _)
      (step_one (step_mk'_left (b := 1) (q' := 16) rfl _ _))) ?_
  have h_cnt : (ListBlank.append (List.replicate A 1) (L_base.cons 0)).cons 1 =
      ListBlank.append (List.replicate (A + 1) 1) (L_base.cons 0) := rfl
  rw [h_cnt]
  refine Eq.trans (nSteps_mkL_left_scan (q := 16) (a := 1) (b := 1) rfl (A + 1) _ _) ?_
  congr 2
  rw [append_replicate_cons, append_replicate_add]
  have : A + 1 + 1 + (m + 1) = A + m + 3 := by omega
  rw [this]

theorem nSteps_pass_15_b0_to_16_edit (A m : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    nSteps edited (1 + A)
      ⟨15, Tape.mkL (counterTape A 0 L_base)
        ((ListBlank.append (List.replicate (m + 1) 1) (R_end.cons 0)).cons 1)⟩ =
      some ⟨16, Tape.mkL (L_base.cons 0)
        (ListBlank.append (List.replicate (A + m + 3) 1) (R_end.cons 0))⟩ := by
  unfold counterTape
  simp only [List.replicate_zero, ListBlank.append]
  refine nSteps_bind_eq (step_one (step_mkL_left (b := 1) (q' := 16) rfl _ _)) ?_
  refine Eq.trans (nSteps_mkL_left_scan (q := 16) (a := 1) (b := 1) rfl A _ _) ?_
  congr 2
  rw [append_replicate_cons, append_replicate_cons, append_replicate_add]
  have : A + 1 + 1 + (m + 1) = A + m + 3 := by omega
  rw [this]

theorem nSteps_pass_11_b0 {M : Machine 25 2} {q_mid : Fin 25}
    (h11_1 : M.transition 11 1 = some (0, .right, 12))
    (h12_1 : M.transition 12 1 = some (1, .right, 12))
    (h12_0 : M.transition 12 0 = some (1, .right, 13))
    (h13_1 : M.transition 13 1 = some (0, .left, 20))
    (h20_1 : M.transition 20 1 = some (1, .left, 20))
    (h20_0 : M.transition 20 0 = some (1, .left, 21))
    (h21_0 : M.transition 21 0 = some (0, .left, 22))
    (h22_1 : M.transition 22 1 = some (0, .left, 22))
    (h22_0 : M.transition 22 0 = some (0, .right, q_mid))
    (hq_0 : M.transition q_mid 0 = some (0, .right, 11))
    (h11_0 : M.transition 11 0 = some (1, .right, 11))
    (A m : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps M ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (1 + (A + (2 + A)))))
      ⟨11, Tape.mk' (counterTape A 0 L_base)
        ((ListBlank.append (List.replicate m 1) ((R.cons 1).cons 0)).cons 1)⟩ =
      some ⟨11, Tape.mk' (counterTape 0 A L_base)
        ((ListBlank.append (List.replicate (m + 1) 1) (R.cons 0)).cons 1)⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 h11_1 h12_1 h12_0 m _ _)
    (nSteps_bind_eq (nSteps_pass_13_one_to_21 h13_1 h20_1 h20_0 m _ _)
      (nSteps_pass_21_b0_to_11 h21_0 h22_1 h22_0 hq_0 h11_0 A _ _))

theorem nSteps_pass_11_bsucc {M : Machine 25 2} {q_mid : Fin 25}
    (h11_1 : M.transition 11 1 = some (0, .right, 12))
    (h12_1 : M.transition 12 1 = some (1, .right, 12))
    (h12_0 : M.transition 12 0 = some (1, .right, 13))
    (h13_1 : M.transition 13 1 = some (0, .left, 20))
    (h20_1 : M.transition 20 1 = some (1, .left, 20))
    (h20_0 : M.transition 20 0 = some (1, .left, 21))
    (h21_1 : M.transition 21 1 = some (0, .left, 9))
    (h9_1 : M.transition 9 1 = some (0, .left, 9))
    (h9_0 : M.transition 9 0 = some (1, .right, q_mid))
    (hq_0 : M.transition q_mid 0 = some (0, .right, 11))
    (h11_0 : M.transition 11 0 = some (1, .right, 11))
    (A b m : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps M ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (1 + (b + (2 + b)))))
      ⟨11, Tape.mk' (counterTape A (b + 1) L_base)
        ((ListBlank.append (List.replicate m 1) ((R.cons 1).cons 0)).cons 1)⟩ =
      some ⟨11, Tape.mk' (counterTape (A + 1) b L_base)
        ((ListBlank.append (List.replicate (m + 1) 1) (R.cons 0)).cons 1)⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 h11_1 h12_1 h12_0 m _ _)
    (nSteps_bind_eq (nSteps_pass_13_one_to_21 h13_1 h20_1 h20_0 m _ _)
      (nSteps_pass_21_bsucc_to_11 h21_1 h9_1 h9_0 hq_0 h11_0 A b _ _))

theorem nSteps_pass_11_to_6_ref (A b m : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    nSteps refM ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (1 + (b + (1 + ((b + 1) + 2))))))
      ⟨11, Tape.mk' (counterTape A (b + 1) L_base)
        ((ListBlank.append (List.replicate m 1) ((R_end.cons 0).cons 0)).cons 1)⟩ =
      some ⟨6, Tape.mk' ((ListBlank.append (List.replicate (A + b + 3) 1) (L_base.cons 0)).cons 1)
        (ListBlank.append (List.replicate m 1) (R_end.cons 0))⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 rfl rfl rfl m _ _)
    (nSteps_bind_eq (nSteps_pass_13_zero_to_15 rfl rfl rfl m _ _)
      (nSteps_pass_15_bsucc_to_6_ref A b _ _))

theorem nSteps_pass_11_to_6_edit (A b m : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    nSteps edited ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (1 + (b + (1 + (b + 3))))))
      ⟨11, Tape.mk' (counterTape A (b + 1) L_base)
        ((ListBlank.append (List.replicate m 1) ((R_end.cons 0).cons 0)).cons 1)⟩ =
      some ⟨6, Tape.mk' ((ListBlank.append (List.replicate (A + b + 3) 1) (L_base.cons 0)).cons 1)
        (ListBlank.append (List.replicate m 1) (R_end.cons 0))⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 rfl rfl rfl m _ _)
    (nSteps_bind_eq (nSteps_pass_13_zero_to_15 rfl rfl rfl m _ _)
      (nSteps_pass_15_bsucc_to_6_edit A b _ _))

theorem nSteps_pass_11_to_16_ref (A m : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    nSteps refM ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (2 + (A + 1))))
      ⟨11, Tape.mk' (counterTape A 0 L_base)
        ((ListBlank.append (List.replicate m 1) ((R_end.cons 0).cons 0)).cons 1)⟩ =
      some ⟨16, Tape.mkL (L_base.cons 0)
        (ListBlank.append (List.replicate (A + m + 3) 1) (R_end.cons 0))⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 rfl rfl rfl m _ _)
    (nSteps_bind_eq (nSteps_pass_13_zero_to_15 rfl rfl rfl m _ _)
      (nSteps_pass_15_b0_to_16_ref A m _ _))

theorem nSteps_pass_11_to_16_edit (A m : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    nSteps edited ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (1 + A)))
      ⟨11, Tape.mk' (counterTape A 0 L_base)
        ((ListBlank.append (List.replicate m 1) ((R_end.cons 0).cons 0)).cons 1)⟩ =
      some ⟨16, Tape.mkL (L_base.cons 0)
        (ListBlank.append (List.replicate (A + m + 3) 1) (R_end.cons 0))⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 rfl rfl rfl m _ _)
    (nSteps_bind_eq (nSteps_pass_13_zero_to_15 rfl rfl rfl m _ _)
      (nSteps_pass_15_b0_to_16_edit A m _ _))

theorem sim_state5_to_0_left_from_0_ref (p1 p2 : ℕ) (L_blank R_end : ListBlank (Fin 2)) :
    nSteps refM (3 + (p1 + (1 + ((p1 + 1) + 1))))
      ⟨5, Tape.mkL ((L_blank.cons 0).cons 0)
        (ListBlank.append (List.replicate p1 1)
          ((ListBlank.append (List.replicate p2 1) (R_end.cons 0)).cons 0))⟩ =
      some ⟨0, Tape.mk' (L_blank.cons 0)
        (ListBlank.append (List.replicate (p1 + p2 + 2) 1) (R_end.cons 0))⟩ := by
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_left (b := 0) (q' := 2) rfl _ _)
      (step_nSteps (step_mkL_right (b := 0) (q' := 0) rfl _ _)
        (step_one (step_mk'_right (b := 1) (q' := 1) rfl _ _)))) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 1) (a := 1) (b := 1) rfl p1 _ _) ?_
  rw [append_replicate_cons]
  refine nSteps_bind_eq (step_one (step_mk'_left (b := 1) (q' := 2) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 2) (a := 1) (b := 1) rfl (p1 + 1) _ _) ?_
  have h_merge : ListBlank.append (List.replicate (p1 + 1) 1)
      ((ListBlank.append (List.replicate p2 1) (R_end.cons 0)).cons 1) =
      ListBlank.append (List.replicate (p1 + p2 + 2) 1) (R_end.cons 0) := by
    rw [append_replicate_cons, append_replicate_add]
    have : p1 + 1 + 1 + p2 = p1 + p2 + 2 := by omega
    rw [this]
  rw [h_merge]
  exact step_one (step_mkL_right (b := 0) (q' := 0) rfl _ _)

/-!
## Primality Predicate and `refM` Semantics
-/

/-- No integer from `k + 2` up to `p - 1` divides `p`. -/
def NoFactorFrom (k p : ℕ) : Prop :=
  ∀ d, k + 2 ≤ d → d < p → ¬ d ∣ p

/-- Trial-division primality: at least two, with no smaller nontrivial divisor. -/
def IsPrime (p : ℕ) : Prop :=
  2 ≤ p ∧ NoFactorFrom 0 p

theorem not_isPrime_zero : ¬ IsPrime 0 := by
  intro ⟨h, _⟩; omega

theorem not_isPrime_one : ¬ IsPrime 1 := by
  intro ⟨h, _⟩; omega

theorem isPrime_two : IsPrime 2 := by
  refine ⟨by omega, fun d hd1 hd2 _ => by omega⟩

/-- The natural number is the sum of two trial-division primes. -/
def HasGoldbachPair (n : ℕ) : Prop :=
  ∃ a b : ℕ, IsPrime a ∧ IsPrime b ∧ a + b = n

/-- The left tape suffix used to encode the reference machine search orientation. -/
def LBase1 : Bool → ℕ → ListBlank (Fin 2)
  | true, q => ListBlank.append (List.replicate (q + 1) 1) B0
  | false, _ => B0

/-- The right tape suffix used to encode the reference machine search orientation. -/
def REnd1 : Bool → ℕ → ListBlank (Fin 2)
  | true, _ => B0
  | false, q => ListBlank.append (List.replicate q 1) B0

/-- Reference primality-test entry with orientation `is_right` and unary parameters `q`, `p`. -/
def cfg0 (is_right : Bool) (q p : ℕ) : Cfg 25 2 :=
  ⟨0, Tape.mk' ((LBase1 is_right q).cons 0)
    (ListBlank.append (List.replicate p 1) ((REnd1 is_right q).cons 0))⟩

/-- Reference trial-division entry, with divisor `k + 2` and remaining unary length `r`. -/
def cfg6 (is_right : Bool) (q k r : ℕ) : Cfg 25 2 :=
  ⟨6, Tape.mk'
    ((ListBlank.append (List.replicate (k + 2) 1) ((LBase1 is_right q).cons 0)).cons 1)
    (ListBlank.append (List.replicate r 1) ((REnd1 is_right q).cons 0))⟩

/-- Reference division-loop configuration with unary counters `A`, `B`, `m`, `r`. -/
def cfg11 (is_right : Bool) (q A B m r : ℕ) : Cfg 25 2 :=
  ⟨11, Tape.mk' (counterTape A B (LBase1 is_right q))
    ((ListBlank.append (List.replicate m 1)
      ((ListBlank.append (List.replicate r 1) ((REnd1 is_right q).cons 0)).cons 0)).cons 1)⟩

/-- Reference primality-test exit, selecting its continuation from the primality result. -/
def cfgExit (is_right is_prime : Bool) (q p : ℕ) : Cfg 25 2 :=
  ⟨if is_prime then 5 else 16, Tape.mkL ((LBase1 is_right q).cons 0)
    (ListBlank.append (List.replicate p 1) ((REnd1 is_right q).cons 0))⟩

theorem cfg11_step_b0 (is_right : Bool) (q A m r' : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps refM s (cfg11 is_right q A 0 m (r' + 1)) =
        some (cfg11 is_right q 0 A (m + 1) r') := by
  have h := nSteps_pass_11_b0 (M := refM) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    A m (LBase1 is_right q) (ListBlank.append (List.replicate r' 1) ((REnd1 is_right q).cons 0))
  exact ⟨_, by omega, h⟩

theorem cfg11_step_bsucc (is_right : Bool) (q A b m r' : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps refM s (cfg11 is_right q A (b + 1) m (r' + 1)) =
        some (cfg11 is_right q (A + 1) b (m + 1) r') := by
  have h := nSteps_pass_11_bsucc (M := refM) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    A b m (LBase1 is_right q) (ListBlank.append (List.replicate r' 1) ((REnd1 is_right q).cons 0))
  exact ⟨_, by omega, h⟩

theorem cfg11_drain (is_right : Bool) (q k r A B m : ℕ)
    (hAB : A + B = k + 1) (hdvd : (k + 2) ∣ B + m + 2) :
    ∃ A' B', A' + B' = k + 1 ∧ (k + 2) ∣ B' + (m + r) + 2 ∧
      ∃ s, nSteps refM s (cfg11 is_right q A B m r) =
        some (cfg11 is_right q A' B' (m + r) 0) := by
  induction r generalizing A B m with
  | zero =>
    exact ⟨A, B, hAB, by simpa using hdvd, 0, rfl⟩
  | succ r' ih =>
    cases B with
    | zero =>
      obtain ⟨s₁, _, hs₁⟩ := cfg11_step_b0 is_right q A m r'
      have hdvd' : (k + 2) ∣ A + (m + 1) + 2 := by
        have h_eq : A + (m + 1) + 2 = (0 + m + 2) + (k + 2) := by omega
        rw [h_eq]
        exact Nat.dvd_add_self_right.mpr hdvd
      obtain ⟨A', B', hAB', hdvd'', s₂, hs₂⟩ := ih 0 A (m + 1) (by omega) hdvd'
      have h_mr : m + 1 + r' = m + (r' + 1) := by omega
      rw [h_mr] at hdvd'' hs₂
      exact ⟨A', B', hAB', hdvd'', s₁ + s₂, nSteps_bind_eq hs₁ hs₂⟩
    | succ b =>
      obtain ⟨s₁, _, hs₁⟩ := cfg11_step_bsucc is_right q A b m r'
      have hdvd' : (k + 2) ∣ b + (m + 1) + 2 := by
        have h_eq : b + (m + 1) + 2 = b + 1 + m + 2 := by omega
        rwa [h_eq]
      obtain ⟨A', B', hAB', hdvd'', s₂, hs₂⟩ := ih (A + 1) b (m + 1) (by omega) hdvd'
      have h_mr : m + 1 + r' = m + (r' + 1) := by omega
      rw [h_mr] at hdvd'' hs₂
      exact ⟨A', B', hAB', hdvd'', s₁ + s₂, nSteps_bind_eq hs₁ hs₂⟩

theorem cfg6_step_enter (is_right : Bool) (q k r' : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps refM s (cfg6 is_right q k (r' + 1)) =
        some (cfg11 is_right q 1 k 0 r') := by
  have h1 := sim_state6_d_ref k (LBase1 is_right q)
    (ListBlank.append (List.replicate r' 1) ((REnd1 is_right q).cons 0))
  have h10_to_11 (L_b R_m : ListBlank (Fin 2)) :
      nSteps refM (1 + k)
        ⟨10, Tape.mk' ((L_b.cons 0).cons 1)
          (ListBlank.append (0 :: (List.replicate k 0 ++ [1])) R_m)⟩ =
        some ⟨11, Tape.mk' (counterTape 1 k L_b) (R_m.cons 1)⟩ := by
    rw [ListBlank.append, ListBlank.append_assoc, ListBlank.append, ListBlank.append]
    refine nSteps_bind_eq (step_one
      (step_mk'_right (M := refM) (q := 10) (q' := 11) (a := 0) (b := 0) rfl _ _)) ?_
    exact nSteps_mk'_right_scan (M := refM) (q := 11) (a := 0) (b := 1) rfl k _ _
  have h := nSteps_bind_eq h1 (h10_to_11 (LBase1 is_right q) _)
  exact ⟨_, by omega, h⟩

theorem cfg6_pass_succ_dvd (is_right : Bool) (q k r' : ℕ)
    (hdvd : (k + 2) ∣ (k + 4 + r')) :
    ∃ s, 1 ≤ s ∧
      nSteps refM s (cfg6 is_right q k (r' + 1)) =
        some (cfgExit is_right false q (k + 4 + r')) := by
  obtain ⟨s₀, _, hs₀⟩ := cfg6_step_enter is_right q k r'
  obtain ⟨A', B', hAB', hdvd', s₁, hs₁⟩ :=
    cfg11_drain is_right q k r' 1 k 0 (by omega) (by simp)
  simp only [Nat.zero_add] at hdvd' hs₁
  have hB0 : B' = 0 := by
    have h_eq1 : k + 4 + r' = (r' + 2) + (k + 2) := by omega
    have h_eq2 : B' + r' + 2 = B' + (r' + 2) := by omega
    rw [h_eq1, Nat.dvd_add_self_right] at hdvd
    rw [h_eq2] at hdvd'
    exact Nat.eq_zero_of_dvd_of_lt ((Nat.dvd_add_iff_left hdvd).mpr hdvd') (by omega)
  subst hB0
  have h_fin := nSteps_pass_11_to_16_ref A' r' (LBase1 is_right q) (REnd1 is_right q)
  have h_p : A' + r' + 3 = k + 4 + r' := by omega
  have h_fin' : nSteps refM ((1 + (r' + 1)) + ((1 + ((r' + 1) + 1)) + (2 + (A' + 1))))
      (cfg11 is_right q A' 0 r' 0) = some (cfgExit is_right false q (k + 4 + r')) := by
    unfold cfg11 cfgExit
    simpa [List.replicate_zero, ListBlank.append, h_p] using h_fin
  exact ⟨_, by omega, nSteps_bind_eq hs₀ (nSteps_bind_eq hs₁ h_fin')⟩

theorem cfg6_pass_succ_not_dvd (is_right : Bool) (q k r' : ℕ)
    (hdvd : ¬ (k + 2) ∣ (k + 4 + r')) :
    ∃ s, 1 ≤ s ∧
      nSteps refM s (cfg6 is_right q k (r' + 1)) =
        some (cfg6 is_right q (k + 1) r') := by
  obtain ⟨s₀, _, hs₀⟩ := cfg6_step_enter is_right q k r'
  obtain ⟨A', B', hAB', hdvd', s₁, hs₁⟩ :=
    cfg11_drain is_right q k r' 1 k 0 (by omega) (by simp)
  simp only [Nat.zero_add] at hdvd' hs₁
  cases B' with
  | zero =>
    exfalso
    apply hdvd
    have h_eq1 : k + 4 + r' = (r' + 2) + (k + 2) := by omega
    rw [h_eq1, Nat.dvd_add_self_right]
    simpa using hdvd'
  | succ b =>
    have h_fin := nSteps_pass_11_to_6_ref A' b r' (LBase1 is_right q) (REnd1 is_right q)
    have h_k : A' + b + 3 = (k + 1) + 2 := by omega
    have h_fin' :
        nSteps refM ((1 + (r' + 1)) + ((1 + ((r' + 1) + 1)) + (1 + (b + (1 + ((b + 1) + 2))))))
          (cfg11 is_right q A' (b + 1) r' 0) = some (cfg6 is_right q (k + 1) r') := by
      unfold cfg11 cfg6
      simpa [List.replicate_zero, ListBlank.append, h_k] using h_fin
    exact ⟨_, by omega, nSteps_bind_eq hs₀ (nSteps_bind_eq hs₁ h_fin')⟩

open Classical in
theorem cfg6_eval (is_right : Bool) (q k r : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps refM s (cfg6 is_right q k r) =
        some (cfgExit is_right (decide (NoFactorFrom k (k + 3 + r))) q (k + 3 + r)) := by
  induction r generalizing k with
  | zero =>
    have h_nf : NoFactorFrom k (k + 3 + 0) := by
      intro d hd1 hd2 hdvd
      have hd_eq : d = k + 2 := by omega
      subst hd_eq
      have h1 : (k + 2) ∣ 1 := by
        have h_add : (k + 2) ∣ (k + 2) + 1 := hdvd
        exact (Nat.dvd_add_right ( Nat.dvd_refl (k + 2) )).mp h_add
      have := Nat.le_of_dvd (by omega) h1
      omega
    rw [decide_eq_true h_nf]
    have h1 := sim_state6_accept_ref k (LBase1 is_right q) (REnd1 is_right q)
    have h_cnt :
        (ListBlank.append (List.replicate (k + 2) 1) ((LBase1 is_right q).cons 0)).cons 1 =
        ListBlank.append (List.replicate (k + 3) 1) ((LBase1 is_right q).cons 0) := rfl
    refine ⟨1 + (k + 3), by omega, ?_⟩
    unfold cfg6 cfgExit
    simp only [Nat.add_zero, List.replicate_zero, ListBlank.append, ↓reduceIte]
    refine nSteps_bind_eq (step_one h1) ?_
    rw [h_cnt]
    exact nSteps_mkL_left_scan (M := refM) (q := 5) (a := 1) (b := 1) rfl (k + 3) _ _
  | succ r' ih =>
    have h_arith : k + 3 + (r' + 1) = k + 4 + r' := by omega
    rw [h_arith]
    by_cases hdvd : (k + 2) ∣ (k + 4 + r')
    · have h_nf : ¬ NoFactorFrom k (k + 4 + r') := fun h => h (k + 2) (by omega) (by omega) hdvd
      rw [decide_eq_false h_nf]
      exact cfg6_pass_succ_dvd is_right q k r' hdvd
    · obtain ⟨s₁, _, hs₁⟩ := cfg6_pass_succ_not_dvd is_right q k r' hdvd
      obtain ⟨s₂, _, hs₂⟩ := ih (k + 1)
      have h_arith2 : k + 1 + 3 + r' = k + 4 + r' := by omega
      rw [h_arith2] at hs₂
      have h_iff : NoFactorFrom k (k + 4 + r') ↔ NoFactorFrom (k + 1) (k + 4 + r') := by
        constructor
        · intro h d hd1 hd2
          exact h d (by omega) hd2
        · intro h d hd1 hd2
          rcases Nat.eq_or_lt_of_le hd1 with rfl | hd_gt
          · exact hdvd
          · exact h d (by omega) hd2
      have h_dec : decide (NoFactorFrom k (k + 4 + r')) =
          decide (NoFactorFrom (k + 1) (k + 4 + r')) := by
        simp [h_iff]
      rw [h_dec]
      exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

open Classical in
theorem cfg0_eval (is_right : Bool) (q p : ℕ) (hp : 1 ≤ p) :
    ∃ s, 1 ≤ s ∧
      nSteps refM s (cfg0 is_right q p) =
        some (cfgExit is_right (decide (IsPrime p)) q p) := by
  rcases Nat.eq_or_lt_of_le hp with rfl | hp2
  · rw [decide_eq_false not_isPrime_one]
    obtain ⟨h1, _⟩ := sim_state0_p1 ((LBase1 is_right q).cons 0) B0
      (REnd1 is_right q) B0
    refine ⟨2 + 1, by omega, ?_⟩
    unfold cfg0 cfgExit
    exact nSteps_bind_eq h1 (step_one
      (step_mkL_left (M := refM) (q := 16) (q' := 16) (a := 1) (b := 1) rfl _ _))
  · rcases Nat.eq_or_lt_of_le hp2 with rfl | hp3
    · rw [decide_eq_true isPrime_two]
      have h1 := sim_state0_p2_ref ((LBase1 is_right q).cons 0) (REnd1 is_right q)
      refine ⟨3 + 2, by omega, ?_⟩
      unfold cfg0 cfgExit
      exact nSteps_bind_eq h1 (step_nSteps
        (step_mkL_left (M := refM) (q := 5) (q' := 5) (a := 1) (b := 1) rfl _ _)
        (step_one (step_mkL_left (M := refM) (q := 5) (q' := 5) (a := 1) (b := 1) rfl _ _)))
    · obtain ⟨r0, rfl⟩ : ∃ r0, p = r0 + 3 := ⟨p - 3, by omega⟩
      obtain ⟨h1, _⟩ := sim_state0_p_ge3 ((LBase1 is_right q).cons 0) B0
        (ListBlank.append (List.replicate r0 1) ((REnd1 is_right q).cons 0)) B0
      have h_enter : nSteps refM 3 (cfg0 is_right q (r0 + 3)) =
          some (cfg6 is_right q 0 r0) := h1
      obtain ⟨s₂, _, hs₂⟩ := cfg6_eval is_right q 0 r0
      have h_prime_iff : IsPrime (r0 + 3) ↔ NoFactorFrom 0 (0 + 3 + r0) := by
        unfold IsPrime
        have h_eq : 0 + 3 + r0 = r0 + 3 := by omega
        rw [h_eq]
        exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      have h_dec : decide (IsPrime (r0 + 3)) = decide (NoFactorFrom 0 (0 + 3 + r0)) := by
        simp [h_prime_iff]
      have h_eq : 0 + 3 + r0 = r0 + 3 := by omega
      rw [h_dec]
      rw [h_eq] at hs₂ ⊢
      exact ⟨3 + s₂, by omega, nSteps_bind_eq h_enter hs₂⟩

theorem cfgExit_tt (q p : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps refM s (cfgExit true true q p) =
        some (cfg0 false p (q + 1)) := by
  have h_scan (Q P : ℕ) :
      nSteps refM (1 + (Q + 1))
        ⟨5, Tape.mkL ((ListBlank.append (List.replicate Q 1) (B0.cons 0)).cons 0)
          (ListBlank.append (List.replicate P 1) B0)⟩ =
        some ⟨0, Tape.mk' (B0.cons 0)
          (ListBlank.append (List.replicate Q 1)
            ((ListBlank.append (List.replicate P 1) B0).cons 0))⟩ := by
    refine nSteps_bind_eq (step_one (step_mkL_left rfl _ _)) ?_
    refine nSteps_bind_eq (nSteps_mkL_left_scan rfl Q _ _) ?_
    exact step_one (step_mkL_right rfl _ _)
  have h : nSteps refM (1 + ((q + 1) + 1)) (cfgExit true true q p) =
      some (cfg0 false p (q + 1)) := by
    unfold cfgExit cfg0
    simpa [LBase1, REnd1, B0_cons_zero] using h_scan (q + 1) p
  exact ⟨_, by omega, h⟩

theorem cfgExit_tf_succ (q' p : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps refM s (cfgExit true false (q' + 1) p) =
        some (cfg0 true q' (p + 1)) := by
  have hr1 := nSteps_state16_to_19_right (M := refM) rfl rfl rfl 0
    (ListBlank.append (List.replicate (q' + 1) 1) B0)
    (ListBlank.append (List.replicate p 1) B0)
  have hr2 := sim_state19_to_0_mkL_ref
    (ListBlank.append (List.replicate q' 1) B0)
    (ListBlank.append (List.replicate (p + 1) 1) B0)
  have h : nSteps refM (2 + 2) (cfgExit true false (q' + 1) p) =
      some (cfg0 true q' (p + 1)) := by
    unfold cfgExit cfg0
    simpa [LBase1, REnd1, B0_cons_zero, List.replicate_succ, ListBlank.append] using
      nSteps_bind_eq hr1 hr2
  exact ⟨_, by omega, h⟩

theorem cfgExit_tf_zero (p : ℕ) :
    ∃ s c, nSteps refM s (cfgExit true false 0 p) = some c ∧
      step refM c = none := by
  have hr : nSteps refM 2 (cfgExit true false 0 p) =
      some ⟨19, Tape.mkL B0
        (((ListBlank.append (List.replicate p 1) B0).cons 1).cons 0)⟩ := by
    unfold cfgExit
    simpa [LBase1, REnd1, B0_cons_zero] using
      nSteps_state16_to_19_right (M := refM) rfl rfl rfl 0 B0
        (ListBlank.append (List.replicate p 1) B0)
  have h_none : step refM ⟨19, Tape.mkL B0
      (((ListBlank.append (List.replicate p 1) B0).cons 1).cons 0)⟩ = none := by
    rw [← B0_cons_zero]; simp [step, Tape.mkL]; rfl
  exact ⟨2, _, hr, h_none⟩

theorem cfgExit_ft (q p : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps refM s (cfgExit false true q p) =
        some (cfg0 false 0 (p + q + 2)) := by
  have hr := sim_state5_to_0_left_from_0_ref p q B0 B0
  have h : nSteps refM (3 + (p + (1 + ((p + 1) + 1)))) (cfgExit false true q p) =
      some (cfg0 false 0 (p + q + 2)) := by
    unfold cfgExit cfg0
    simpa [LBase1, REnd1, B0_cons_zero] using hr
  exact ⟨_, by omega, h⟩

theorem cfgExit_ff_succ (q p' : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps refM s (cfgExit false false q (p' + 2)) =
        some (cfg0 true p' (q + 1)) := by
  have hr1 : nSteps refM (p' + 7)
      ⟨16, Tape.mkL B0
        (ListBlank.append (List.replicate (p' + 2) 1)
          ((ListBlank.append (List.replicate q 1) B0).cons 0))⟩ =
      some ⟨19, Tape.mkL (ListBlank.append (List.replicate (p' + 1) 1) B0)
        ((ListBlank.append (List.replicate (q + 1) 1) B0).cons 0)⟩ := by
    simpa [B0_cons_zero, List.replicate_succ, ListBlank.append,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      nSteps_state16_to_19_left (M := refM) rfl rfl rfl rfl rfl rfl rfl 0 (p' + 1) B0
        (ListBlank.append (List.replicate q 1) B0)
  have hr2 := sim_state19_to_0_mkL_ref
    (ListBlank.append (List.replicate p' 1) B0)
    (ListBlank.append (List.replicate (q + 1) 1) B0)
  have h : nSteps refM ((p' + 7) + 2) (cfgExit false false q (p' + 2)) =
      some (cfg0 true p' (q + 1)) := by
    unfold cfgExit cfg0
    simpa [LBase1, REnd1, B0_cons_zero, List.replicate_succ, ListBlank.append] using
      nSteps_bind_eq hr1 hr2
  exact ⟨_, by omega, h⟩

theorem cfgExit_ff_one (q : ℕ) :
    ∃ s c, nSteps refM s (cfgExit false false q 1) = some c ∧
      step refM c = none := by
  have hr : nSteps refM 6 (cfgExit false false q 1) =
      some ⟨19, Tape.mkL B0
        ((ListBlank.append (List.replicate (q + 1) 1) B0).cons 0)⟩ := by
    unfold cfgExit
    simpa [LBase1, REnd1, B0_cons_zero, List.replicate_succ, ListBlank.append] using
      nSteps_state16_to_19_left (M := refM) rfl rfl rfl rfl rfl rfl rfl 0 0 B0
        (ListBlank.append (List.replicate q 1) B0)
  have h_none : step refM ⟨19, Tape.mkL B0
      ((ListBlank.append (List.replicate (q + 1) 1) B0).cons 0)⟩ = none := by
    rw [← B0_cons_zero]; simp [step, Tape.mkL]; rfl
  exact ⟨6, _, hr, h_none⟩

/-- Reference search entry for the even number `2 * w + 4`. -/
def stageCfg (w : ℕ) : Cfg 25 2 :=
  cfg0 true (2 * w + 2) 1

open Classical in
theorem cfg0_partner_pass (w q p : ℕ) (hp : 1 ≤ p) (hsum : q + p = 2 * w + 3)
    (hp_prime : IsPrime p) (hq_prime : IsPrime (q + 1)) :
    ∃ s, 1 ≤ s ∧ nSteps refM s (cfg0 true q p) = some (stageCfg (w + 1)) := by
  obtain ⟨s₁, _, hs₁⟩ := cfg0_eval true q p hp
  rw [decide_eq_true hp_prime] at hs₁
  obtain ⟨s₂, _, hs₂⟩ := cfgExit_tt q p
  obtain ⟨s₃, _, hs₃⟩ := cfg0_eval false p (q + 1) (by omega)
  rw [decide_eq_true hq_prime] at hs₃
  obtain ⟨s₄, _, hs₄⟩ := cfgExit_ft p (q + 1)
  have h_sum2 : (q + 1) + p + 2 = (2 * (w + 1) + 2) + 2 := by omega
  rw [h_sum2] at hs₄
  obtain ⟨s₅, _, hs₅⟩ := cfg0_eval false 0 ((2 * (w + 1) + 2) + 2) (by omega)
  have h_not_prime : ¬ IsPrime ((2 * (w + 1) + 2) + 2) := by
    intro ⟨_, hnf⟩
    exact hnf 2 (by omega) (by omega) ⟨w + 3, by omega⟩
  rw [decide_eq_false h_not_prime] at hs₅
  obtain ⟨s₆, _, hs₆⟩ := cfgExit_ff_succ 0 (2 * (w + 1) + 2)
  exact ⟨_, by omega,
    nSteps_bind_eq hs₁ (nSteps_bind_eq hs₂ (nSteps_bind_eq hs₃
      (nSteps_bind_eq hs₄ (nSteps_bind_eq hs₅ hs₆))))⟩

open Classical in
theorem cfg0_partner_fail_succ (q' p : ℕ) (hp : 1 ≤ p)
    (hfail : ¬ (IsPrime p ∧ IsPrime (q' + 2))) :
    ∃ s, 1 ≤ s ∧ nSteps refM s (cfg0 true (q' + 1) p) = some (cfg0 true q' (p + 1)) := by
  obtain ⟨s₁, _, hs₁⟩ := cfg0_eval true (q' + 1) p hp
  by_cases hp_prime : IsPrime p
  · have hq_not_prime : ¬ IsPrime (q' + 2) := fun hq => hfail ⟨hp_prime, hq⟩
    rw [decide_eq_true hp_prime] at hs₁
    obtain ⟨s₂, _, hs₂⟩ := cfgExit_tt (q' + 1) p
    obtain ⟨s₃, _, hs₃⟩ := cfg0_eval false p (q' + 2) (by omega)
    rw [decide_eq_false hq_not_prime] at hs₃
    obtain ⟨s₄, _, hs₄⟩ := cfgExit_ff_succ p q'
    exact ⟨_, by omega, nSteps_bind_eq hs₁ (nSteps_bind_eq hs₂ (nSteps_bind_eq hs₃ hs₄))⟩
  · rw [decide_eq_false hp_prime] at hs₁
    obtain ⟨s₂, _, hs₂⟩ := cfgExit_tf_succ q' p
    exact ⟨_, by omega, nSteps_bind_eq hs₁ hs₂⟩

open Classical in
theorem cfg0_partner_fail_zero (p : ℕ) (hp : 1 ≤ p) :
    ∃ s c, nSteps refM s (cfg0 true 0 p) = some c ∧ step refM c = none := by
  obtain ⟨s₁, _, hs₁⟩ := cfg0_eval true 0 p hp
  by_cases hp_prime : IsPrime p
  · rw [decide_eq_true hp_prime] at hs₁
    obtain ⟨s₂, _, hs₂⟩ := cfgExit_tt 0 p
    obtain ⟨s₃, _, hs₃⟩ := cfg0_eval false p 1 (by omega)
    rw [decide_eq_false not_isPrime_one] at hs₃
    obtain ⟨s₄, c, hs₄, hnone⟩ := cfgExit_ff_one p
    exact ⟨_, c, nSteps_bind_eq hs₁ (nSteps_bind_eq hs₂ (nSteps_bind_eq hs₃ hs₄)), hnone⟩
  · rw [decide_eq_false hp_prime] at hs₁
    obtain ⟨s₂, c, hs₂, hnone⟩ := cfgExit_tf_zero p
    exact ⟨_, c, nSteps_bind_eq hs₁ hs₂, hnone⟩

theorem search_advance (w q p : ℕ) (hp : 1 ≤ p) (hsum : q + p = 2 * w + 3)
    {q' : ℕ} (hq' : q' ≤ q) (hq1 : IsPrime (q' + 1)) (hp1 : IsPrime (2 * w + 3 - q')) :
    ∃ s, 1 ≤ s ∧ nSteps refM s (cfg0 true q p) = some (stageCfg (w + 1)) := by
  induction q generalizing p with
  | zero =>
    have hq'0 : q' = 0 := by omega
    subst hq'0
    exact absurd hq1 not_isPrime_one
  | succ q0 ih =>
    by_cases hcurr : IsPrime p ∧ IsPrime (q0 + 2)
    · exact cfg0_partner_pass w (q0 + 1) p hp hsum hcurr.1 hcurr.2
    · have hq'_le : q' ≤ q0 := by
        rcases Nat.eq_or_lt_of_le hq' with rfl | hlt
        · exfalso
          apply hcurr
          have hp_eq : p = 2 * w + 3 - (q0 + 1) := by omega
          rw [hp_eq]
          exact ⟨hp1, hq1⟩
        · omega
      obtain ⟨s₁, _, hs₁⟩ := cfg0_partner_fail_succ q0 p hp hcurr
      obtain ⟨s₂, _, hs₂⟩ := ih (p + 1) (by omega) (by omega) hq'_le
      exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

theorem search_halt (w q p : ℕ) (hp : 1 ≤ p) (hsum : q + p = 2 * w + 3)
    (hno : ∀ q' ≤ q, ¬ (IsPrime (q' + 1) ∧ IsPrime (2 * w + 3 - q'))) :
    ∃ s c, nSteps refM s (cfg0 true q p) = some c ∧ step refM c = none := by
  induction q generalizing p with
  | zero =>
    exact cfg0_partner_fail_zero p hp
  | succ q0 ih =>
    have hcurr : ¬ (IsPrime p ∧ IsPrime (q0 + 2)) := by
      intro ⟨hp_pr, hq_pr⟩
      have hp_eq : p = 2 * w + 3 - (q0 + 1) := by omega
      rw [hp_eq] at hp_pr
      exact hno (q0 + 1) (by omega) ⟨hq_pr, hp_pr⟩
    obtain ⟨s₁, _, hs₁⟩ := cfg0_partner_fail_succ q0 p hp hcurr
    obtain ⟨s₂, c, hs₂, hnone⟩ := ih (p + 1) (by omega) (by omega)
      (fun q' hq' => hno q' (by omega))
    exact ⟨s₁ + s₂, c, nSteps_bind_eq hs₁ hs₂, hnone⟩

theorem stage_advance (w : ℕ) (h : HasGoldbachPair (2 * w + 4)) :
    ∃ s, 1 ≤ s ∧ nSteps refM s (stageCfg w) = some (stageCfg (w + 1)) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  have ha2 : 2 ≤ a := ha.1
  have hb2 : 2 ≤ b := hb.1
  have hq' : a - 1 ≤ 2 * w + 2 := by omega
  have ha_eq : a - 1 + 1 = a := by omega
  have hb_eq : 2 * w + 3 - (a - 1) = b := by omega
  refine search_advance w (2 * w + 2) 1 (by omega) (by omega) hq' ?_ ?_
  · rwa [ha_eq]
  · rwa [hb_eq]

theorem stage_halt (w : ℕ) (h : ¬ HasGoldbachPair (2 * w + 4)) :
    ∃ s c, nSteps refM s (stageCfg w) = some c ∧ step refM c = none := by
  refine search_halt w (2 * w + 2) 1 (by omega) (by omega) ?_
  intro q' hq' ⟨hq1, hp1⟩
  exact h ⟨q' + 1, 2 * w + 3 - q', hq1, hp1, by omega⟩

theorem reaches_imp_nSteps {M : Machine 25 2} {a b : Cfg 25 2}
    (h : Reaches (step M) a b) : ∃ k, nSteps M k a = some b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, nSteps_bind_eq hk (step_one hstep)⟩

theorem nSteps_eq_none_of_step_none {M : Machine 25 2} {k : ℕ} (s : ℕ) {a b : Cfg 25 2}
    (hk : nSteps M k a = some b) (hnone : step M b = none) (hks : k < s) :
    nSteps M s a = none := by
  have hs : s = k + ((s - k - 1) + 1) := by omega
  rw [hs, nSteps_add, hk, Option.bind_some, nSteps_succ, hnone, Option.bind_none]

theorem stage_iter_all (hall : ∀ w, HasGoldbachPair (2 * w + 4)) (N : ℕ) :
    ∃ s, N ≤ s ∧ nSteps refM s (stageCfg 0) = some (stageCfg N) := by
  induction N with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ N ih =>
    obtain ⟨s₁, _, hs₁⟩ := ih
    obtain ⟨s₂, _, hs₂⟩ := stage_advance N (hall N)
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

theorem stage_reach_or_halt (w : ℕ) :
    (∃ s, nSteps refM s (stageCfg 0) = some (stageCfg w)) ∨
    (∃ s c, nSteps refM s (stageCfg 0) = some c ∧ step refM c = none) := by
  induction w with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ w ih =>
    rcases ih with ⟨s₁, hs₁⟩ | hhalt
    · by_cases hw : HasGoldbachPair (2 * w + 4)
      · obtain ⟨s₂, _, hs₂⟩ := stage_advance w hw
        exact Or.inl ⟨s₁ + s₂, nSteps_bind_eq hs₁ hs₂⟩
      · obtain ⟨s₂, c, hs₂, hnone⟩ := stage_halt w hw
        exact Or.inr ⟨s₁ + s₂, c, nSteps_bind_eq hs₁ hs₂, hnone⟩
    · exact Or.inr hhalt

theorem boot_chk0_ref :
    nSteps refM 49 init = some (stageCfg 0) := by
  have h47 : nSteps refM 47 init =
      some ⟨19, ⟨1, ListBlank.append (List.replicate 2 1) B0,
        (ListBlank.append (List.replicate 1 1) B0).cons 0⟩⟩ := boot_reference_47
  have h2 := sim_state19_to_0_ref
    (ListBlank.append (List.replicate 2 1) B0)
    (ListBlank.append (List.replicate 1 1) B0)
  unfold stageCfg cfg0
  simpa [LBase1, REnd1, B0_cons_zero] using nSteps_bind_eq h47 h2

theorem halts_reference_iff_exists_counterexample :
    Halts refM ↔ ∃ w : ℕ, ¬ HasGoldbachPair (2 * w + 4) := by
  unfold ConjectureMachines.Halts
  rw [nSteps_eval_dom boot_chk0_ref]
  constructor
  · intro hdom
    by_contra hall
    push Not at hall
    rw [Part.dom_iff_mem] at hdom
    obtain ⟨b, hb⟩ := hdom
    rw [StateTransition.mem_eval] at hb
    obtain ⟨hreach, hnone⟩ := hb
    obtain ⟨k, hk⟩ := reaches_imp_nSteps hreach
    obtain ⟨s, hks, hs⟩ := stage_iter_all hall (k + 1)
    have h_eq_none := nSteps_eq_none_of_step_none s hk hnone (by omega)
    rw [h_eq_none] at hs
    cases hs
  · rintro ⟨w, hw⟩
    have h_halt : ∃ s c, nSteps refM s (stageCfg 0) = some c ∧ step refM c = none := by
      rcases stage_reach_or_halt w with ⟨s₁, hs₁⟩ | hhalt
      · obtain ⟨s₂, c, hs₂, hnone⟩ := stage_halt w hw
        exact ⟨s₁ + s₂, c, nSteps_bind_eq hs₁ hs₂, hnone⟩
      · exact hhalt
    obtain ⟨s, c, hs, hnone⟩ := h_halt
    rw [Part.dom_iff_mem]
    exact ⟨c, StateTransition.mem_eval.mpr ⟨nSteps_reaches hs, hnone⟩⟩

/-!
## `edited` Semantics (`L`-First Goldbach Machine)
-/

/-- The left tape suffix for the intermediate machine search orientation. -/
def LBaseE : Bool → ℕ → ListBlank (Fin 2)
  | true, q => ListBlank.append (List.replicate (q + 1) 1) B0
  | false, _ => B0

/-- The right tape suffix for the intermediate machine search orientation. -/
def REndE : Bool → ℕ → ListBlank (Fin 2)
  | true, _ => B0
  | false, q => ListBlank.append (List.replicate (q + 1) 1) B0

/-- Intermediate primality-test entry with orientation and unary search parameters. -/
def cfg0E (is_right : Bool) (q p : ℕ) : Cfg 25 2 :=
  ⟨0, Tape.mk' ((LBaseE is_right q).cons 0)
    (ListBlank.append (List.replicate (p + 1) 1) ((REndE is_right q).cons 0))⟩

/-- Intermediate trial-division entry, with divisor `k + 2` and remainder parameter `r`. -/
def cfg6E (is_right : Bool) (q k r : ℕ) : Cfg 25 2 :=
  ⟨6, Tape.mk'
    ((ListBlank.append (List.replicate (k + 2) 1) ((LBaseE is_right q).cons 0)).cons 1)
    (ListBlank.append (List.replicate (r + 1) 1) ((REndE is_right q).cons 0))⟩

/-- Intermediate division-loop configuration with unary counter parameters. -/
def cfg11E (is_right : Bool) (q A B m r : ℕ) : Cfg 25 2 :=
  ⟨11, Tape.mk' (counterTape A B (LBaseE is_right q))
    ((ListBlank.append (List.replicate (m + 1) 1)
      ((ListBlank.append (List.replicate r 1) ((REndE is_right q).cons 0)).cons 0)).cons 1)⟩

/-- Intermediate primality-test exit, selecting the prime or composite continuation. -/
def cfgExitE (is_right is_prime : Bool) (q p : ℕ) : Cfg 25 2 :=
  if is_prime then
    ⟨6, Tape.mk'
      (ListBlank.append (List.replicate (p + 1) 1) ((LBaseE is_right q).cons 0))
      ((REndE is_right q).cons 0)⟩
  else
    ⟨16, Tape.mkL ((LBaseE is_right q).cons 0)
      (ListBlank.append (List.replicate (p + 1) 1) ((REndE is_right q).cons 0))⟩

theorem cfg11E_step_b0 (is_right : Bool) (q A m r' : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps edited s (cfg11E is_right q A 0 m (r' + 1)) =
        some (cfg11E is_right q 0 A (m + 1) r') := by
  have h_rep : ListBlank.append (List.replicate (r' + 1) 1) ((REndE is_right q).cons 0) =
      (ListBlank.append (List.replicate r' 1) ((REndE is_right q).cons 0)).cons 1 := rfl
  unfold cfg11E
  rw [h_rep]
  have h := nSteps_pass_11_b0 (M := edited) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    A (m + 1) (LBaseE is_right q)
    (ListBlank.append (List.replicate r' 1) ((REndE is_right q).cons 0))
  exact ⟨_, by omega, h⟩

theorem cfg11E_step_bsucc (is_right : Bool) (q A b m r' : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps edited s (cfg11E is_right q A (b + 1) m (r' + 1)) =
        some (cfg11E is_right q (A + 1) b (m + 1) r') := by
  have h_rep : ListBlank.append (List.replicate (r' + 1) 1) ((REndE is_right q).cons 0) =
      (ListBlank.append (List.replicate r' 1) ((REndE is_right q).cons 0)).cons 1 := rfl
  unfold cfg11E
  rw [h_rep]
  have h := nSteps_pass_11_bsucc (M := edited) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    A b (m + 1) (LBaseE is_right q)
    (ListBlank.append (List.replicate r' 1) ((REndE is_right q).cons 0))
  exact ⟨_, by omega, h⟩

theorem cfg11E_drain (is_right : Bool) (q k r A B m : ℕ)
    (hAB : A + B = k + 1) (hdvd : (k + 2) ∣ B + m + 2) :
    ∃ A' B', A' + B' = k + 1 ∧ (k + 2) ∣ B' + (m + r) + 2 ∧
      ∃ s, nSteps edited s (cfg11E is_right q A B m r) =
        some (cfg11E is_right q A' B' (m + r) 0) := by
  induction r generalizing A B m with
  | zero =>
    exact ⟨A, B, hAB, by simpa using hdvd, 0, rfl⟩
  | succ r' ih =>
    cases B with
    | zero =>
      obtain ⟨s₁, _, hs₁⟩ := cfg11E_step_b0 is_right q A m r'
      have hdvd' : (k + 2) ∣ A + (m + 1) + 2 := by
        have h_eq : A + (m + 1) + 2 = (0 + m + 2) + (k + 2) := by omega
        rw [h_eq]
        exact Nat.dvd_add_self_right.mpr hdvd
      obtain ⟨A', B', hAB', hdvd'', s₂, hs₂⟩ := ih 0 A (m + 1) (by omega) hdvd'
      have h_mr : m + 1 + r' = m + (r' + 1) := by omega
      rw [h_mr] at hdvd'' hs₂
      exact ⟨A', B', hAB', hdvd'', s₁ + s₂, nSteps_bind_eq hs₁ hs₂⟩
    | succ b =>
      obtain ⟨s₁, _, hs₁⟩ := cfg11E_step_bsucc is_right q A b m r'
      have hdvd' : (k + 2) ∣ b + (m + 1) + 2 := by
        have h_eq : b + (m + 1) + 2 = b + 1 + m + 2 := by omega
        rwa [h_eq]
      obtain ⟨A', B', hAB', hdvd'', s₂, hs₂⟩ := ih (A + 1) b (m + 1) (by omega) hdvd'
      have h_mr : m + 1 + r' = m + (r' + 1) := by omega
      rw [h_mr] at hdvd'' hs₂
      exact ⟨A', B', hAB', hdvd'', s₁ + s₂, nSteps_bind_eq hs₁ hs₂⟩

theorem cfg6E_step_enter (is_right : Bool) (q k r' : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps edited s (cfg6E is_right q k (r' + 1)) =
        some (cfg11E is_right q 1 k 0 r') := by
  have h_rep : ListBlank.append (List.replicate (r' + 1 + 1) 1) ((REndE is_right q).cons 0) =
      ((ListBlank.append (List.replicate r' 1) ((REndE is_right q).cons 0)).cons 1).cons 1 := rfl
  unfold cfg6E cfg11E
  rw [h_rep]
  have h1 := sim_state6_d_edit k (LBaseE is_right q)
    (ListBlank.append (List.replicate r' 1) ((REndE is_right q).cons 0))
  have h0_to_11 (L_b R_m : ListBlank (Fin 2)) :
      nSteps edited (1 + k)
        ⟨0, Tape.mk' ((L_b.cons 0).cons 1)
          (ListBlank.append (0 :: (List.replicate k 0 ++ [1])) R_m)⟩ =
        some ⟨11, Tape.mk' (counterTape 1 k L_b) (R_m.cons 1)⟩ := by
    rw [ListBlank.append, ListBlank.append_assoc, ListBlank.append, ListBlank.append]
    refine nSteps_bind_eq (step_one
      (step_mk'_right (M := edited) (q := 0) (q' := 11) (a := 0) (b := 0) rfl _ _)) ?_
    exact nSteps_mk'_right_scan (M := edited) (q := 11) (a := 0) (b := 1) rfl k _ _
  have h := nSteps_bind_eq h1 (h0_to_11 (LBaseE is_right q) _)
  exact ⟨_, by omega, h⟩

theorem cfg6E_pass_succ_dvd (is_right : Bool) (q k r' : ℕ)
    (hdvd : (k + 2) ∣ (k + 4 + r')) :
    ∃ s, 1 ≤ s ∧
      nSteps edited s (cfg6E is_right q k (r' + 1)) =
        some (cfgExitE is_right false q (k + 4 + r')) := by
  obtain ⟨s₀, _, hs₀⟩ := cfg6E_step_enter is_right q k r'
  obtain ⟨A', B', hAB', hdvd', s₁, hs₁⟩ :=
    cfg11E_drain is_right q k r' 1 k 0 (by omega) (by simp)
  simp only [Nat.zero_add] at hdvd' hs₁
  have hB0 : B' = 0 := by
    have h_eq1 : k + 4 + r' = (r' + 2) + (k + 2) := by omega
    have h_eq2 : B' + r' + 2 = B' + (r' + 2) := by omega
    rw [h_eq1, Nat.dvd_add_self_right] at hdvd
    rw [h_eq2] at hdvd'
    exact Nat.eq_zero_of_dvd_of_lt ((Nat.dvd_add_iff_left hdvd).mpr hdvd') (by omega)
  subst hB0
  have h_fin := nSteps_pass_11_to_16_edit A' (r' + 1) (LBaseE is_right q) (REndE is_right q)
  have h_p : A' + (r' + 1) + 3 = (k + 4 + r') + 1 := by omega
  have h_fin' : nSteps edited ((1 + (r' + 1 + 1)) + ((1 + ((r' + 1 + 1) + 1)) + (1 + A')))
      (cfg11E is_right q A' 0 r' 0) = some (cfgExitE is_right false q (k + 4 + r')) := by
    unfold cfg11E cfgExitE
    simpa [List.replicate_zero, ListBlank.append, h_p] using h_fin
  exact ⟨_, by omega, nSteps_bind_eq hs₀ (nSteps_bind_eq hs₁ h_fin')⟩

theorem cfg6E_pass_succ_not_dvd (is_right : Bool) (q k r' : ℕ)
    (hdvd : ¬ (k + 2) ∣ (k + 4 + r')) :
    ∃ s, 1 ≤ s ∧
      nSteps edited s (cfg6E is_right q k (r' + 1)) =
        some (cfg6E is_right q (k + 1) r') := by
  obtain ⟨s₀, _, hs₀⟩ := cfg6E_step_enter is_right q k r'
  obtain ⟨A', B', hAB', hdvd', s₁, hs₁⟩ :=
    cfg11E_drain is_right q k r' 1 k 0 (by omega) (by simp)
  simp only [Nat.zero_add] at hdvd' hs₁
  cases B' with
  | zero =>
    exfalso
    apply hdvd
    have h_eq1 : k + 4 + r' = (r' + 2) + (k + 2) := by omega
    rw [h_eq1, Nat.dvd_add_self_right]
    simpa using hdvd'
  | succ b =>
    have h_fin := nSteps_pass_11_to_6_edit A' b (r' + 1) (LBaseE is_right q) (REndE is_right q)
    have h_k : A' + b + 3 = (k + 1) + 2 := by omega
    have h_fin' :
        nSteps edited ((1 + (r' + 1 + 1)) + ((1 + ((r' + 1 + 1) + 1)) + (1 + (b + (1 + (b + 3))))))
          (cfg11E is_right q A' (b + 1) r' 0) = some (cfg6E is_right q (k + 1) r') := by
      unfold cfg11E cfg6E
      simpa [List.replicate_zero, ListBlank.append, h_k] using h_fin
    exact ⟨_, by omega, nSteps_bind_eq hs₀ (nSteps_bind_eq hs₁ h_fin')⟩

open Classical in
theorem cfg6E_eval (is_right : Bool) (q k r : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps edited s (cfg6E is_right q k r) =
        some (cfgExitE is_right (decide (NoFactorFrom k (k + 3 + r))) q (k + 3 + r)) := by
  induction r generalizing k with
  | zero =>
    have h_nf : NoFactorFrom k (k + 3 + 0) := by
      intro d hd1 hd2 hdvd
      have hd_eq : d = k + 2 := by omega
      subst hd_eq
      have h1 : (k + 2) ∣ 1 := by
        have h_add : (k + 2) ∣ (k + 2) + 1 := hdvd
        exact (Nat.dvd_add_right (Nat.dvd_refl (k + 2))).mp h_add
      have := Nat.le_of_dvd (by omega) h1
      omega
    rw [decide_eq_true h_nf]
    have h1 := sim_state6_accept_edit k (LBaseE is_right q) (REndE is_right q)
    have h_cnt :
        ((ListBlank.append (List.replicate (k + 2) 1) ((LBaseE is_right q).cons 0)).cons 1).cons 1 =
        ListBlank.append (List.replicate (k + 3 + 1) 1) ((LBaseE is_right q).cons 0) := rfl
    refine ⟨2 + ((k + 2) + (2 + ((k + 1) + (6 + (k + (1 + (k + 3))))))), by omega, ?_⟩
    unfold cfg6E cfgExitE
    simpa [Nat.add_zero, List.replicate_zero, ListBlank.append, h_cnt] using h1
  | succ r' ih =>
    have h_arith : k + 3 + (r' + 1) = k + 4 + r' := by omega
    rw [h_arith]
    by_cases hdvd : (k + 2) ∣ (k + 4 + r')
    · have h_nf : ¬ NoFactorFrom k (k + 4 + r') := fun h => h (k + 2) (by omega) (by omega) hdvd
      rw [decide_eq_false h_nf]
      exact cfg6E_pass_succ_dvd is_right q k r' hdvd
    · obtain ⟨s₁, _, hs₁⟩ := cfg6E_pass_succ_not_dvd is_right q k r' hdvd
      obtain ⟨s₂, _, hs₂⟩ := ih (k + 1)
      have h_arith2 : k + 1 + 3 + r' = k + 4 + r' := by omega
      rw [h_arith2] at hs₂
      have h_iff : NoFactorFrom k (k + 4 + r') ↔ NoFactorFrom (k + 1) (k + 4 + r') := by
        constructor
        · intro h d hd1 hd2
          exact h d (by omega) hd2
        · intro h d hd1 hd2
          rcases Nat.eq_or_lt_of_le hd1 with rfl | hd_gt
          · exact hdvd
          · exact h d (by omega) hd2
      have h_dec : decide (NoFactorFrom k (k + 4 + r')) =
          decide (NoFactorFrom (k + 1) (k + 4 + r')) := by
        simp [h_iff]
      rw [h_dec]
      exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

open Classical in
theorem cfg0E_eval (is_right : Bool) (q p : ℕ) (hp : 1 ≤ p) :
    ∃ s, 1 ≤ s ∧
      nSteps edited s (cfg0E is_right q p) =
        some (cfgExitE is_right (decide (IsPrime p)) q p) := by
  rcases Nat.eq_or_lt_of_le hp with rfl | hp2
  · rw [decide_eq_false not_isPrime_one]
    obtain ⟨_, h2⟩ := sim_state0_p1 B0 ((LBaseE is_right q).cons 0) B0 (REndE is_right q)
    refine ⟨3 + 2, by omega, ?_⟩
    unfold cfg0E cfgExitE
    exact nSteps_bind_eq h2 (step_nSteps
      (step_mkL_left (M := edited) (q := 16) (q' := 16) (a := 1) (b := 1) rfl _ _)
      (step_one (step_mkL_left (M := edited) (q := 16) (q' := 16) (a := 1) (b := 1) rfl _ _)))
  · rcases Nat.eq_or_lt_of_le hp2 with rfl | hp3
    · rw [decide_eq_true isPrime_two]
      have h2 := sim_state0_p2_edit ((LBaseE is_right q).cons 0) (REndE is_right q)
      refine ⟨3, by omega, ?_⟩
      unfold cfg0E cfgExitE
      exact h2
    · obtain ⟨r0, rfl⟩ : ∃ r0, p = r0 + 3 := ⟨p - 3, by omega⟩
      obtain ⟨_, h2⟩ := sim_state0_p_ge3 B0 ((LBaseE is_right q).cons 0) B0
        (ListBlank.append (List.replicate r0 1) ((REndE is_right q).cons 0))
      have h_enter : nSteps edited 3 (cfg0E is_right q (r0 + 3)) =
          some (cfg6E is_right q 0 r0) := h2
      obtain ⟨s₂, _, hs₂⟩ := cfg6E_eval is_right q 0 r0
      have h_prime_iff : IsPrime (r0 + 3) ↔ NoFactorFrom 0 (0 + 3 + r0) := by
        unfold IsPrime
        have h_eq : 0 + 3 + r0 = r0 + 3 := by omega
        rw [h_eq]
        exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      have h_dec : decide (IsPrime (r0 + 3)) = decide (NoFactorFrom 0 (0 + 3 + r0)) := by
        simp [h_prime_iff]
      have h_eq : 0 + 3 + r0 = r0 + 3 := by omega
      rw [h_dec]
      rw [h_eq] at hs₂ ⊢
      exact ⟨3 + s₂, by omega, nSteps_bind_eq h_enter hs₂⟩

theorem cfgExitE_ft (q p : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps edited s (cfgExitE false true q p) =
        some (cfg0E true p q) := by
  have h : nSteps edited 3 (cfgExitE false true q p) = some (cfg0E true p q) := by
    unfold cfgExitE cfg0E LBaseE REndE
    simp only [↓reduceIte, B0_cons_zero]
    rw [List.replicate_succ, ListBlank.append]
    refine step_nSteps (step_mk'_right (b := 0) (q' := 7) rfl _ _) ?_
    refine step_nSteps (step_mk'_left (b := 1) (q' := 22) rfl _ _) ?_
    exact step_one (step_mkL_right (b := 0) (q' := 0) rfl _ _)
  exact ⟨3, by omega, h⟩

theorem nSteps_state18_to_0_edit (k : ℕ) (L_base R_p2 : ListBlank (Fin 2)) :
    nSteps edited (1 + ((k + 1) + 1))
      ⟨18, Tape.mkL ((ListBlank.append (List.replicate (k + 1) 1) (L_base.cons 0)).cons 1) R_p2⟩ =
      some ⟨0, Tape.mk' (L_base.cons 0)
        (ListBlank.append (List.replicate (k + 1) 1) (R_p2.cons 0))⟩ := by
  refine nSteps_bind_eq (step_one (step_mkL_left (b := 0) (q' := 19) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 19) (a := 1) (b := 1) rfl (k + 1) _ _) ?_
  exact step_one (step_mkL_right (b := 0) (q' := 0) rfl _ _)

theorem cfgExitE_tf_succ (p0 q : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps edited s (cfgExitE true false (p0 + 1) q) =
        some (cfg0E false (q + 1) p0) := by
  have h1 : step edited (cfgExitE true false (p0 + 1) q) =
      some ⟨18, Tape.mkL
        ((ListBlank.append (List.replicate (p0 + 1) 1) (B0.cons 0)).cons 1)
        (ListBlank.append (List.replicate (q + 2) 1) B0)⟩ := by
    unfold cfgExitE LBaseE REndE
    simp only [Bool.false_eq_true, ↓reduceIte, B0_cons_zero]
    rw [List.replicate_succ, ListBlank.append]
    exact step_mkL_left (M := edited) (q := 16) (q' := 18) (a := 0) (b := 1) rfl _ _
  have h2 := nSteps_state18_to_0_edit p0 B0 (ListBlank.append (List.replicate (q + 2) 1) B0)
  have h : nSteps edited (1 + (1 + ((p0 + 1) + 1))) (cfgExitE true false (p0 + 1) q) =
      some (cfg0E false (q + 1) p0) := by
    unfold cfg0E LBaseE REndE
    simpa [B0_cons_zero] using nSteps_bind_eq (step_one h1) h2
  exact ⟨_, by omega, h⟩

theorem nSteps_state16_left_split_edit (k : ℕ) (L_blank R_end : ListBlank (Fin 2)) :
    nSteps edited ((3 + ((k + 2) + 1)) + (1 + ((k + 1) + 1)))
      ⟨16, Tape.mkL ((L_blank.cons 0).cons 0)
        (ListBlank.append (List.replicate (k + 2) 1) (R_end.cons 0))⟩ =
      some ⟨0, Tape.mk' ((L_blank.cons 0).cons 0)
        (ListBlank.append (List.replicate (k + 1) 1) ((R_end.cons 1).cons 0))⟩ := by
  have h_pre : nSteps edited (3 + ((k + 2) + 1))
      ⟨16, Tape.mkL ((L_blank.cons 0).cons 0)
        (ListBlank.append (List.replicate (k + 2) 1) (R_end.cons 0))⟩ =
      some ⟨18, Tape.mkL
        ((ListBlank.append (List.replicate (k + 1) 1) ((L_blank.cons 0).cons 0)).cons 1)
        (R_end.cons 1)⟩ := by
    refine nSteps_bind_eq
      (step_nSteps (step_mkL_left (b := 1) (q' := 18) rfl _ _)
        (step_nSteps (step_mkL_right (b := 0) (q' := 2) rfl _ _)
          (step_one (step_mk'_right (b := 0) (q' := 5) rfl _ _)))) ?_
    refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 5) (a := 1) (b := 1) rfl (k + 2) _ _) ?_
    rw [List.replicate_succ, ListBlank.append]
    exact step_one (step_mk'_left (b := 1) (q' := 18) rfl _ _)
  exact nSteps_bind_eq h_pre (nSteps_state18_to_0_edit k (L_blank.cons 0) (R_end.cons 1))

theorem cfgExitE_ff (q p0 : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps edited s (cfgExitE false false q (p0 + 1)) =
        some (cfg0E false (q + 1) p0) := by
  have h := nSteps_state16_left_split_edit p0 B0
    (ListBlank.append (List.replicate (q + 1) 1) B0)
  have h' : nSteps edited ((3 + ((p0 + 2) + 1)) + (1 + ((p0 + 1) + 1)))
      (cfgExitE false false q (p0 + 1)) = some (cfg0E false (q + 1) p0) := by
    unfold cfgExitE cfg0E LBaseE REndE
    simpa [B0_cons_zero, List.replicate_succ, ListBlank.append] using h
  exact ⟨_, by omega, h'⟩

theorem cfg0E_halt_zero (q : ℕ) :
    ∃ s c, nSteps edited s (cfg0E false q 0) = some c ∧ step edited c = none := by
  have h1 : nSteps edited 1 (cfg0E false q 0) =
      some ⟨3, Tape.mk' ((B0.cons 0).cons 1) ((REndE false q).cons 0)⟩ := by
    unfold cfg0E LBaseE
    simp only [List.replicate_succ, List.replicate_zero, ListBlank.append]
    exact step_one (step_mk'_right (M := edited) (q := 0) (q' := 3) (a := 1) (b := 1) rfl _ _)
  have hnone : step edited ⟨3, Tape.mk' ((B0.cons 0).cons 1) ((REndE false q).cons 0)⟩ = none := by
    simp [step, Tape.mk']; rfl
  exact ⟨1, _, h1, hnone⟩

theorem nSteps_state6_merge_to_16_edit (p q0 : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    nSteps edited ((4 + ((q0 + 1) + (1 + ((q0 + 1) + 3)))) + (p + q0 + 5))
      ⟨6, Tape.mk'
        (ListBlank.append (List.replicate (q0 + 2) 1)
          ((ListBlank.append (List.replicate (p + 1) 1) (L_base.cons 0)).cons 0))
        ((R_end.cons 0).cons 0)⟩ =
      some ⟨16, Tape.mkL (L_base.cons 0)
        (ListBlank.append (List.replicate (p + q0 + 5) 1) (R_end.cons 0))⟩ := by
  have h_pre : nSteps edited (4 + ((q0 + 1) + (1 + ((q0 + 1) + 3))))
      ⟨6, Tape.mk'
        (ListBlank.append (List.replicate (q0 + 2) 1)
          ((ListBlank.append (List.replicate (p + 1) 1) (L_base.cons 0)).cons 0))
        ((R_end.cons 0).cons 0)⟩ =
      some ⟨16, Tape.mkL
        (ListBlank.append (List.replicate (p + q0 + 5) 1) (L_base.cons 0))
        (R_end.cons 0)⟩ := by
    rw [List.replicate_succ, ListBlank.append]
    refine nSteps_bind_eq
      (step_nSteps (step_mk'_right (b := 0) (q' := 7) rfl _ _)
        (step_nSteps (step_mk'_left (b := 0) (q' := 14) rfl _ _)
          (step_nSteps (step_mkL_left (b := 1) (q' := 15) rfl _ _)
            (step_one (step_mkL_left (b := 0) (q' := 23) rfl _ _))))) ?_
    refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 23) (a := 1) (b := 1) rfl (q0 + 1) _ _) ?_
    refine nSteps_bind_eq (step_one (step_mkL_right (b := 1) (q' := 24) rfl _ _)) ?_
    refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 24) (a := 1) (b := 1) rfl (q0 + 1) _ _) ?_
    refine step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl _ _) ?_
    refine step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl _ _) ?_
    apply step_one
    have h_cnt :
        ((ListBlank.append (List.replicate (q0 + 1) 1)
          ((ListBlank.append (List.replicate (p + 1) 1) (L_base.cons 0)).cons 1)).cons 1).cons 1 =
        ListBlank.append (List.replicate (p + q0 + 5) 1) (L_base.cons 0) := by
      rw [append_replicate_cons, append_replicate_add]
      have h_eq : p + q0 + 5 = ((q0 + 1 + 1 + (p + 1)) + 1) + 1 := by omega
      rw [h_eq, List.replicate_succ, List.replicate_succ, ListBlank.append, ListBlank.append]
    simpa [h_cnt] using
      step_mk'_left (M := edited) (q := 4) (q' := 16) (a := 0) (b := 0) rfl
        (ListBlank.append (List.replicate (p + q0 + 5) 1) (L_base.cons 0)) R_end
  exact nSteps_bind_eq h_pre
    (nSteps_mkL_left_scan (M := edited) (q := 16) (a := 1) (b := 1) rfl (p + q0 + 5) _ _)

theorem cfgExitE_tt (w p q0 : ℕ) (hsum : p + (q0 + 1) = 2 * w + 4) :
    ∃ s, 1 ≤ s ∧
      nSteps edited s (cfgExitE true true p (q0 + 1)) =
        some (cfg0E false 0 (2 * w + 6)) := by
  have h1 := nSteps_state6_merge_to_16_edit p q0 B0 B0
  have h_len : p + q0 + 5 = (2 * w + 6) + 2 := by omega
  rw [h_len] at h1
  have h2 := nSteps_state16_left_split_edit (2 * w + 6) B0 B0
  simp only [B0_cons_zero] at h1 h2
  have h : nSteps edited
      (((4 + ((q0 + 1) + (1 + ((q0 + 1) + 3)))) + ((2 * w + 6) + 2)) +
        ((3 + ((2 * w + 6 + 2) + 1)) + (1 + ((2 * w + 6 + 1) + 1))))
      (cfgExitE true true p (q0 + 1)) = some (cfg0E false 0 (2 * w + 6)) := by
    unfold cfgExitE cfg0E LBaseE REndE
    simpa [B0_cons_zero, List.replicate_succ, ListBlank.append] using nSteps_bind_eq h1 h2
  exact ⟨_, by omega, h⟩

/-- Intermediate search entry for the even number `2 * w + 4`. -/
def stageCfgE (w : ℕ) : Cfg 25 2 :=
  cfg0E false 2 (2 * w + 2)

open Classical in
theorem cfg0E_partner_fail_succ (q p0 : ℕ) (hq : 1 ≤ q)
    (hfail : ¬ (IsPrime (p0 + 2) ∧ IsPrime q)) :
    ∃ s, 1 ≤ s ∧
      nSteps edited s (cfg0E false q (p0 + 2)) = some (cfg0E false (q + 1) (p0 + 1)) := by
  obtain ⟨s₁, _, hs₁⟩ := cfg0E_eval false q (p0 + 2) (by omega)
  by_cases hp_prime : IsPrime (p0 + 2)
  · have hq_not_prime : ¬ IsPrime q := fun hq_pr => hfail ⟨hp_prime, hq_pr⟩
    rw [decide_eq_true hp_prime] at hs₁
    obtain ⟨s₂, _, hs₂⟩ := cfgExitE_ft q (p0 + 2)
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    obtain ⟨s₃, _, hs₃⟩ := cfg0E_eval true (p0 + 2) (q' + 1) (by omega)
    rw [decide_eq_false hq_not_prime] at hs₃
    obtain ⟨s₄, _, hs₄⟩ := cfgExitE_tf_succ (p0 + 1) (q' + 1)
    exact ⟨_, by omega, nSteps_bind_eq hs₁ (nSteps_bind_eq hs₂ (nSteps_bind_eq hs₃ hs₄))⟩
  · rw [decide_eq_false hp_prime] at hs₁
    obtain ⟨s₂, _, hs₂⟩ := cfgExitE_ff q (p0 + 1)
    exact ⟨_, by omega, nSteps_bind_eq hs₁ hs₂⟩

open Classical in
theorem cfg0E_partner_pass (w q0 p : ℕ) (hp : 1 ≤ p) (hsum : p + (q0 + 1) = 2 * w + 4)
    (hp_prime : IsPrime p) (hq_prime : IsPrime (q0 + 1)) :
    ∃ s, 1 ≤ s ∧ nSteps edited s (cfg0E false (q0 + 1) p) = some (stageCfgE (w + 1)) := by
  obtain ⟨s₁, _, hs₁⟩ := cfg0E_eval false (q0 + 1) p hp
  rw [decide_eq_true hp_prime] at hs₁
  obtain ⟨s₂, _, hs₂⟩ := cfgExitE_ft (q0 + 1) p
  obtain ⟨s₃, _, hs₃⟩ := cfg0E_eval true p (q0 + 1) (by omega)
  rw [decide_eq_true hq_prime] at hs₃
  obtain ⟨s₄, _, hs₄⟩ := cfgExitE_tt w p q0 hsum
  obtain ⟨s₅, _, hs₅⟩ := cfg0E_eval false 0 (2 * w + 6) (by omega)
  have h_not_prime : ¬ IsPrime (2 * w + 6) := by
    intro ⟨_, hnf⟩
    exact hnf 2 (by omega) (by omega) ⟨w + 3, by omega⟩
  rw [decide_eq_false h_not_prime] at hs₅
  obtain ⟨s₆, _, hs₆⟩ := cfgExitE_ff 0 (2 * w + 5)
  obtain ⟨s₇, _, hs₇⟩ := cfg0E_partner_fail_succ 1 (2 * w + 3) (by omega)
    (fun ⟨_, h1⟩ => not_isPrime_one h1)
  have h_target : cfg0E false (1 + 1) (2 * w + 3 + 1) = stageCfgE (w + 1) := by
    unfold stageCfgE
    congr 1
  rw [h_target] at hs₇
  exact ⟨_, by omega,
    nSteps_bind_eq hs₁ (nSteps_bind_eq hs₂ (nSteps_bind_eq hs₃
      (nSteps_bind_eq hs₄ (nSteps_bind_eq hs₅ (nSteps_bind_eq hs₆ hs₇)))))⟩

open Classical in
theorem cfg0E_partner_fail_one (q : ℕ) :
    ∃ s c, nSteps edited s (cfg0E false q 1) = some c ∧ step edited c = none := by
  obtain ⟨s₁, _, hs₁⟩ := cfg0E_eval false q 1 (by omega)
  rw [decide_eq_false not_isPrime_one] at hs₁
  obtain ⟨s₂, _, hs₂⟩ := cfgExitE_ff q 0
  obtain ⟨s₃, c, hs₃, hnone⟩ := cfg0E_halt_zero (q + 1)
  exact ⟨_, c, nSteps_bind_eq hs₁ (nSteps_bind_eq hs₂ hs₃), hnone⟩

theorem searchE_advance (w q p0 : ℕ) (hq : 1 ≤ q) (hsum : q + (p0 + 1) = 2 * w + 4)
    {p' : ℕ} (hp' : p' ≤ p0) (hp1 : IsPrime (p' + 1)) (hq1 : IsPrime (2 * w + 4 - (p' + 1))) :
    ∃ s, 1 ≤ s ∧ nSteps edited s (cfg0E false q (p0 + 1)) = some (stageCfgE (w + 1)) := by
  induction p0 generalizing q with
  | zero =>
    have hp'0 : p' = 0 := by omega
    subst hp'0
    exact absurd hp1 not_isPrime_one
  | succ p1 ih =>
    by_cases hcurr : IsPrime (p1 + 2) ∧ IsPrime q
    · obtain ⟨q0, rfl⟩ : ∃ q0, q = q0 + 1 := ⟨q - 1, by omega⟩
      exact cfg0E_partner_pass w q0 (p1 + 2) (by omega) (by omega) hcurr.1 hcurr.2
    · have hp'_le : p' ≤ p1 := by
        rcases Nat.eq_or_lt_of_le hp' with rfl | hlt
        · exfalso
          apply hcurr
          have hq_eq : q = 2 * w + 4 - (p1 + 2) := by omega
          rw [hq_eq]
          exact ⟨hp1, hq1⟩
        · omega
      obtain ⟨s₁, _, hs₁⟩ := cfg0E_partner_fail_succ q p1 hq hcurr
      obtain ⟨s₂, _, hs₂⟩ := ih (q + 1) (by omega) (by omega) hp'_le
      exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

theorem searchE_halt (w q p0 : ℕ) (hq : 1 ≤ q) (hsum : q + (p0 + 1) = 2 * w + 4)
    (hno : ∀ p' ≤ p0, ¬ (IsPrime (p' + 1) ∧ IsPrime (2 * w + 4 - (p' + 1)))) :
    ∃ s c, nSteps edited s (cfg0E false q (p0 + 1)) = some c ∧ step edited c = none := by
  induction p0 generalizing q with
  | zero =>
    exact cfg0E_partner_fail_one q
  | succ p1 ih =>
    have hcurr : ¬ (IsPrime (p1 + 2) ∧ IsPrime q) := by
      intro ⟨hp_pr, hq_pr⟩
      have hq_eq : q = 2 * w + 4 - (p1 + 2) := by omega
      rw [hq_eq] at hq_pr
      exact hno (p1 + 1) (by omega) ⟨hp_pr, hq_pr⟩
    obtain ⟨s₁, _, hs₁⟩ := cfg0E_partner_fail_succ q p1 hq hcurr
    obtain ⟨s₂, c, hs₂, hnone⟩ := ih (q + 1) (by omega) (by omega)
      (fun p' hp' => hno p' (by omega))
    exact ⟨s₁ + s₂, c, nSteps_bind_eq hs₁ hs₂, hnone⟩

theorem stageE_advance (w : ℕ) (h : HasGoldbachPair (2 * w + 4)) :
    ∃ s, 1 ≤ s ∧ nSteps edited s (stageCfgE w) = some (stageCfgE (w + 1)) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  have ha2 : 2 ≤ a := ha.1
  have hb2 : 2 ≤ b := hb.1
  have hp' : b - 1 ≤ 2 * w + 1 := by omega
  have hb_eq : b - 1 + 1 = b := by omega
  have ha_eq : 2 * w + 4 - (b - 1 + 1) = a := by omega
  refine searchE_advance w 2 (2 * w + 1) (by omega) (by omega) hp' ?_ ?_
  · rwa [hb_eq]
  · rwa [ha_eq]

theorem stageE_halt (w : ℕ) (h : ¬ HasGoldbachPair (2 * w + 4)) :
    ∃ s c, nSteps edited s (stageCfgE w) = some c ∧ step edited c = none := by
  refine searchE_halt w 2 (2 * w + 1) (by omega) (by omega) ?_
  intro p' hp' ⟨hp1, hq1⟩
  exact h ⟨2 * w + 4 - (p' + 1), p' + 1, hq1, hp1, by omega⟩

theorem stageE_iter_all (hall : ∀ w, HasGoldbachPair (2 * w + 4)) (N : ℕ) :
    ∃ s, N ≤ s ∧ nSteps edited s (stageCfgE 0) = some (stageCfgE N) := by
  induction N with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ N ih =>
    obtain ⟨s₁, _, hs₁⟩ := ih
    obtain ⟨s₂, _, hs₂⟩ := stageE_advance N (hall N)
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

theorem stageE_reach_or_halt (w : ℕ) :
    (∃ s, nSteps edited s (stageCfgE 0) = some (stageCfgE w)) ∨
    (∃ s c, nSteps edited s (stageCfgE 0) = some c ∧ step edited c = none) := by
  induction w with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ w ih =>
    rcases ih with ⟨s₁, hs₁⟩ | hhalt
    · by_cases hw : HasGoldbachPair (2 * w + 4)
      · obtain ⟨s₂, _, hs₂⟩ := stageE_advance w hw
        exact Or.inl ⟨s₁ + s₂, nSteps_bind_eq hs₁ hs₂⟩
      · obtain ⟨s₂, c, hs₂, hnone⟩ := stageE_halt w hw
        exact Or.inr ⟨s₁ + s₂, c, nSteps_bind_eq hs₁ hs₂, hnone⟩
    · exact Or.inr hhalt

theorem boot_chk0_edit :
    nSteps edited 125 ⟨2, default⟩ = some (stageCfgE 0) := by
  rw [boot_edited_125]
  simp only [stageCfgE, cfg0E, LBaseE, REndE, B0_cons_zero, List.replicate_succ,
    List.replicate_zero, ListBlank.append]
  rfl

theorem halts_edited_iff_exists_counterexample :
    (eval (step edited) ⟨2, default⟩).Dom ↔ ∃ w : ℕ, ¬ HasGoldbachPair (2 * w + 4) := by
  rw [nSteps_eval_dom boot_chk0_edit]
  constructor
  · intro hdom
    by_contra hall
    push Not at hall
    rw [Part.dom_iff_mem] at hdom
    obtain ⟨b, hb⟩ := hdom
    rw [StateTransition.mem_eval] at hb
    obtain ⟨hreach, hnone⟩ := hb
    obtain ⟨k, hk⟩ := reaches_imp_nSteps hreach
    obtain ⟨s, hks, hs⟩ := stageE_iter_all hall (k + 1)
    have h_eq_none := nSteps_eq_none_of_step_none s hk hnone (by omega)
    rw [h_eq_none] at hs
    cases hs
  · rintro ⟨w, hw⟩
    have h_halt : ∃ s c, nSteps edited s (stageCfgE 0) = some c ∧ step edited c = none := by
      rcases stageE_reach_or_halt w with ⟨s₁, hs₁⟩ | hhalt
      · obtain ⟨s₂, c, hs₂, hnone⟩ := stageE_halt w hw
        exact ⟨s₁ + s₂, c, nSteps_bind_eq hs₁ hs₂, hnone⟩
      · exact hhalt
    obtain ⟨s, c, hs, hnone⟩ := h_halt
    rw [Part.dom_iff_mem]
    exact ⟨c, StateTransition.mem_eval.mpr ⟨nSteps_reaches hs, hnone⟩⟩

theorem candidate_equivalent : Halts candidate ↔ Halts reference :=
  candidate_iff_edited.trans
    (halts_edited_iff_exists_counterexample.trans
      halts_reference_iff_exists_counterexample.symm)

end ConjectureMachines.Goldbach21
