/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maxence Faldor, Moritz Firsching
-/
module

public import LeanPool.CryptidsGoldbach.Machines

/-! # Binary tape scans and finite execution

The shared definitions and lemmas retain their original `Goldbach21` names.
-/

@[expose] public section

namespace ConjectureMachines.Goldbach21

open Turing StateTransition

variable {states : ℕ}

/-- Execute exactly `n` transitions, returning `none` if a transition halts early. -/
def nSteps (M : Machine states 2) (n : ℕ) : Cfg states 2 → Option (Cfg states 2) :=
  Nat.rec (motive := fun _ => Cfg states 2 → Option (Cfg states 2))
    (fun c => some c)
    (fun _ ih c => (step M c).bind ih)
    n

@[simp]
theorem nSteps_zero (M : Machine states 2) (c : Cfg states 2) :
    nSteps M 0 c = some c := rfl

@[simp]
theorem nSteps_succ (M : Machine states 2) (n : ℕ) (c : Cfg states 2) :
    nSteps M (n + 1) c = (step M c).bind (nSteps M n) := rfl

attribute [eqns nSteps_zero nSteps_succ] nSteps

theorem nSteps_reaches {M : Machine states 2} {n : ℕ} {c c' : Cfg states 2}
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

theorem nSteps_eval_dom {M : Machine states 2} {n : ℕ} {c c' : Cfg states 2}
    (h : nSteps M n c = some c') :
    (eval (step M) c).Dom ↔ (eval (step M) c').Dom := by
  rw [StateTransition.reaches_eval (nSteps_reaches h)]

theorem nSteps_add {M : Machine states 2} (m n : ℕ) (c : Cfg states 2) :
    nSteps M (m + n) c = (nSteps M m c).bind (nSteps M n) := by
  induction m generalizing c with
  | zero => simp [nSteps]
  | succ m ih =>
    rw [Nat.succ_add, nSteps, nSteps]
    cases step M c <;> simp [ih]

theorem nSteps_bind_eq {M : Machine states 2} {m n : ℕ} {c c₁ c₂ : Cfg states 2}
    (h₁ : nSteps M m c = some c₁) (h₂ : nSteps M n c₁ = some c₂) :
    nSteps M (m + n) c = some c₂ := by
  rw [nSteps_add, h₁, Option.bind_some, h₂]

theorem step_nSteps {M : Machine states 2} {n : ℕ} {c c₁ c₂ : Cfg states 2}
    (h₁ : step M c = some c₁) (h₂ : nSteps M n c₁ = some c₂) :
    nSteps M (n + 1) c = some c₂ := by
  rw [nSteps, h₁, Option.bind_some, h₂]

theorem step_one {M : Machine states 2} {c c₁ : Cfg states 2} (h : step M c = some c₁) :
    nSteps M 1 c = some c₁ := by
  rw [nSteps, h]; rfl

theorem mk_append_replicate_zero (l : List (Fin 2)) (n : ℕ) :
    ListBlank.mk (l ++ List.replicate n 0) = ListBlank.mk l :=
  Quotient.sound' (Or.inr ⟨n, rfl⟩)

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

theorem step_right {M : Machine states 2} {q q' : Fin states} {a b : Fin 2}
    (h : M.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', ⟨R.head, L.cons b, R.tail⟩⟩ := by
  simp [step, h, Tape.write, Tape.move]

theorem step_right_cons {M : Machine states 2} {q q' : Fin states} {a b c : Fin 2}
    (h : M.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, ⟨a, L, R.cons c⟩⟩ = some ⟨q', ⟨c, L.cons b, R⟩⟩ := by
  simp [step, h, Tape.write, Tape.move]

theorem step_mkL_left {M : Machine states 2} {q q' : Fin states} {a b : Fin 2}
    (h : M.transition q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, h, Tape.mkL, Tape.write, Tape.move]

theorem step_mkL_right {M : Machine states 2} {q q' : Fin states} {a b : Fin 2}
    (h : M.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_right {M : Machine states 2} {q q' : Fin states} {a b : Fin 2}
    (h : M.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, h, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_left {M : Machine states 2} {q q' : Fin states} {a b : Fin 2}
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

/-- Scan to the left over a constant block using a uniform tape step. -/
theorem nSteps_mkL_left_scan_of_step {M : Machine states 2} {q : Fin states} {a b : Fin 2}
    (h : ∀ L R, step M ⟨q, ⟨a, L, R⟩⟩ = some ⟨q, Tape.mkL L (R.cons b)⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps M k ⟨q, Tape.mkL (ListBlank.append (List.replicate k a) L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append (List.replicate k b) R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, Tape.mkL_cons, h]
    simp only [Option.bind_some]
    rw [ih (R.cons b), append_replicate_cons]

theorem nSteps_mkL_left_scan {M : Machine states 2} {q : Fin states} {a b : Fin 2}
    (h : M.transition q a = some (b, .left, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps M k ⟨q, Tape.mkL (ListBlank.append (List.replicate k a) L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append (List.replicate k b) R)⟩ :=
  nSteps_mkL_left_scan_of_step (fun l r ↦ by simpa only [Tape.mkL_cons] using step_mkL_left h l r)
    k L R

/-- Scan to the right over a constant block using a uniform tape step. -/
theorem nSteps_mk'_right_scan_of_step {M : Machine states 2} {q : Fin states} {a b : Fin 2}
    (h : ∀ L R, step M ⟨q, ⟨a, L, R⟩⟩ = some ⟨q, Tape.mk' (L.cons b) R⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps M k ⟨q, Tape.mk' L (ListBlank.append (List.replicate k a) R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append (List.replicate k b) L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, Tape.mk'_cons, h]
    simp only [Option.bind_some]
    rw [ih (L.cons b), append_replicate_cons]

theorem nSteps_mk'_right_scan {M : Machine states 2} {q : Fin states} {a b : Fin 2}
    (h : M.transition q a = some (b, .right, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps M k ⟨q, Tape.mk' L (ListBlank.append (List.replicate k a) R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append (List.replicate k b) L) R⟩ :=
  nSteps_mk'_right_scan_of_step (fun l r ↦ by simpa only [Tape.mk'_cons] using step_mk'_right h l r)
    k L R

/-- The all-blank one-sided binary tape. -/
def B0 : ListBlank (Fin 2) := ListBlank.mk []

@[simp]
theorem B0_cons_zero : B0.cons 0 = B0 :=
  mk_append_replicate_zero [] 1

theorem reaches_imp_nSteps {M : Machine states 2} {a b : Cfg states 2}
    (h : Reaches (step M) a b) : ∃ k, nSteps M k a = some b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, nSteps_bind_eq hk (step_one hstep)⟩

theorem nSteps_eq_none_of_step_none {M : Machine states 2} {k : ℕ} (s : ℕ) {a b : Cfg states 2}
    (hk : nSteps M k a = some b) (hnone : step M b = none) (hks : k < s) :
    nSteps M s a = none := by
  have hs : s = k + ((s - k - 1) + 1) := by omega
  rw [hs, nSteps_add, hk, Option.bind_some, nSteps_succ, hnone, Option.bind_none]

end ConjectureMachines.Goldbach21
