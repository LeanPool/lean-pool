/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Model


/-!
# Reasoning about Level F code

* `Result.state`: the state an `EStateM` computation ends in, whether it succeeds or throws.
* `Pres R m`: every run of `m` ends in a state related to its start state by `R`. For a
  reflexive, transitive `R` this composes through the whole `do`-notation; the tactic `pres`
  decomposes a computation into its primitive state updates.
* Array lemmas for the total-map view (`getX`).
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Results -/

/-- Recover the reached state from a successful or failed state-monad result. -/
def Result.state {ε σ α : Type} : EStateM.Result ε σ α → σ
  | .ok _ s => s
  | .error _ s => s

@[simp] theorem Result.state_ok {ε σ α : Type} (a : α) (s : σ) :
    Result.state (EStateM.Result.ok a s : EStateM.Result ε σ α) = s := rfl
@[simp] theorem Result.state_error {ε σ α : Type} (e : ε) (s : σ) :
    Result.state (EStateM.Result.error e s : EStateM.Result ε σ α) = s := rfl

/-! ### `run` lemmas -/

section run
variable {α β : Type}

@[simp] theorem run_pure (a : α) (s : Core) : (pure a : CM α).run s = .ok a s := rfl
@[simp] theorem run_get (s : Core) : (get : CM Core).run s = .ok s s := rfl
@[simp] theorem run_set (t s : Core) : (set t : CM PUnit).run s = .ok ⟨⟩ t := rfl
@[simp] theorem run_modify (f : Core → Core) (s : Core) :
    (modify f : CM PUnit).run s = .ok ⟨⟩ (f s) := rfl
@[simp] theorem run_modifyGet (f : Core → α × Core) (s : Core) :
    (modifyGet f : CM α).run s = .ok (f s).1 (f s).2 := rfl
@[simp] theorem run_throw (e : Err) (s : Core) : (throw e : CM α).run s = .error e s := rfl
@[simp] theorem run_guard (msg : String) (s : Core) :
    (OrderMaintenance.Model.guard msg : CM α).run s = .error (.guard msg) s := rfl
@[simp] theorem run_ite {c : Prop} [Decidable c] (a b : CM α) (s : Core) :
    (if c then a else b).run s = if c then a.run s else b.run s := by
  split <;> rfl
theorem run_bind (m : CM α) (f : α → CM β) (s : Core) :
    (m >>= f).run s = match m.run s with
      | .ok a s' => (f a).run s'
      | .error e s' => .error e s' := by
  show EStateM.bind m f s = _
  unfold EStateM.bind EStateM.run
  cases m s <;> rfl

end run

/-! ### Frame preservation -/

/-- Every run of `m` ends, normally or by a failed guard, in a state related to its start state
by `R`; and `m` never hits `Err.bug`. -/
def Pres {α : Type} (R : Core → Core → Prop) (m : CM α) : Prop :=
  ∀ s, match m.run s with
    | .ok _ s' => R s s'
    | .error (.guard _) s' => R s s'
    | .error (.bug _) _ => False

/-- A preorder on states, for `Pres`. -/
class IsPre (R : Core → Core → Prop) : Prop where
  refl : ∀ s, R s s
  trans : ∀ s t u, R s t → R t u → R s u

section pres
variable {R : Core → Core → Prop} [IsPre R] {α β : Type}

theorem Pres.pure (a : α) : Pres R (pure a : CM α) := fun s => IsPre.refl s
theorem Pres.get : Pres R (get : CM Core) := fun s => IsPre.refl s
theorem Pres.guard (msg : String) : Pres R (guard msg : CM α) := fun s => IsPre.refl s
omit [IsPre R] in
theorem Pres.modify {f : Core → Core} (h : ∀ s, R s (f s)) : Pres R (modify f : CM PUnit) := h
omit [IsPre R] in
omit [IsPre R] in
theorem Pres.modifyGet {f : Core → α × Core} (h : ∀ s, R s (f s).2) :
    Pres R (modifyGet f : CM α) := h

theorem Pres.bind {m : CM α} {f : α → CM β} (hm : Pres R m) (hf : ∀ a, Pres R (f a)) :
    Pres R (m >>= f) := by
  intro s
  have h1 := hm s
  rw [run_bind]
  rcases hms : m.run s with ⟨a, s'⟩ | ⟨e, s'⟩
  · rw [hms] at h1
    have h2 := hf a s'
    simp only
    rcases hfs : (f a).run s' with ⟨b, s''⟩ | ⟨e, s''⟩
    · rw [hfs] at h2; exact IsPre.trans _ _ _ h1 h2
    · rw [hfs] at h2
      cases e with
      | guard _ => exact IsPre.trans _ _ _ h1 h2
      | bug _ => exact h2
  · rw [hms] at h1
    cases e with
    | guard _ => exact h1
    | bug _ => exact h1

omit [IsPre R] in
theorem Pres.ite {c : Prop} [Decidable c] {a b : CM α} (ha : Pres R a) (hb : Pres R b) :
    Pres R (if c then a else b) := by
  split <;> assumption

theorem Pres.forIn_list {γ : Type} (l : List γ) (b : β) {f : γ → β → CM (ForInStep β)}
    (hf : ∀ x b, Pres R (f x b)) : Pres R (forIn l b f) := by
  induction l generalizing b with
  | nil => exact Pres.pure b
  | cons x t ih =>
    simp only [List.forIn_cons]
    refine Pres.bind (hf x b) fun r => ?_
    cases r with
    | done b' => exact Pres.pure b'
    | yield b' => exact ih b'

theorem Pres.mapM_list {γ δ : Type} (l : List γ) {f : γ → CM δ} (hf : ∀ x, Pres R (f x)) :
    Pres R (l.mapM f) := by
  induction l with
  | nil => exact Pres.pure _
  | cons x t ih =>
    simp only [List.mapM_cons]
    exact Pres.bind (hf x) fun _ => Pres.bind ih fun _ => Pres.pure _

theorem Pres.forM_list {γ : Type} (l : List γ) {f : γ → CM PUnit} (hf : ∀ x, Pres R (f x)) :
    Pres R (l.forM f) := by
  induction l with
  | nil => exact Pres.pure _
  | cons x t ih =>
    show Pres R (do f x; t.forM f)
    exact Pres.bind (hf x) fun _ => ih

theorem Pres.forIn_array {γ : Type} (a : Array γ) (b : β) {f : γ → β → CM (ForInStep β)}
    (hf : ∀ x b, Pres R (f x b)) : Pres R (forIn a b f) := by
  rw [← Array.forIn_toList]
  exact Pres.forIn_list _ _ hf

omit [IsPre R] in
theorem Pres.mono {R' : Core → Core → Prop} {m : CM α} (h : Pres R m) (hR : ∀ s t, R s t → R' s t) :
    Pres R' m := by
  intro s
  have h1 := h s
  rcases hms : m.run s with ⟨a, s'⟩ | ⟨e, s'⟩
  · rw [hms] at h1; exact hR _ _ h1
  · rw [hms] at h1
    cases e with
    | guard _ => exact hR _ _ h1
    | bug _ => exact h1

end pres

/-- Decompose a computation into primitive state updates, using the given lemmas for calls.
Leaves goals of the form `∀ s, R s (f s)` for the updates. -/
syntax "pres" ("[" term,* "]")? : tactic
macro_rules
  | `(tactic| pres) => `(tactic| pres [Pres.get])
  | `(tactic| pres [$ts,*]) => `(tactic| repeat' (first
      | with_reducible exact Pres.pure _
      | with_reducible exact Pres.get
      | with_reducible exact Pres.guard _
      | with_reducible refine Pres.bind ?_ fun _ => ?_
      | with_reducible refine Pres.forIn_list _ _ fun _ _ => ?_
      | with_reducible refine Pres.forIn_array _ _ fun _ _ => ?_
      | with_reducible refine Pres.mapM_list _ fun _ => ?_
      | with_reducible refine Pres.forM_list _ fun _ => ?_
      | with_reducible refine Pres.ite ?_ ?_
      | with_reducible refine Pres.modify ?_
      | with_reducible refine Pres.modifyGet ?_
      | (first $[| with_reducible exact $ts:term]*)
      | split
      | (dsimp only; done)
      | dsimp only))

/-! ### Arrays as total maps -/

section arrays
variable {α : Type} [Inhabited α]

theorem Array.getX_def (a : Array α) (i : Nat) : a.getX i = a.getD i default := rfl

@[simp] theorem Array.getX_modify (a : Array α) (i j : Nat) (f : α → α) :
    (a.modify i f).getX j = if i = j ∧ i < a.size then f (a.getX j) else a.getX j := by
  simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size <;> simp [hi]
  · simp [hij]

omit [Inhabited α] in
theorem Array.size_modify' (a : Array α) (i : Nat) (f : α → α) :
    (a.modify i f).size = a.size := Array.size_modify

@[simp] theorem Array.getX_push (a : Array α) (v : α) (j : Nat) :
    (a.push v).getX j = if j = a.size then v else a.getX j := by
  simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases h : j = a.size <;> simp [h]

theorem Array.getX_set! (a : Array α) (i j : Nat) (v : α) :
    (a.set! i v).getX j = if i = j ∧ i < a.size then v else a.getX j := by
  simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij; by_cases hi : i < a.size <;> simp [hi]
  · simp [hij]

@[simp] theorem Array.getX_setIfInBounds (a : Array α) (i j : Nat) (v : α) :
    (a.setIfInBounds i v).getX j = if i = j ∧ i < a.size then v else a.getX j := by
  rw [← Array.set!_eq_setIfInBounds]; exact Array.getX_set! a i j v

omit [Inhabited α] in
theorem Array.size_set!' (a : Array α) (i : Nat) (v : α) :
    (a.set! i v).size = a.size := by simp

@[simp] theorem Array.getX_ite {c : Prop} [Decidable c] (a b : Array α) (i : Nat) :
    (if c then a else b).getX i = if c then a.getX i else b.getX i := by split <;> rfl

omit [Inhabited α] in
@[simp] theorem Array.size_ite {c : Prop} [Decidable c] (a b : Array α) :
    (if c then a else b).size = if c then a.size else b.size := by split <;> rfl

theorem Array.getX_ge (a : Array α) {j : Nat} (h : a.size ≤ j) : a.getX j = default := by
  simp [Array.getX, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

end arrays

end OrderMaintenance.Proof

/-! ### `run` of reads followed by a continuation -/

namespace OrderMaintenance.Proof

open OrderMaintenance.Model

section reads
variable {β : Type} (f : _ → CM β) (s : Core)

theorem run_get_bind (k : Core → CM β) : (get >>= k).run s = (k s).run s := rfl
theorem run_modify_bind (g : Core → Core) (k : PUnit → CM β) :
    (modify g >>= k).run s = (k ⟨⟩).run (g s) := rfl
theorem run_getE_bind (i : Nat) (k : Elem → CM β) :
    (getE i >>= k).run s = (k (s.E.getX i)).run s := rfl
theorem run_getG_bind (i : Nat) (k : Group → CM β) :
    (getG i >>= k).run s = (k (s.Gs.getX i)).run s := rfl
theorem run_getC_bind (i : Nat) (k : Chunk → CM β) :
    (getC i >>= k).run s = (k (s.C.getX i)).run s := rfl
theorem run_getP_bind (k : Params → CM β) : (getP >>= k).run s = (k s.P).run s := rfl
theorem run_pure_bind {α : Type} (a : α) (k : α → CM β) :
    (pure a >>= k).run s = (k a).run s := rfl
@[simp] theorem run_map_guard {γ : Type} (g : γ → β) (msg : String) :
    (g <$> (OrderMaintenance.Model.guard msg : CM γ)).run s = .error (.guard msg) s := rfl

theorem run_between (a b : Nat) (why : String) :
    (between a b why).run s =
      if a + 1 ≥ b then .error (.guard why) s else .ok ((a + b) / 2) s := by
  unfold between
  by_cases h : a + 1 ≥ b <;> simp [h]

theorem run_after (a D B : Nat) (why : String) :
    (after a D B why).run s =
      if a + D ≥ 1 <<< B ∨ a + D ≤ a then .error (.guard why) s else .ok (a + D) s := by
  unfold after
  by_cases h : a + D ≥ 1 <<< B ∨ a + D ≤ a
  · rcases h with h | h <;> simp [h]
  · simp only [not_or] at h; simp [h.1, h.2]

theorem run_before (b D : Nat) (why : String) :
    (before b D why).run s =
      if b < D ∨ D = 0 then .error (.guard why) s else .ok (b - D) s := by
  unfold before
  by_cases h : b < D ∨ D = 0
  · rcases h with h | h <;> simp [h]
  · simp only [not_or] at h; simp [h.1, h.2]

end reads

end OrderMaintenance.Proof
