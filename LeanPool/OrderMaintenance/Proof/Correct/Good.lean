/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Correct.Frame


/-!
# Background work keeps INV-S or leaves the element list intact

`Good m`: from a state satisfying INV-S, `m`
* either succeeds, in a state satisfying INV-S with the same element list,
* or fails a guard, in a state whose element records are unchanged (FALLBACK then rebuilds
  everything else from them, Lemma 3.3),
* and never hits `Err.bug`.

In both cases the element records (links, liveness, handles) are unchanged: `EFrame`.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The element records are unchanged, except for their group and label. -/
structure EFrame (s s' : Core) : Prop where
  size : s'.E.size = s.E.size
  next : ∀ e, eN s' e = eN s e
  prev : ∀ e, eP s' e = eP s e
  live : ∀ e, (s'.E.getX e).live = (s.E.getX e).live
  h : ∀ e, (s'.E.getX e).h = (s.E.getX e).h
  head : s'.head = s.head
  tail : s'.tail = s.tail
  P : s'.P = s.P

theorem EFrame.refl (s : Core) : EFrame s s :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl⟩

theorem EFrame.trans {s t u : Core} (h1 : EFrame s t) (h2 : EFrame t u) : EFrame s u :=
  ⟨h2.size.trans h1.size, fun e => (h2.next e).trans (h1.next e),
   fun e => (h2.prev e).trans (h1.prev e), fun e => (h2.live e).trans (h1.live e),
   fun e => (h2.h e).trans (h1.h e), h2.head.trans h1.head, h2.tail.trans h1.tail, h2.P.trans h1.P⟩

theorem SameLinks.eframe {s s' : Core} (h : SameLinks s s') : EFrame s s' :=
  ⟨h.Esize, h.eN, h.eP, h.eLive, h.eH, h.head, h.tail, h.P⟩

/-- Preserve a valid core and its abstract nesting whenever the computation succeeds. -/
def Good {α : Type} (m : CM α) : Prop :=
  ∀ s A, INV s A →
    match m.run s with
    | .ok _ s' => EFrame s s' ∧ ∃ A', INV s' A' ∧ A'.elist = A.elist
    | .error (.guard _) s' => EFrame s s'
    | .error (.bug _) _ => False

section good
variable {α β : Type}

theorem Good.pure (a : α) : Good (pure a : CM α) :=
  fun s A h => ⟨EFrame.refl s, A, h, rfl⟩

theorem Good.guard (msg : String) : Good (OrderMaintenance.Model.guard msg : CM α) :=
  fun s _ _ => EFrame.refl s

theorem Good.of_pres {m : CM α} (h : Pres Safe m) : Good m := by
  intro s A hI
  have h1 := h s
  rcases hms : m.run s with ⟨a, s'⟩ | ⟨e, s'⟩
  · rw [hms] at h1; exact ⟨h1.1.eframe, A, h1.2 A hI, rfl⟩
  · rw [hms] at h1
    cases e with
    | guard _ => exact h1.1.eframe
    | bug _ => exact h1

theorem Good.bind {m : CM α} {f : α → CM β} (hm : Good m) (hf : ∀ a, Good (f a)) :
    Good (m >>= f) := by
  intro s A hI
  have h1 := hm s A hI
  rw [run_bind]
  rcases hms : m.run s with ⟨a, s'⟩ | ⟨e, s'⟩
  · rw [hms] at h1
    obtain ⟨hef, A', hI', hA'⟩ := h1
    have h2 := hf a s' A' hI'
    simp only
    rcases hfs : (f a).run s' with ⟨b, s''⟩ | ⟨e, s''⟩
    · rw [hfs] at h2
      obtain ⟨hef2, A'', hI'', hA''⟩ := h2
      exact ⟨hef.trans hef2, A'', hI'', hA''.trans hA'⟩
    · rw [hfs] at h2
      cases e with
      | guard _ => exact hef.trans h2
      | bug _ => exact h2
  · rw [hms] at h1
    cases e with
    | guard _ => exact h1
    | bug _ => exact h1

theorem Good.ite {c : Prop} [Decidable c] {a b : CM α} (ha : Good a) (hb : Good b) :
    Good (if c then a else b) := by
  split <;> assumption

theorem Good.forIn_list {γ : Type} (l : List γ) (b : β) {f : γ → β → CM (ForInStep β)}
    (hf : ∀ x b, Good (f x b)) : Good (forIn l b f) := by
  induction l generalizing b with
  | nil => exact Good.pure b
  | cons x t ih =>
    simp only [List.forIn_cons]
    refine Good.bind (hf x b) fun r => ?_
    cases r with
    | done b' => exact Good.pure b'
    | yield b' => exact ih b'

theorem Good.get : Good (get : CM Core) := Good.of_pres Pres.get

end good

/-- Decompose a computation into `Good` pieces, using the given lemmas for calls. -/
syntax "good" ("[" term,* "]")? : tactic
macro_rules
  | `(tactic| good) => `(tactic| good [Good.get])
  | `(tactic| good [$ts,*]) => `(tactic| repeat' (first
      | with_reducible exact Good.pure _
      | with_reducible exact Good.get
      | with_reducible exact Good.guard _
      | with_reducible refine Good.bind ?_ fun _ => ?_
      | with_reducible refine Good.forIn_list _ _ fun _ _ => ?_
      | with_reducible refine Good.ite ?_ ?_
      | (first $[| with_reducible exact $ts:term]*)
      | split
      | (dsimp only; done)
      | dsimp only))

end OrderMaintenance.Proof
