/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.Trace

/-!
# Executable evaluation-trace certificates

`Nock.Verb.run` (`Nock/Verb.lean`) iterates the small-step `next` to a result noun but discards
the intermediate states.  This module adds `runTrace`, which returns the full list of visited
verbs, and proves it is a *certificate* of the paper's evaluation trace (`Def:eval_trace`,
`main.tex:1114–1128`; transition checker `Algorithm:Transition_Function`, `main.tex:1633–1666`):

* `runTrace_traceOf`         — the emitted list is a consistent trace of the input (`TraceOf`);
* `runTrace_complete`        — it is complete (ends at a terminal/⊥ verb);
* `runTrace_adjacent_nockCheck` — every adjacent pair is accepted by the two-verb checker `Nock`
                                (`NockCheck _ (some _) = true`);
* `runTrace_run`             — its last verb carries exactly the `run` result;
* `runTrace_unique`          — the emitted trace is independent of the fuel budget.

`runTrace_unique` is the executable realization of `Thm:deterministic_Trace` (`main.tex:1156–1158`):
because `next` is a function, the trace from a verb is forced, so any two successful runs coincide.
These are Lean consistency theorems, not numbered paper theorems.
-/

@[expose] public section

namespace Nock
namespace Verb

/-- Fuel-indexed iteration of `next` that *records* every visited verb.  `some T` iff evaluation
    reached a terminal/⊥ state within the budget (so `T` ends there); `none` iff fuel ran out. -/
def runTrace : Nat → Verb → Option (List Verb)
  | 0,        _ => none
  | fuel + 1, v =>
      match next v with
      | some v' => (runTrace fuel v').map (fun T => v :: T)
      | none    => some [v]

/-- Run a Nock program `*[subject, formula]`, recording the full evaluation trace. -/
def runTraceProgram (fuel : Nat) (subject formula : Noun) : Option (List Verb) :=
  runTrace fuel (program subject formula)

/-! ### The trace is a consistent, complete trace of the input -/

/-- **`runTrace` produces a consistent, complete trace headed at the input.**  Bundles the three
    facts carried through the fuel recursion: head `= v`, `Consistent`, and `Complete`. -/
theorem runTrace_spec :
    ∀ (fuel : Nat) (v : Verb) (T : List Verb), runTrace fuel v = some T →
      TraceOf v T ∧ Complete T := by
  intro fuel
  induction fuel with
  | zero => intro v T h; simp [runTrace] at h
  | succ fuel ih =>
      intro v T h
      simp only [runTrace] at h
      cases hn : next v with
      | none =>
          rw [hn] at h
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨⟨rfl, trivial⟩, ⟨v, rfl, hn⟩⟩
      | some v' =>
          rw [hn] at h
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨T', hT', rfl⟩ := h
          obtain ⟨⟨hhead, hcons⟩, hcomp⟩ := ih v' T' hT'
          obtain ⟨rest, rfl⟩ : ∃ rest, T' = v' :: rest := by
            cases T' with
            | nil => simp at hhead
            | cons a t =>
                simp only [List.head?_cons, Option.some.injEq] at hhead
                exact ⟨t, by rw [hhead]⟩
          refine ⟨⟨rfl, ⟨hn, hcons⟩⟩, ?_⟩
          obtain ⟨w, hw, hwn⟩ := hcomp
          exact ⟨w, by rw [List.getLast?_cons_cons, hw], hwn⟩

/-- **The emitted list is a consistent trace of the input** (`TraceOf`, `main.tex:1114–1118`). -/
theorem runTrace_traceOf {fuel : Nat} {v : Verb} {T : List Verb}
    (h : runTrace fuel v = some T) : TraceOf v T := (runTrace_spec fuel v T h).1

/-- **The emitted trace is complete** (`main.tex:1122`): it ends at a terminal or ⊥ verb. -/
theorem runTrace_complete {fuel : Nat} {v : Verb} {T : List Verb}
    (h : runTrace fuel v = some T) : Complete T := (runTrace_spec fuel v T h).2

/-! ### Every adjacent pair is accepted by the transition checker `Nock` -/

/-- Every consecutive pair of a list is accepted by the paper's two-verb checker `Nock`
    (`NockCheck _ (some _) = true`).  Mirrors the shape of `Consistent`. -/
def AdjNockCheck : List Verb → Prop
  | []             => True
  | [_]            => True
  | a :: b :: rest => NockCheck a (some b) = true ∧ AdjNockCheck (b :: rest)

/-- A consistent trace is accepted pairwise by the transition checker: every `Step a b`
    (`next a = some b`) makes `NockCheck a (some b) = true` (`nockCheck_eq_true_iff`). -/
theorem adjNockCheck_of_consistent : ∀ (T : List Verb), Consistent T → AdjNockCheck T
  | [],             _ => trivial
  | [_],            _ => trivial
  | a :: b :: rest, h => by
      obtain ⟨hstep, hcons⟩ := h
      exact ⟨nockCheck_eq_true_iff.mpr (Or.inl ⟨b, rfl, hstep⟩),
        adjNockCheck_of_consistent (b :: rest) hcons⟩

/-- **Executable** two-verb transition checker over a whole trace: `Bool`-valued reflection of
    `AdjNockCheck`, so the certificate can actually be *run* (and extracted). -/
def adjNockCheckB : List Verb → Bool
  | []             => true
  | [_]            => true
  | a :: b :: rest => NockCheck a (some b) && adjNockCheckB (b :: rest)

/-- `adjNockCheckB` decides `AdjNockCheck`: the executable checker returns `true` iff every
    adjacent pair passes the paper's transition checker `Nock`. -/
theorem adjNockCheckB_iff : ∀ (T : List Verb), adjNockCheckB T = true ↔ AdjNockCheck T
  | []             => by simp [adjNockCheckB, AdjNockCheck]
  | [_]            => by simp [adjNockCheckB, AdjNockCheck]
  | _ :: b :: rest => by
      simp only [adjNockCheckB, AdjNockCheck, Bool.and_eq_true]
      exact and_congr Iff.rfl (adjNockCheckB_iff (b :: rest))

-- main.tex:1633–1666  (Algorithm:Transition_Function accepts every emitted step)
/-- **Every adjacent pair of the emitted trace passes the transition checker `Nock`.**  The
    certificate is checkable by the paper's `Algorithm:Transition_Function`. -/
theorem runTrace_adjacent_nockCheck {fuel : Nat} {v : Verb} {T : List Verb}
    (h : runTrace fuel v = some T) : AdjNockCheck T :=
  adjNockCheck_of_consistent T (runTrace_traceOf h).2

/-- **The executable checker accepts every emitted trace.**  Running `adjNockCheckB` on the
    output of `runTrace` returns `true` — the certificate is machine-checkable, not just a
    `Prop`. -/
theorem runTrace_adjNockCheckB {fuel : Nat} {v : Verb} {T : List Verb}
    (h : runTrace fuel v = some T) : adjNockCheckB T = true :=
  (adjNockCheckB_iff T).mpr (runTrace_adjacent_nockCheck h)

/-! ### The last verb carries the `run` result -/

/-- **The emitted trace's last verb carries exactly the `run` result.**  `run fuel v` is the
    `result` (terminal noun, or `none` on crash) of the trace's final verb. -/
theorem runTrace_run :
    ∀ (fuel : Nat) (v : Verb) (T : List Verb), runTrace fuel v = some T →
      ∃ w, T.getLast? = some w ∧ run fuel v = result w := by
  intro fuel
  induction fuel with
  | zero => intro v T h; simp [runTrace] at h
  | succ fuel ih =>
      intro v T h
      simp only [runTrace] at h
      cases hn : next v with
      | none =>
          rw [hn] at h
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨v, rfl, by simp only [run, hn]⟩
      | some v' =>
          rw [hn] at h
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨T', hT', rfl⟩ := h
          obtain ⟨w, hw, hrun⟩ := ih v' T' hT'
          obtain ⟨rest, rfl⟩ : ∃ rest, T' = v' :: rest := by
            have hhead := (runTrace_spec fuel v' T' hT').1.1
            cases T' with
            | nil => simp at hhead
            | cons a t =>
                simp only [List.head?_cons, Option.some.injEq] at hhead
                exact ⟨t, by rw [hhead]⟩
          refine ⟨w, ?_, ?_⟩
          · rw [List.getLast?_cons_cons]; exact hw
          · simp only [run, hn]; exact hrun

/-! ### The emitted trace is independent of the fuel budget -/

-- main.tex:1156–1158  (executable realization of Thm:deterministic_Trace)
/-- **The emitted trace is unique.**  Because `next` is a function, any two successful runs of
    `runTrace` on the same verb — at any fuel budgets — produce the same trace.  This is the
    executable form of `Thm:deterministic_Trace` (`main.tex:1156–1158`). -/
theorem runTrace_unique :
    ∀ (fuel₁ fuel₂ : Nat) (v : Verb) (T₁ T₂ : List Verb),
      runTrace fuel₁ v = some T₁ → runTrace fuel₂ v = some T₂ → T₁ = T₂ := by
  intro fuel₁
  induction fuel₁ with
  | zero => intro fuel₂ v T₁ T₂ h₁ _; simp [runTrace] at h₁
  | succ f₁ ih =>
      intro fuel₂ v T₁ T₂ h₁ h₂
      cases fuel₂ with
      | zero => simp [runTrace] at h₂
      | succ f₂ =>
          simp only [runTrace] at h₁ h₂
          cases hn : next v with
          | none =>
              rw [hn] at h₁ h₂
              simp only [Option.some.injEq] at h₁ h₂
              rw [← h₁, ← h₂]
          | some v' =>
              rw [hn] at h₁ h₂
              simp only [Option.map_eq_some_iff] at h₁ h₂
              obtain ⟨T₁', hT₁', rfl⟩ := h₁
              obtain ⟨T₂', hT₂', rfl⟩ := h₂
              rw [ih f₂ v' T₁' T₂' hT₁' hT₂']

-- main.tex:1122–1124, 1633–1666  (the completion edge: valid terminal, or a checked crash to ⊥)
/-- **The completion edge is accounted for.**  The emitted trace's last verb is either terminal
    (a *valid* completion, `main.tex:1123`) or crashes, and in the crash case the transition to `⊥`
    passes the checker (`NockCheck w none = true`, `main.tex:1124`, `1644`, `1650`).  Together with
    `runTrace_adjacent_nockCheck`, every edge of the certificate — including the final ⊥ edge on a
    crash — is `Nock`-checked; there is no unchecked step. -/
theorem runTrace_final_edge {fuel : Nat} {v : Verb} {T : List Verb}
    (h : runTrace fuel v = some T) :
    ∃ w, T.getLast? = some w ∧ (isTerminal w = true ∨ NockCheck w none = true) := by
  obtain ⟨w, hw, hwn⟩ := runTrace_complete h
  refine ⟨w, hw, ?_⟩
  by_cases ht : isTerminal w = true
  · exact Or.inl ht
  · refine Or.inr (nockCheck_eq_true_iff.mpr (Or.inr ⟨rfl, ?_⟩))
    have hgi : getIndex w ≠ none := fun hg => ht (getIndex_none_iff_terminal.mp hg)
    exact ⟨hgi, hwn⟩

/-- **`runTraceProgram` emits a certified trace of the program.**  Its head is the program verb,
    it is consistent and complete, every adjacent step passes the checker `Nock`, and the final
    state is terminal or has a crash edge accepted by the checker. -/
theorem runTraceProgram_certificate {fuel : Nat} {subject formula : Noun} {T : List Verb}
    (h : runTraceProgram fuel subject formula = some T) :
    TraceOf (program subject formula) T ∧ Complete T ∧ AdjNockCheck T ∧
      (∃ w, T.getLast? = some w ∧ (isTerminal w = true ∨ NockCheck w none = true)) :=
  ⟨runTrace_traceOf h, runTrace_complete h, runTrace_adjacent_nockCheck h, runTrace_final_edge h⟩

end Verb
end Nock
