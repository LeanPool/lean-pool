/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.DFA

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# Reading a finite automaton as a grammar

A DFA state describes what remains to be read. Use states as nonterminals:
a transition from `q` to `q'` on `a` becomes the production `q → a q'`, and an
accepting state may produce the empty word. Each derivation follows a run of
the automaton and stops only at an accepting state.

`dfaGrammar_derives_iff` proves this correspondence from any starting state;
`dfaGrammar_language` gives equality of the complete word languages. Applying
the forward Parikh theorem to this grammar establishes semilinearity for a
regular language. This adapter uses Mathlib's existing DFA and grammar types;
its finite production set is defined classically.
-/
namespace Parikh
variable {T : Type*} {σ : Type} [Fintype T] [Fintype σ]

/-- States are nonterminals. Transitions emit one letter and the next state;
accepting states may emit the empty word. Classical finiteness suffices here;
this adapter is not an executable compiler. -/
noncomputable abbrev dfaGrammar (M : DFA T σ) : ContextFreeGrammar T := by
  classical
  exact {
    NT := σ
    initial := M.start
    rules := (Finset.univ : Finset (σ × T)).image (fun (q, a) =>
      ⟨q, [.terminal a, .nonterminal (M.step q a)]⟩) ∪
      ((Finset.univ : Finset σ).filter (fun q => q ∈ M.accept)).image (fun q => ⟨q, []⟩)
  }

/-- From any DFA state, grammar derivation of a terminal word is exactly
acceptance by the DFA started at that state. -/
theorem dfaGrammar_derives_iff (M : DFA T σ) (q : σ) (w : List T) :
    (dfaGrammar M).Derives [.nonterminal q] (w.map .terminal) ↔
      M.evalFrom q w ∈ M.accept := by
  classical
  have hrules (r : ContextFreeRule T σ) : r ∈ (dfaGrammar M).rules ↔
      (∃ s a, r = ⟨s, [.terminal a, .nonterminal (M.step s a)]⟩) ∨
      (∃ s, s ∈ M.accept ∧ r = ⟨s, []⟩) := by
    dsimp only [dfaGrammar]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      Finset.mem_filter, true_and]
    constructor
    · rintro (⟨⟨s, a⟩, hr⟩ | ⟨s, hs, hr⟩)
      · exact Or.inl ⟨s, a, hr.symm⟩
      · exact Or.inr ⟨s, hs, hr.symm⟩
    · rintro (⟨s, a, rfl⟩ | ⟨s, hs, rfl⟩)
      · exact Or.inl ⟨(s, a), rfl⟩
      · exact Or.inr ⟨s, hs, rfl⟩
  have hrewrite (r : ContextFreeRule T σ) (u : List T) (s : σ)
      (v : List (Symbol T σ))
      (h : r.Rewrites (u.map .terminal ++ [.nonterminal s]) v) :
      r.input = s ∧ v = u.map .terminal ++ r.output := by
    induction u generalizing v with
    | nil =>
      cases h with
      | head => simp
      | cons _ h => cases h
    | cons a u ih =>
      cases h with
      | cons _ h =>
        obtain ⟨hs, hv⟩ := ih _ h
        exact ⟨hs, by simp [hv]⟩
  have hterminal (u : List T) (v : List (Symbol T σ)) :
      ¬ (dfaGrammar M).Produces (u.map .terminal) v := by
    rintro ⟨r, _, hr⟩
    have := hr.nonterminal_input_mem
    simp at this
  constructor
  · intro h
    have hinvariant {v : List (Symbol T σ)}
        (hv : (dfaGrammar M).Derives [.nonterminal q] v) :
        (∃ u, v = u.map .terminal ∧ M.evalFrom q u ∈ M.accept) ∨
        (∃ u s, v = u.map .terminal ++ [.nonterminal s] ∧ M.evalFrom q u = s) := by
      induction hv with
      | refl => exact Or.inr ⟨[], q, rfl, rfl⟩
      | tail _ hstep ih =>
        rcases ih with ⟨u, rfl, _⟩ | ⟨u, s, rfl, hrun⟩
        · exact (hterminal _ _ hstep).elim
        · obtain ⟨r, hr, hrewriteStep⟩ := hstep
          obtain ⟨hinput, rfl⟩ := hrewrite r u s _ hrewriteStep
          rcases (hrules r).mp hr with ⟨s', a, rfl⟩ | ⟨s', hs', rfl⟩
          · change s' = s at hinput
            subst s'
            right
            refine ⟨u ++ [a], M.step s a, ?_, ?_⟩
            · simp
            · simp [DFA.evalFrom_of_append, hrun]
          · change s' = s at hinput
            subst s'
            left
            exact ⟨u, by simp, hrun ▸ hs'⟩
    rcases hinvariant h with ⟨u, hu, haccept⟩ | ⟨u, s, hu, _⟩
    · have : w = u := (List.map_inj_right (fun _ _ h => Symbol.terminal.inj h)).mp hu
      simpa [this] using haccept
    · have : (.nonterminal s : Symbol T σ) ∈ w.map .terminal := by
        exact hu.symm ▸ (by simp)
      simp at this
  · intro h
    induction w generalizing q with
    | nil =>
      apply ContextFreeGrammar.Produces.single
      refine ⟨⟨q, []⟩, (hrules _).mpr (Or.inr ⟨q, h, rfl⟩), ?_⟩
      exact ContextFreeRule.Rewrites.input_output
    | cons a w ih =>
      have hstep : (dfaGrammar M).Produces [.nonterminal q]
          [.terminal a, .nonterminal (M.step q a)] :=
        ⟨⟨q, [.terminal a, .nonterminal (M.step q a)]⟩,
          (hrules _).mpr (Or.inl ⟨q, a, rfl⟩), ContextFreeRule.Rewrites.input_output⟩
      exact hstep.trans_derives ((ih (M.step q a) h).append_left [.terminal a])

/-- The finite right-linear grammar generates precisely the DFA's language,
including empty words and empty terminal alphabets. -/
theorem dfaGrammar_language (M : DFA T σ) : (dfaGrammar M).language = M.accepts := by
  ext w
  exact dfaGrammar_derives_iff M M.start w

end Parikh
