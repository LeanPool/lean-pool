/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import Init

/-!
  Chain-Based Minimalist Grammars (Stabler 1997; Stabler & Keenan 2003)

  Canonical algebraic formalization of Chomsky's Minimalist Program:
    • Syntactic features: category `x`, selector `=x`, licensor `+f`, licensee `-f`.
    • Expressions: `(isLex, headChain, movers)` obeying the Shortest Move Constraint (SMC).
    • Structure-building operations: `lex`, `merge1`, `merge2`, `merge3`, `move1`, `move2`.

  The SMC is built into the rules as an invariant of every derived expression.
  Stabler and Keenan (2003, §2, Definition 1) impose it on `move` only.
  The formalized variant uses nonempty lexical feature lists and a distinguished
  basic category as its goal. `MGOriginal.lean` presents the rules without
  the extra invariant on `merge` and proves language equivalence for this variant.
-/

@[expose] public section

namespace FormalLinguistics

/-- Minimalist syntactic features over base categories `Base` and movement features `Lic`. -/
inductive MGFeature (Base Lic : Type) where
  | cat : Base → MGFeature Base Lic        -- `x`   (syntactic category)
  | sel : Base → MGFeature Base Lic        -- `=x`  (selector)
  | licensor : Lic → MGFeature Base Lic    -- `+f`  (movement attractor)
  | licensee : Lic → MGFeature Base Lic    -- `-f`  (movement licensee)
  deriving DecidableEq, Repr

/-- A syntactic chain pairing a phonetic string with its remaining feature stack. -/
structure MGChain (Base Lic T : Type) where
  /-- Terminal string carried by the chain. -/
  str : List T
  /-- Remaining ordered feature sequence. -/
  feats : List (MGFeature Base Lic)
  deriving DecidableEq, Repr

/-- A Minimalist Grammar expression:
    `isLex = true` denotes a lexical item (`::` in Stabler & Keenan's notation),
    `isLex = false` denotes a derived expression (`:`),
    `head` is the main chain, and `movers` are pending displaced chains. -/
structure MGExpr (Base Lic T : Type) where
  /-- Whether the expression is a lexical item rather than the result of a rule. -/
  isLex : Bool
  /-- Head chain of the expression. -/
  head : MGChain Base Lic T
  /-- Chains waiting to discharge licensee features by movement. -/
  movers : List (MGChain Base Lic T)
  deriving DecidableEq, Repr

/-- Extract the leading licensee feature `f` if a chain begins with `licensee f`. -/
def MGChain.headLic {Base Lic T : Type} (c : MGChain Base Lic T) : Option Lic :=
  match c.feats with
  | MGFeature.licensee f :: _ => some f
  | _ => none

/-- Shortest Move Constraint (SMC) & mover well-formedness:
    every mover starts with a licensee feature `-f`, and all leading licensee features
    among active movers are pairwise distinct. -/
def SMC {Base Lic T : Type} (ms : List (MGChain Base Lic T)) : Prop :=
  (∀ c, c ∈ ms → ∃ f δ, c.feats = MGFeature.licensee f :: δ) ∧
  (ms.filterMap MGChain.headLic).Nodup

/-- A finite Minimalist Grammar over base categories `Base`, movement features `Lic`,
    and terminal alphabet `T`. -/
structure MG (Base Lic T : Type) where
  /-- Category of complete expressions. -/
  start : Base
  /-- Finite list of lexical strings paired with nonempty feature sequences. -/
  lexicon : List (List T × List (MGFeature Base Lic))
  /-- The formalized variant requires each lexical entry to have at least one feature. -/
  lex_nonempty : ∀ entry, entry ∈ lexicon → entry.2 ≠ []

namespace MG

variable {Base Lic T : Type}

/-- Derivable expressions of a Minimalist Grammar via Stabler & Keenan's (2003)
    five structure-building rules (`merge1`, `merge2`, `merge3`, `move1`, `move2`)
    plus lexical insertion (`lex`). -/
inductive Derives (G : MG Base Lic T) : MGExpr Base Lic T → Prop where
  /-- Lexical insertion: `(w, α) ∈ G.lexicon` yields a lexical (`isLex = true`) expression. -/
  | lex {w : List T} {α : List (MGFeature Base Lic)} :
      (w, α) ∈ G.lexicon →
      Derives G ⟨true, ⟨w, α⟩, []⟩

  /-- Merge 1 (complement of a lexical head, right-adjoined: `s ++ t`). -/
  | merge1 {s t : List T} {x : Base} {γ : List (MGFeature Base Lic)}
      {b : Bool} {ms : List (MGChain Base Lic T)} :
      Derives G ⟨true, ⟨s, MGFeature.sel x :: γ⟩, []⟩ →
      Derives G ⟨b, ⟨t, [MGFeature.cat x]⟩, ms⟩ →
      Derives G ⟨false, ⟨s ++ t, γ⟩, ms⟩

  /-- Merge 2 (specifier of a derived head, left-adjoined: `t ++ s`). -/
  | merge2 {s t : List T} {x : Base} {γ : List (MGFeature Base Lic)}
      {b : Bool} {ms1 ms2 : List (MGChain Base Lic T)} :
      Derives G ⟨false, ⟨s, MGFeature.sel x :: γ⟩, ms1⟩ →
      Derives G ⟨b, ⟨t, [MGFeature.cat x]⟩, ms2⟩ →
      SMC (ms1 ++ ms2) →
      Derives G ⟨false, ⟨t ++ s, γ⟩, ms1 ++ ms2⟩

  /-- Merge 3 (merging a phrase with remaining features `δ = licensee f :: δ'`; becomes a mover). -/
  | merge3 {s t : List T} {x : Base} {f : Lic}
      {γ δ' : List (MGFeature Base Lic)}
      {b1 b2 : Bool} {ms1 ms2 : List (MGChain Base Lic T)} :
      Derives G ⟨b1, ⟨s, MGFeature.sel x :: γ⟩, ms1⟩ →
      Derives G ⟨b2, ⟨t, MGFeature.cat x :: MGFeature.licensee f :: δ'⟩, ms2⟩ →
      SMC (ms1 ++ ⟨t, MGFeature.licensee f :: δ'⟩ :: ms2) →
      Derives G ⟨false, ⟨s, γ⟩, ms1 ++ ⟨t, MGFeature.licensee f :: δ'⟩ :: ms2⟩

  /-- Move 1 (final landing of a mover checking its last feature `-f`, left-adjoined: `t ++ s`). -/
  | move1 {s t : List T} {f : Lic} {γ : List (MGFeature Base Lic)}
      {ms1 ms2 : List (MGChain Base Lic T)} :
      Derives G ⟨false, ⟨s, MGFeature.licensor f :: γ⟩,
        ms1 ++ ⟨t, [MGFeature.licensee f]⟩ :: ms2⟩ →
      Derives G ⟨false, ⟨t ++ s, γ⟩, ms1 ++ ms2⟩

  /-- Move 2 (non-final movement: `-f` checked, mover retains `licensee f' :: δ'`). -/
  | move2 {s t : List T} {f f' : Lic} {γ δ' : List (MGFeature Base Lic)}
      {ms1 ms2 : List (MGChain Base Lic T)} :
      Derives G ⟨false, ⟨s, MGFeature.licensor f :: γ⟩,
        ms1 ++ ⟨t, MGFeature.licensee f :: MGFeature.licensee f' :: δ'⟩ :: ms2⟩ →
      SMC (ms1 ++ ⟨t, MGFeature.licensee f' :: δ'⟩ :: ms2) →
      Derives G ⟨false, ⟨s, γ⟩, ms1 ++ ⟨t, MGFeature.licensee f' :: δ'⟩ :: ms2⟩

/-- The string language generated by a Minimalist Grammar:
    all strings `w` derivable as a complete `G.start` expression with no remaining movers. -/
def Lang (G : MG Base Lic T) (w : List T) : Prop :=
  ∃ b, Derives G ⟨b, ⟨w, [MGFeature.cat G.start]⟩, []⟩

/-- Helper: removing one element preserves `SMC`. -/
theorem smc_remove {ms1 ms2 : List (MGChain Base Lic T)} {c : MGChain Base Lic T}
    (h : SMC (ms1 ++ c :: ms2)) : SMC (ms1 ++ ms2) := by
  obtain ⟨hall, hnd⟩ := h
  refine ⟨?_, ?_⟩
  · intro x hx
    apply hall x
    rcases List.mem_append.mp hx with h1 | h2
    · exact List.mem_append_left _ h1
    · exact List.mem_append_right _ (List.mem_cons_of_mem c h2)
  · simp only [List.filterMap_append, List.filterMap_cons] at hnd ⊢
    cases hc : c.headLic with
    | none => simpa [hc] using hnd
    | some f =>
      rw [hc] at hnd
      exact List.Nodup.sublist (List.Sublist.append_left (List.sublist_cons_self f _) _) hnd

/-- Every derivable MG expression satisfies the Shortest Move Constraint (`SMC`). -/
theorem Derives.smc {G : MG Base Lic T} {e : MGExpr Base Lic T} (h : Derives G e) :
    SMC e.movers := by
  induction h with
  | lex _ =>
    exact ⟨fun _ h => by simp at h, List.nodup_nil⟩
  | merge1 _ _ _ ih2 => exact ih2
  | merge2 _ _ hsmc _ _ => exact hsmc
  | merge3 _ _ hsmc _ _ => exact hsmc
  | move1 _ ih => exact smc_remove ih
  | move2 _ hsmc _ => exact hsmc

/-- Every chain in a derivable MG expression carries a suffix of some lexical feature list. -/
def isSuffix {α : Type} (s l : List α) : Prop :=
  ∃ p, p ++ s = l

theorem isSuffix_refl {α : Type} (l : List α) : isSuffix l l :=
  ⟨[], rfl⟩

theorem isSuffix_tail {α : Type} {a : α} {s l : List α} (h : isSuffix (a :: s) l) :
    isSuffix s l := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p ++ [a], by simpa [List.append_assoc] using hp⟩

/-- Sub-suffix property of Minimalist Grammars:
    both the head feature stack and every mover's feature stack are suffixes of
    feature lists occurring in `G.lexicon`. -/
theorem Derives.feats_suffix {G : MG Base Lic T} {e : MGExpr Base Lic T} (h : Derives G e) :
    (∃ entry, entry ∈ G.lexicon ∧ isSuffix e.head.feats entry.2) ∧
    (∀ c, c ∈ e.movers → ∃ entry, entry ∈ G.lexicon ∧ isSuffix c.feats entry.2) := by
  induction h with
  | @lex w α hlex =>
    exact ⟨⟨(w, α), hlex, isSuffix_refl α⟩, fun _ hm => by simp at hm⟩
  | merge1 _ _ ih1 ih2 =>
    obtain ⟨⟨e1, he1, hs1⟩, _⟩ := ih1
    exact ⟨⟨e1, he1, isSuffix_tail hs1⟩, ih2.2⟩
  | merge2 _ _ _ ih1 ih2 =>
    obtain ⟨⟨e1, he1, hs1⟩, hm1⟩ := ih1
    refine ⟨⟨e1, he1, isSuffix_tail hs1⟩, ?_⟩
    intro c hc
    rcases List.mem_append.mp hc with h1 | h2
    · exact hm1 c h1
    · exact ih2.2 c h2
  | merge3 _ _ _ ih1 ih2 =>
    obtain ⟨⟨e1, he1, hs1⟩, hm1⟩ := ih1
    obtain ⟨⟨e2, he2, hs2⟩, hm2⟩ := ih2
    refine ⟨⟨e1, he1, isSuffix_tail hs1⟩, ?_⟩
    intro c hc
    rcases List.mem_append.mp hc with h1 | h2
    · exact hm1 c h1
    · rcases List.mem_cons.mp h2 with rfl | h2'
      · exact ⟨e2, he2, isSuffix_tail hs2⟩
      · exact hm2 c h2'
  | move1 _ ih =>
    obtain ⟨⟨e1, he1, hs1⟩, hm⟩ := ih
    refine ⟨⟨e1, he1, isSuffix_tail hs1⟩, ?_⟩
    intro c hc
    apply hm c
    rcases List.mem_append.mp hc with h1 | h2
    · exact List.mem_append_left _ h1
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
  | move2 _ _ ih =>
    obtain ⟨⟨e1, he1, hs1⟩, hm⟩ := ih
    refine ⟨⟨e1, he1, isSuffix_tail hs1⟩, ?_⟩
    intro c hc
    rcases List.mem_append.mp hc with h1 | h2
    · exact hm c (List.mem_append_left _ h1)
    · rcases List.mem_cons.mp h2 with rfl | h2'
      · obtain ⟨e2, he2, hs2⟩ := hm _ (List.mem_append_right _ (List.mem_cons_self ..))
        exact ⟨e2, he2, isSuffix_tail hs2⟩
      · exact hm c (List.mem_append_right _ (List.mem_cons_of_mem _ h2'))

end MG
end FormalLinguistics
