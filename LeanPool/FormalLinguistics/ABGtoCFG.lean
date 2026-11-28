/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import LeanPool.FormalLinguistics.CFG
public import LeanPool.FormalLinguistics.ABG

/-!
  Direction 1 of Bar-Hillel, Gaifman & Shamir (1960):
  Every AB Basic Categorial Grammar has a weakly equivalent Context-Free Grammar.
-/

@[expose] public section

namespace FormalLinguistics

namespace Cat

variable {P : Type}

/-- All sub-categories (subformulas) of a category `C`. -/
def subcats : Cat P → List (Cat P)
  | Cat.atom p => [Cat.atom p]
  | Cat.rslash A B => Cat.rslash A B :: (subcats A ++ subcats B)
  | Cat.lslash B A => Cat.lslash B A :: (subcats B ++ subcats A)

theorem mem_subcats_self (C : Cat P) : C ∈ C.subcats := by
  cases C <;> simp [subcats]

theorem subcats_trans {C D E : Cat P} (h1 : C ∈ D.subcats) (h2 : D ∈ E.subcats) :
    C ∈ E.subcats := by
  induction E with
  | atom p =>
    simp [subcats] at h2
    subst h2
    exact h1
  | rslash A B ihA ihB =>
    simp [subcats] at h2
    rcases h2 with rfl | hA | hB
    · exact h1
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihA hA))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihB hB))
  | lslash B A ihB ihA =>
    simp [subcats] at h2
    rcases h2 with rfl | hB | hA
    · exact h1
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihB hB))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihA hA))

theorem rslash_mem_subcats_left {A B E : Cat P} (h : Cat.rslash A B ∈ E.subcats) :
    A ∈ E.subcats :=
  subcats_trans (D := Cat.rslash A B)
    (List.mem_cons_of_mem _ (List.mem_append_left _ (mem_subcats_self A))) h

theorem lslash_mem_subcats_right {B A E : Cat P} (h : Cat.lslash B A ∈ E.subcats) :
    A ∈ E.subcats :=
  subcats_trans (D := Cat.lslash B A)
    (List.mem_cons_of_mem _ (List.mem_append_right _ (mem_subcats_self A))) h

end Cat

namespace ABG

variable {P T : Type}

/-- Finite list of all sub-categories appearing in the lexicon of `G`. -/
def allSubcats (G : ABG P T) : List (Cat P) :=
  G.lexicon.flatMap (fun entry => entry.2.subcats)

/-- Subformula property: every category derivable by an `ABTree` is a lexical sub-category. -/
theorem ABTree.mem_allSubcats {G : ABG P T} {C : Cat P} {w : List T}
    (h : ABTree G C w) : C ∈ G.allSubcats := by
  induction h with
  | @lex a c ha =>
    exact List.mem_flatMap.mpr ⟨(a, c), ha, Cat.mem_subcats_self c⟩
  | @fwd A B w1 w2 _ _ ih1 _ =>
    obtain ⟨entry, hentry, hsub⟩ := List.mem_flatMap.mp ih1
    exact List.mem_flatMap.mpr ⟨entry, hentry, Cat.rslash_mem_subcats_left hsub⟩
  | @bwd A B w1 w2 _ _ _ ih2 =>
    obtain ⟨entry, hentry, hsub⟩ := List.mem_flatMap.mp ih2
    exact List.mem_flatMap.mpr ⟨entry, hentry, Cat.lslash_mem_subcats_right hsub⟩

/-- Convert a finite AB Categorial Grammar into a finite Context-Free Grammar. -/
def toCFG (G : ABG P T) : CFG (Cat P) T where
  start := Cat.atom G.distinguished
  rules :=
    (G.lexicon.map fun entry => (entry.2, [Symbol.tm entry.1])) ++
    (G.allSubcats.filterMap fun c =>
      match c with
      | Cat.rslash A B => some (A, [Symbol.nt (Cat.rslash A B), Symbol.nt B])
      | Cat.lslash B A => some (A, [Symbol.nt B, Symbol.nt (Cat.lslash B A)])
      | Cat.atom _ => none)

/-- Helper list-level predicate for mutual structural recursion on `CFG.Yield` / `CFG.YieldList`. -/
inductive ABYieldList (G : ABG P T) : List (Symbol (Cat P) T) → List T → Prop where
  | nil : ABYieldList G [] []
  | cons_tm {a : T} {rhs : List (Symbol (Cat P) T)} {w : List T} :
      ABYieldList G rhs w → ABYieldList G (Symbol.tm a :: rhs) (a :: w)
  | cons_nt {C : Cat P} {rhs : List (Symbol (Cat P) T)} {w1 w2 : List T} :
      ABTree G C w1 → ABYieldList G rhs w2 → ABYieldList G (Symbol.nt C :: rhs) (w1 ++ w2)

mutual
  theorem toCFG_sound {G : ABG P T} {C : Cat P} {w : List T} :
      CFG.Yield (G.toCFG) C w → ABTree G C w
    | CFG.Yield.rule hr hyl_raw => by
      have hyl := toCFG_sound_list hyl_raw
      simp [toCFG] at hr
      rcases hr with ⟨a, c, hlex, rfl, rfl⟩ | ⟨c, hsub, hmatch⟩
      · cases hyl with
        | cons_tm hnil =>
          cases hnil
          exact ABTree.lex hlex
      · cases c with
        | atom p => simp at hmatch
        | rslash X Y =>
          simp at hmatch
          obtain ⟨rfl, rfl⟩ := hmatch
          cases hyl with
          | cons_nt h1 hrest =>
            cases hrest with
            | cons_nt h2 hnil =>
              cases hnil
              simpa using ABTree.fwd h1 h2
        | lslash Y X =>
          simp at hmatch
          obtain ⟨rfl, rfl⟩ := hmatch
          cases hyl with
          | cons_nt h1 hrest =>
            cases hrest with
            | cons_nt h2 hnil =>
              cases hnil
              simpa using ABTree.bwd h1 h2

  theorem toCFG_sound_list {G : ABG P T} {α : List (Symbol (Cat P) T)} {w : List T} :
      CFG.YieldList (G.toCFG) α w → ABYieldList G α w
    | CFG.YieldList.nil => ABYieldList.nil
    | CFG.YieldList.cons_tm h => ABYieldList.cons_tm (toCFG_sound_list h)
    | CFG.YieldList.cons_nt hy hyl =>
      ABYieldList.cons_nt (toCFG_sound hy) (toCFG_sound_list hyl)
end

theorem toCFG_complete {G : ABG P T} {C : Cat P} {w : List T}
    (h : ABTree G C w) : CFG.Yield (G.toCFG) C w := by
  induction h with
  | @lex a c ha =>
    have hr : (c, [Symbol.tm a]) ∈ G.toCFG.rules := by
      simp [toCFG]
      left
      exact ⟨a, c, ha, rfl, rfl⟩
    exact CFG.Yield.rule hr (CFG.YieldList.cons_tm CFG.YieldList.nil)
  | @fwd A B w1 w2 h1 h2 ih1 ih2 =>
    have hsub : Cat.rslash A B ∈ G.allSubcats := h1.mem_allSubcats
    have hr : (A, [Symbol.nt (Cat.rslash A B), Symbol.nt B]) ∈ G.toCFG.rules := by
      simp [toCFG]
      exact ⟨Cat.rslash A B, hsub, rfl⟩
    have hyl : CFG.YieldList (G.toCFG) [Symbol.nt (Cat.rslash A B), Symbol.nt B] (w1 ++ w2) := by
      simpa using CFG.YieldList.cons_nt ih1 (CFG.YieldList.cons_nt ih2 CFG.YieldList.nil)
    exact CFG.Yield.rule hr hyl
  | @bwd A B w1 w2 h1 h2 ih1 ih2 =>
    have hsub : Cat.lslash B A ∈ G.allSubcats := h2.mem_allSubcats
    have hr : (A, [Symbol.nt B, Symbol.nt (Cat.lslash B A)]) ∈ G.toCFG.rules := by
      simp [toCFG]
      exact ⟨Cat.lslash B A, hsub, rfl⟩
    have hyl : CFG.YieldList (G.toCFG) [Symbol.nt B, Symbol.nt (Cat.lslash B A)] (w1 ++ w2) := by
      simpa using CFG.YieldList.cons_nt ih1 (CFG.YieldList.cons_nt ih2 CFG.YieldList.nil)
    exact CFG.Yield.rule hr hyl

/-- Bar-Hillel, Gaifman & Shamir (1960), Direction 1:
    Every AB Categorial Grammar generates a context-free language. -/
theorem toCFG_lang (G : ABG P T) (w : List T) :
    G.toCFG.Lang w ↔ G.Lang w := by
  rw [CFG.lang_iff_yield, ABG.lang_iff_abtree]
  exact ⟨toCFG_sound, toCFG_complete⟩

end ABG
end FormalLinguistics
