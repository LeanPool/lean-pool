/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import LeanPool.FormalLinguistics.GNF
public import LeanPool.FormalLinguistics.ABG

/-!
  2-Standard Greibach Normal Form → AB Categorial Grammar
  (the hard direction of Bar-Hillel, Gaifman & Shamir 1960, reached here via Greibach normal form)
  Every rule in 2-GNF maps directly to a lexical category of slash-depth ≤ 2:
    • U → a       ↦  (a, atom U)
    • U → a V     ↦  (a, atom U / atom V)
    • U → a V W   ↦  (a, (atom U / atom W) / atom V)
-/

@[expose] public section

namespace FormalLinguistics

namespace GNFtoABG

variable {N T : Type}

/-- Give each Greibach-normal-form rule a categorial lexical entry headed by its terminal. -/
def toABG (G : GNF2 N T) : ABG N T where
  distinguished := G.start
  lexicon :=
    (G.rules0.map fun (U, a) => (a, Cat.atom U)) ++
    (G.rules1.map fun (U, a, V) => (a, Cat.rslash (Cat.atom U) (Cat.atom V))) ++
    (G.rules2.map fun (U, a, V, W) =>
      (a, Cat.rslash (Cat.rslash (Cat.atom U) (Cat.atom W)) (Cat.atom V)))

/-- Every category in `(toABG G).lexicon` is one of the 3 right-slash shapes of depth ≤ 2. -/
theorem lex_shapes {G : GNF2 N T} {a : T} {C : Cat N} (h : (a, C) ∈ (toABG G).lexicon) :
    (∃ U, C = Cat.atom U ∧ (U, a) ∈ G.rules0) ∨
    (∃ U V, C = Cat.rslash (Cat.atom U) (Cat.atom V) ∧ (U, a, V) ∈ G.rules1) ∨
    (∃ U V W, C = Cat.rslash (Cat.rslash (Cat.atom U) (Cat.atom W)) (Cat.atom V) ∧
      (U, a, V, W) ∈ G.rules2) := by
  simp only [toABG, List.mem_append, List.mem_map] at h
  rcases h with (⟨⟨U, a'⟩, hr, heq⟩ | ⟨⟨U, a', V⟩, hr, heq⟩) | ⟨⟨U, a', V, W⟩, hr, heq⟩
  · simp at heq; obtain ⟨rfl, rfl⟩ := heq
    left; exact ⟨U, rfl, hr⟩
  · simp at heq; obtain ⟨rfl, rfl⟩ := heq
    right; left; exact ⟨U, V, rfl, hr⟩
  · simp at heq; obtain ⟨rfl, rfl⟩ := heq
    right; right; exact ⟨U, V, W, rfl, hr⟩

/-- Semantic invariant for all derivable ABTrees in `toABG G`:
    - No `lslash` category is ever derivable.
    - No category of depth ≥ 3 is ever derivable.
    - Depth-2 `((U / W) / V)` only comes directly from a `rules2` lexical item.
    - Depth-1 `(U / W)` comes either from a `rules1` lexical item or a `rules2` item applied to `V`.
    - Depth-0 `(U)` yields a valid `GNF2.Yield G U w`. -/
def treeInv (G : GNF2 N T) : Cat N → List T → Prop
  | Cat.atom U, w => GNF2.Yield G U w
  | Cat.rslash (Cat.atom U) (Cat.atom W), w =>
      (∃ a, w = [a] ∧ (U, a, W) ∈ G.rules1) ∨
      (∃ a V wv, w = a :: wv ∧ (U, a, V, W) ∈ G.rules2 ∧ GNF2.Yield G V wv)
  | Cat.rslash (Cat.rslash (Cat.atom U) (Cat.atom W)) (Cat.atom V), w =>
      ∃ a, w = [a] ∧ (U, a, V, W) ∈ G.rules2
  | _, _ => False

theorem toABG_sound_inv {G : GNF2 N T} {C : Cat N} {w : List T}
    (h : ABG.ABTree (toABG G) C w) : treeInv G C w := by
  induction h with
  | @lex a C hlex =>
    rcases lex_shapes hlex with
      ⟨U, rfl, hr⟩ | ⟨U, V, rfl, hr⟩ | ⟨U, V, W, rfl, hr⟩
    · exact GNF2.Yield.r0 hr
    · left; exact ⟨a, rfl, hr⟩
    · exact ⟨a, rfl, hr⟩
  | @fwd A B w1 w2 _ _ ih1 ih2 =>
    cases A with
    | atom U =>
      cases B with
      | atom W =>
        rcases ih1 with ⟨a, rfl, hr1⟩ | ⟨a, V, wv, rfl, hr2, hV⟩
        · exact GNF2.Yield.r1 hr1 ih2
        · exact GNF2.Yield.r2 hr2 hV ih2
      | rslash _ _ => simp [treeInv] at ih1
      | lslash _ _ => simp [treeInv] at ih1
    | rslash A1 A2 =>
      cases A1 with
      | atom U =>
        cases A2 with
        | atom W =>
          cases B with
          | atom V =>
            obtain ⟨a, rfl, hr2⟩ := ih1
            right; exact ⟨a, V, w2, rfl, hr2, ih2⟩
          | rslash _ _ => simp [treeInv] at ih1
          | lslash _ _ => simp [treeInv] at ih1
        | rslash _ _ => simp [treeInv] at ih1
        | lslash _ _ => simp [treeInv] at ih1
      | rslash _ _ => simp [treeInv] at ih1
      | lslash _ _ => simp [treeInv] at ih1
    | lslash _ _ => simp [treeInv] at ih1
  | @bwd A B w1 w2 _ _ _ ih2 =>
    simp [treeInv] at ih2

theorem toABG_complete {G : GNF2 N T} {U : N} {w : List T}
    (h : GNF2.Yield G U w) : ABG.ABTree (toABG G) (Cat.atom U) w := by
  induction h with
  | @r0 U a hr =>
    apply ABG.ABTree.lex
    simp only [toABG, List.mem_append, List.mem_map]
    left; left
    exact ⟨(U, a), hr, rfl⟩
  | @r1 U V a w hr _ ih =>
    have hlex : ABG.ABTree (toABG G) (Cat.rslash (Cat.atom U) (Cat.atom V)) [a] := by
      apply ABG.ABTree.lex
      simp only [toABG, List.mem_append, List.mem_map]
      left; right
      exact ⟨(U, a, V), hr, rfl⟩
    exact ABG.ABTree.fwd hlex ih
  | @r2 U V W a w1 w2 hr _ _ ih1 ih2 =>
    have hlex : ABG.ABTree (toABG G)
        (Cat.rslash (Cat.rslash (Cat.atom U) (Cat.atom W)) (Cat.atom V)) [a] := by
      apply ABG.ABTree.lex
      simp only [toABG, List.mem_append, List.mem_map]
      right
      exact ⟨(U, a, V, W), hr, rfl⟩
    have h1 : ABG.ABTree (toABG G) (Cat.rslash (Cat.atom U) (Cat.atom W)) (a :: w1) :=
      ABG.ABTree.fwd hlex ih1
    simpa [List.cons_append] using ABG.ABTree.fwd h1 ih2

theorem toABG_lang (G : GNF2 N T) (w : List T) :
    (toABG G).Lang w ↔ G.Lang w := by
  rw [ABG.lang_iff_abtree]
  exact ⟨toABG_sound_inv, toABG_complete⟩

end GNFtoABG
end FormalLinguistics
