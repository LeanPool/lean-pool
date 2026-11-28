/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

module

public import LeanPool.FormalLinguistics.LambekPentus
public import Mathlib.Computability.ContextFreeGrammar

/-!
# Context-free languages in Mathlib

The list of productions used by the grammar transformations has the same language semantics as
Mathlib's finite set of productions. The equivalences for basic categorial grammars and Lambek
grammars can therefore be used with `Language.IsContextFree`.
-/

@[expose] public section

namespace FormalLinguistics

/-- Identify the transformation grammar symbols with Mathlib’s grammar symbols. -/
def symbolEquiv {N T : Type} : Symbol N T ≃ _root_.Symbol T N where
  toFun
    | .nt n => .nonterminal n
    | .tm t => .terminal t
  invFun
    | .nonterminal n => .nt n
    | .terminal t => .tm t
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl

/-- Read a Mathlib grammar as a list of productions for the grammar transformations. -/
noncomputable def CFG.ofMathlib {T : Type} (G : ContextFreeGrammar T) : CFG G.NT T where
  start := G.initial
  rules := G.rules.toList.map fun rule => (rule.input, rule.output.map symbolEquiv.symm)

/-- Interpret a list-based grammar as a Mathlib grammar, ignoring repeated productions. -/
noncomputable abbrev CFG.toMathlib {N T : Type} (G : CFG N T) : ContextFreeGrammar T :=
  ⟨N, G.start, by
    classical
    exact (G.rules.map fun rule => ⟨rule.1, rule.2.map symbolEquiv⟩).toFinset⟩

private theorem map_encode_decode {N T : Type} (symbols : List (Symbol N T)) :
    (symbols.map symbolEquiv).map symbolEquiv.symm = symbols := by
  simp [List.map_map, Function.comp_def]

private theorem map_decode_encode {N T : Type} (symbols : List (_root_.Symbol T N)) :
    (symbols.map symbolEquiv.symm).map symbolEquiv = symbols := by
  simp [List.map_map, Function.comp_def]

private theorem CFG.produces_map_iff {N T : Type} (G : CFG N T) {u v : List (Symbol N T)} :
    G.toMathlib.Produces (u.map symbolEquiv) (v.map symbolEquiv) ↔ G.Step u v := by
  classical
  constructor
  · rintro ⟨r, hr, rewrites⟩
    change r ∈ (G.rules.map fun rule => (⟨rule.1, rule.2.map symbolEquiv⟩ :
      ContextFreeRule T N)).toFinset at hr
    obtain ⟨⟨A, rhs⟩, hRule, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
    obtain ⟨left, suffix, hp, hq⟩ := rewrites.exists_parts
    change u.map symbolEquiv = left ++ [_root_.Symbol.nonterminal A] ++ suffix at hp
    change v.map symbolEquiv = left ++ rhs.map symbolEquiv ++ suffix at hq
    have hpu := congrArg (List.map symbolEquiv.symm) hp
    have hqv := congrArg (List.map symbolEquiv.symm) hq
    simp only [map_encode_decode, List.map_append, List.map_cons, List.map_nil] at hpu hqv
    rw [hpu, hqv]
    exact .mk _ _ _ _ hRule
  · rintro ⟨left, suffix, rhs, A, hr⟩
    refine ⟨⟨A, rhs.map symbolEquiv⟩, ?_, ?_⟩
    · change _ ∈ (G.rules.map fun rule => (⟨rule.1, rule.2.map symbolEquiv⟩ :
        ContextFreeRule T N)).toFinset
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(A, rhs), hr, rfl⟩)
    · simpa [List.map_append, symbolEquiv] using
        ContextFreeRule.rewrites_of_exists_parts
          (⟨A, rhs.map symbolEquiv⟩ : ContextFreeRule T N)
          (left.map symbolEquiv) (suffix.map symbolEquiv)

private theorem CFG.derives_of_mathlib {N T : Type} (G : CFG N T)
    {u v : List (_root_.Symbol T N)} (h : G.toMathlib.Derives u v) :
    G.Derives (u.map symbolEquiv.symm) (v.map symbolEquiv.symm) := by
  induction h with
  | refl => exact .refl _
  | @tail w x _ step ih =>
    apply CFG.Derives.tail ih
    apply (G.produces_map_iff).mp
    rw [map_decode_encode, map_decode_encode]
    exact step

/-- Applying Mathlib's derivation relation to a converted grammar preserves its language. -/
theorem CFG.mem_toMathlib_language {N T : Type} (G : CFG N T) (w : List T) :
    w ∈ G.toMathlib.language ↔ G.Lang w := by
  change G.toMathlib.Derives [_root_.Symbol.nonterminal G.start] (w.map _root_.Symbol.terminal) ↔
    G.Derives [.nt G.start] (w.map Symbol.tm)
  constructor
  · intro h
    have mapped := G.derives_of_mathlib h
    rw [List.map_map] at mapped
    exact mapped
  · intro h
    have transport {u v : List (Symbol N T)} (h : G.Derives u v) :
        G.toMathlib.Derives (u.map symbolEquiv) (v.map symbolEquiv) := by
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ step ih => exact .tail ih (G.produces_map_iff.mpr step)
    have mapped := transport h
    rw [List.map_map] at mapped
    exact mapped

/-- A Mathlib grammar round-trips through the list presentation. -/
theorem CFG.toMathlib_ofMathlib {T : Type} (G : ContextFreeGrammar T) :
    (CFG.ofMathlib G).toMathlib = G := by
  classical
  cases G with
  | mk N start rules =>
    suffices ((rules.toList.map fun rule => (rule.input, rule.output.map symbolEquiv.symm)).map
        fun rule => (⟨rule.1, rule.2.map symbolEquiv⟩ : ContextFreeRule T N)).toFinset = rules
      from congrArg (ContextFreeGrammar.mk N start) this
    rw [List.map_map]
    change (List.map (fun rule : ContextFreeRule T N =>
      (⟨rule.input, (rule.output.map symbolEquiv.symm).map symbolEquiv⟩ :
        ContextFreeRule T N)) rules.toList).toFinset = rules
    simp

/-- The language recognized by the list presentation of a Mathlib grammar. -/
theorem CFG.ofMathlib_lang {T : Type} (G : ContextFreeGrammar T) (w : List T) :
    (CFG.ofMathlib G).Lang w ↔ w ∈ G.language := by
  rw [← CFG.mem_toMathlib_language, CFG.toMathlib_ofMathlib]

private theorem contextFree_iff {T : Type} (L : Language T) :
    (∃ (N : Type) (_ : DecidableEq N) (G : CFG N T), ∀ w, G.Lang w ↔ w ∈ L) ↔
      L.IsContextFree := by
  classical
  constructor
  · rintro ⟨N, _, G, hG⟩
    exact ⟨G.toMathlib, Set.ext fun w => (G.mem_toMathlib_language w).trans (hG w)⟩
  · rintro ⟨G, rfl⟩
    exact ⟨G.NT, Classical.typeDecidableEq G.NT, CFG.ofMathlib G, CFG.ofMathlib_lang G⟩

/-- Basic categorial grammars recognize precisely the epsilon-free context-free languages. -/
theorem bar_hillel_gaifman_shamir_isContextFree {T : Type} (L : Language T) :
    (∃ (P : Type) (G : ABG P T), ∀ w, G.Lang w ↔ w ∈ L) ↔
      L.IsContextFree ∧ [] ∉ L := by
  classical
  exact (bar_hillel_gaifman_shamir (· ∈ L)).trans ((contextFree_iff L).and Iff.rfl)

/-- Product Lambek grammars recognize precisely the epsilon-free context-free languages. -/
theorem chomsky_pentus_isContextFree {T : Type} (L : Language T) :
    IsLambekLang (· ∈ L) ↔ L.IsContextFree ∧ [] ∉ L := by
  classical
  exact (chomsky_pentus (· ∈ L)).trans ((contextFree_iff L).and Iff.rfl)

end FormalLinguistics
