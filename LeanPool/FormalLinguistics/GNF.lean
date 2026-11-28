/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import LeanPool.FormalLinguistics.CNF

/-!
  2-Standard Greibach Normal Form via a left-corner construction
  (in the tradition of Rosenkrantz 1967 and Rosenkrantz & Lewis 1970; cf. Blum & Koch 1999)
  Every CNF grammar is converted into an equivalent 2-GNF grammar whose rules all have the shape:
    • U → a
    • U → a V
    • U → a V W
  Every proof is pure structural induction / length induction — zero nonterminal ordering hacks.
-/

@[expose] public section

namespace FormalLinguistics

/-- A grammar in 2-Standard Greibach Normal Form (each rule starts with a terminal
    followed by 0, 1, or 2 nonterminals). -/
structure GNF2 (N T : Type) where
  /-- Start nonterminal. -/
  start : N
  /-- Productions with a terminal and no trailing nonterminal. -/
  rules0 : List (N × T)           -- U → a
  /-- Productions with a terminal followed by one nonterminal. -/
  rules1 : List (N × T × N)       -- U → a V
  /-- Productions with a terminal followed by two nonterminals. -/
  rules2 : List (N × T × N × N)   -- U → a V W

namespace GNF2

variable {N T : Type}

/-- Parse-tree derivations in binary Greibach normal form. -/
inductive Yield (G : GNF2 N T) : N → List T → Prop where
  | r0 {U : N} {a : T} :
      (U, a) ∈ G.rules0 → Yield G U [a]
  | r1 {U V : N} {a : T} {w : List T} :
      (U, a, V) ∈ G.rules1 → Yield G V w → Yield G U (a :: w)
  | r2 {U V W : N} {a : T} {w1 w2 : List T} :
      (U, a, V, W) ∈ G.rules2 → Yield G V w1 → Yield G W w2 → Yield G U (a :: (w1 ++ w2))

/-- Words derivable from the start nonterminal in binary Greibach normal form. -/
def Lang (G : GNF2 N T) (w : List T) : Prop :=
  Yield G G.start w

end GNF2

/-- Nonterminals of the left-corner construction:
    `orig A` represents `A`;
    `diff A X` represents the suffix remaining to the right of a left-corner `X` inside an `A`-tree. -/
inductive GNFNT (N : Type) where
  | orig : N → GNFNT N
  | diff : N → N → GNFNT N
  deriving DecidableEq, Repr

namespace CNFtoGNF

variable {N T : Type}

/-- Left-spine relation in CNF: `LeftChain G A X w` means `A ⇒⁺ X w` along the left spine. -/
inductive LeftChain (G : CNF N T) : N → N → List T → Prop where
  | one {A X Y : N} {w : List T} :
      (A, X, Y) ∈ G.binRules → CNF.Yield G Y w → LeftChain G A X w
  | step {A P X Y : N} {w1 w2 : List T} :
      LeftChain G A P w2 → (P, X, Y) ∈ G.binRules → CNF.Yield G Y w1 →
      LeftChain G A X (w1 ++ w2)

theorem cnf_yield_pos {G : CNF N T} {A : N} {w : List T} (h : CNF.Yield G A w) :
    0 < w.length := by
  induction h with
  | tm _ => simp
  | bin _ _ _ ih1 ih2 => simp; omega

theorem leftChain_pos {G : CNF N T} {A X : N} {w : List T} (h : LeftChain G A X w) :
    0 < w.length := by
  induction h with
  | one _ hy => exact cnf_yield_pos hy
  | step _ _ hy _ =>
    have h1 := cnf_yield_pos hy
    simp; omega

theorem leftChain_snoc {G : CNF N T} {A B C X : N} {w1 w2 : List T}
    (hb : (A, B, C) ∈ G.binRules) (hC : CNF.Yield G C w2) (hlc : LeftChain G B X w1) :
    LeftChain G A X (w1 ++ w2) := by
  induction hlc with
  | one hB hY =>
    exact LeftChain.step (LeftChain.one hb hC) hB hY
  | step _ hP hY ih =>
    simpa [List.append_assoc] using LeftChain.step ih hP hY

/-- Every CNF parse tree decomposes along its leftmost spine into either a direct terminal rule
    or a leftmost terminal leaf `X → a` plus a `LeftChain G A X w'`. -/
theorem cnf_yield_split {G : CNF N T} {A : N} {w : List T} (h : CNF.Yield G A w) :
    (∃ a, (A, a) ∈ G.termRules ∧ w = [a]) ∨
    (∃ X a w', (X, a) ∈ G.termRules ∧ LeftChain G A X w' ∧ w = a :: w') := by
  induction h with
  | @tm A a htm =>
    left; exact ⟨a, htm, rfl⟩
  | @bin A B C w1 w2 hb _ hC ihB _ =>
    rcases ihB with ⟨a, htmB, rfl⟩ | ⟨X, a, w1', htmX, hlc, rfl⟩
    · right
      exact ⟨B, a, w2, htmB, LeftChain.one hb hC, rfl⟩
    · right
      exact ⟨X, a, w1' ++ w2, htmX, leftChain_snoc hb hC hlc, rfl⟩

/-- Plugging a `CNF.Yield G X wx` into the left-corner hole of `LeftChain G A X w` yields `CNF.Yield G A (wx ++ w)`. -/
theorem cnf_yield_of_leftChain_yield {G : CNF N T} {A X : N} {wx w : List T}
    (hlc : LeftChain G A X w) (hx : CNF.Yield G X wx) :
    CNF.Yield G A (wx ++ w) := by
  induction hlc generalizing wx with
  | one hb hY =>
    exact CNF.Yield.bin hb hx hY
  | step _ hP hY ih =>
    have hP_yield : CNF.Yield G _ (wx ++ _) := CNF.Yield.bin hP hx hY
    simpa [List.append_assoc] using ih hP_yield

theorem cnf_yield_of_leftChain {G : CNF N T} {A X : N} {a : T} {w : List T}
    (htm : (X, a) ∈ G.termRules) (hlc : LeftChain G A X w) :
    CNF.Yield G A (a :: w) :=
  cnf_yield_of_leftChain_yield hlc (CNF.Yield.tm htm)

/-- Finite list of all nonterminals appearing as LHS of a binary rule in `G`. -/
def allBinLHS (G : CNF N T) : List N :=
  G.binRules.map fun (A, _, _) => A

theorem leftChain_mem_allBinLHS {G : CNF N T} {A X : N} {w : List T}
    (hlc : LeftChain G A X w) : A ∈ allBinLHS G := by
  induction hlc with
  | @one X Y _ hb _ =>
    exact List.mem_map.mpr ⟨(A, X, Y), hb, rfl⟩
  | step _ _ _ ih => exact ih

/-- The left-corner construction: CNF → 2-Standard GNF. -/
def cnfToGNF [DecidableEq N] (G : CNF N T) : GNF2 (GNFNT N) T where
  start := GNFNT.orig G.start
  -- Rule 1: orig A → a   (when A → a)
  -- Rule 3: diff A X → b (when A → X Y and Y → b)
  rules0 :=
    (G.termRules.map fun (A, a) => (GNFNT.orig A, a)) ++
    (G.binRules.flatMap fun (A, X, Y) =>
      G.termRules.filterMap fun (Y', b) =>
        if Y' = Y then some (GNFNT.diff A X, b) else none)
  -- Rule 2: orig A → a (diff A X)       (when X → a, A ∈ allBinLHS G)
  -- Rule 4: diff A X → b (diff Y Z)     (when A → X Y and Z → b)
  -- Rule 5: diff A X → b (diff A P)     (when P → X Y, Y → b, A ∈ allBinLHS G)
  rules1 :=
    ((allBinLHS G).flatMap fun A =>
      G.termRules.map fun (X, a) => (GNFNT.orig A, a, GNFNT.diff A X)) ++
    (G.binRules.flatMap fun (A, X, Y) =>
      G.termRules.map fun (Z, b) => (GNFNT.diff A X, b, GNFNT.diff Y Z)) ++
    ((allBinLHS G).flatMap fun A =>
      G.binRules.flatMap fun (P, X, Y) =>
        G.termRules.filterMap fun (Y', b) =>
          if Y' = Y then some (GNFNT.diff A X, b, GNFNT.diff A P) else none)
  -- Rule 6: diff A X → b (diff Y Z) (diff A P) (when P → X Y, Z → b, A ∈ allBinLHS G)
  rules2 :=
    (allBinLHS G).flatMap fun A =>
      G.binRules.flatMap fun (P, X, Y) =>
        G.termRules.map fun (Z, b) =>
          (GNFNT.diff A X, b, GNFNT.diff Y Z, GNFNT.diff A P)

/-- Semantic interpretation of `GNFNT N` back in the CNF grammar `G`. -/
def interp (G : CNF N T) : GNFNT N → List T → Prop
  | GNFNT.orig A, w => CNF.Yield G A w
  | GNFNT.diff A X, w => LeftChain G A X w

theorem cnfToGNF_sound [DecidableEq N] {G : CNF N T} {U : GNFNT N} {w : List T}
    (h : GNF2.Yield (cnfToGNF G) U w) : interp G U w := by
  induction h with
  | @r0 U a hr =>
    simp only [cnfToGNF, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filterMap] at hr
    rcases hr with ⟨⟨A, a'⟩, htm, heq⟩ | ⟨⟨A, X, Y⟩, hb, ⟨Y', b⟩, htm, hif⟩
    · simp at heq; obtain ⟨rfl, rfl⟩ := heq
      exact CNF.Yield.tm htm
    · split at hif
      · next hEq =>
        simp at hif; obtain ⟨rfl, rfl⟩ := hif; subst hEq
        exact LeftChain.one hb (CNF.Yield.tm htm)
      · simp at hif
  | @r1 U V a w hr _ ih =>
    simp only [cnfToGNF, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap] at hr
    rcases hr with
      (⟨A, _, ⟨X, a'⟩, htm, heq⟩ | ⟨⟨A, X, Y⟩, hb, ⟨Z, b⟩, htm, heq⟩) |
      ⟨A, _, ⟨P, X, Y⟩, hb, ⟨Y', b⟩, htm, hif⟩
    · simp at heq; obtain ⟨rfl, rfl, rfl⟩ := heq
      exact cnf_yield_of_leftChain htm ih
    · simp at heq; obtain ⟨rfl, rfl, rfl⟩ := heq
      exact LeftChain.one hb (cnf_yield_of_leftChain htm ih)
    · split at hif
      · next hEq =>
        simp at hif; obtain ⟨rfl, rfl, rfl⟩ := hif; subst hEq
        exact LeftChain.step ih hb (CNF.Yield.tm htm)
      · simp at hif
  | @r2 U V W a w1 w2 hr _ _ ih1 ih2 =>
    simp only [cnfToGNF, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨A, _, ⟨P, X, Y⟩, hb, ⟨Z, b⟩, htm, heq⟩ := hr
    simp at heq; obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    have hY : CNF.Yield G Y (b :: w1) := cnf_yield_of_leftChain htm ih1
    exact LeftChain.step ih2 hb hY

/-- Strong induction on string length proves completeness of `diff A X` for all `LeftChain`s! -/
theorem cnfToGNF_complete_leftChain [DecidableEq N] {G : CNF N T} :
    ∀ n (A X : N) (w : List T), w.length ≤ n → LeftChain G A X w →
      GNF2.Yield (cnfToGNF G) (GNFNT.diff A X) w := by
  intro n
  induction n with
  | zero =>
    intro A X w hlen hlc
    have hpos := leftChain_pos hlc
    omega
  | succ n ih =>
    intro A X w hlen hlc
    have hA_in : A ∈ allBinLHS G := leftChain_mem_allBinLHS hlc
    cases hlc with
    | @one X Y w hb hY =>
      rcases cnf_yield_split hY with ⟨b, htmY, rfl⟩ | ⟨Z, b, w', htmZ, hlcY, rfl⟩
      · -- Rule 3: diff A X → b
        apply GNF2.Yield.r0
        simp only [cnfToGNF, List.mem_append, List.mem_flatMap, List.mem_filterMap]
        right
        exact ⟨(A, X, Y), hb, (Y, b), htmY, by simp⟩
      · -- Rule 4: diff A X → b (diff Y Z)
        have hlen' : w'.length ≤ n := by simp at hlen; omega
        have hYZ := ih Y Z w' hlen' hlcY
        apply GNF2.Yield.r1 _ hYZ
        simp only [cnfToGNF, List.mem_append, List.mem_flatMap, List.mem_map]
        left; right
        exact ⟨(A, X, Y), hb, (Z, b), htmZ, rfl⟩
    | @step P X Y w1 w2 hlcAP hb hY =>
      have hpos1 : 0 < w1.length := cnf_yield_pos hY
      have hpos2 : 0 < w2.length := leftChain_pos hlcAP
      have hlen2 : w2.length ≤ n := by simp at hlen; omega
      have hAP := ih A P w2 hlen2 hlcAP
      rcases cnf_yield_split hY with ⟨b, htmY, rfl⟩ | ⟨Z, b, w1', htmZ, hlcY, rfl⟩
      · -- Rule 5: diff A X → b (diff A P)
        apply GNF2.Yield.r1 _ hAP
        simp only [cnfToGNF, List.mem_append, List.mem_flatMap, List.mem_filterMap]
        right
        exact ⟨A, hA_in, (P, X, Y), hb, (Y, b), htmY, by simp⟩
      · -- Rule 6: diff A X → b (diff Y Z) (diff A P)
        have hlen1' : w1'.length ≤ n := by simp at hlen; omega
        have hYZ := ih Y Z w1' hlen1' hlcY
        apply GNF2.Yield.r2 _ hYZ hAP
        simp only [cnfToGNF, List.mem_flatMap, List.mem_map]
        exact ⟨A, hA_in, (P, X, Y), hb, (Z, b), htmZ, rfl⟩

theorem cnfToGNF_complete [DecidableEq N] {G : CNF N T} {A : N} {w : List T}
    (h : CNF.Yield G A w) : GNF2.Yield (cnfToGNF G) (GNFNT.orig A) w := by
  rcases cnf_yield_split h with ⟨a, htmA, rfl⟩ | ⟨X, a, w', htmX, hlc, rfl⟩
  · -- Rule 1: orig A → a
    apply GNF2.Yield.r0
    simp only [cnfToGNF, List.mem_append, List.mem_map]
    left
    exact ⟨(A, a), htmA, rfl⟩
  · -- Rule 2: orig A → a (diff A X)
    have hA_in : A ∈ allBinLHS G := leftChain_mem_allBinLHS hlc
    have hdiff := cnfToGNF_complete_leftChain w'.length A X w' (Nat.le_refl _) hlc
    apply GNF2.Yield.r1 _ hdiff
    simp only [cnfToGNF, List.mem_append, List.mem_flatMap, List.mem_map]
    left; left
    exact ⟨A, hA_in, (X, a), htmX, rfl⟩

/-- 2-GNF theorem: `cnfToGNF G` generates the exact same language as `G`. -/
theorem cnfToGNF_lang [DecidableEq N] (G : CNF N T) (w : List T) :
    (cnfToGNF G).Lang w ↔ G.Lang w :=
  ⟨cnfToGNF_sound, cnfToGNF_complete⟩

end CNFtoGNF
end FormalLinguistics
