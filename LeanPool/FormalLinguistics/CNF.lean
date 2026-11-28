/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import LeanPool.FormalLinguistics.CFG
public import LeanPool.FormalLinguistics.Fixpoint

/-!
  Chomsky Normal Form (Chomsky, 1959)
  Complete computable pipeline: CFG → BinCFG → NoEpsCFG → CNF,
  preserving all non-empty strings (`CNF.Lang w ↔ CFG.Lang w ∧ w ≠ []`).
-/

@[expose] public section

namespace FormalLinguistics

/-! ### Stage 1: Binarized CFG (all RHS have length ≤ 2, terminals isolated) -/

/-- An original nonterminal, a lifted terminal, or a symbol naming a rule suffix. -/
inductive BinNT (N T : Type) where
  | orig : N → BinNT N T
  | tm : T → BinNT N T
  | tail : List (Symbol N T) → BinNT N T
  deriving DecidableEq, Repr

/-- A grammar whose productions have only empty, terminal, unary, or binary right-hand sides. -/
structure BinCFG (N T : Type) where
  /-- Start nonterminal of the binarized grammar. -/
  start : N
  /-- Sources of productions with an empty right-hand side. -/
  epsRules : List N
  /-- Terminal productions, encoded as a source and a terminal. -/
  termRules : List (N × T)
  /-- Unary productions, encoded as a source and a replacement nonterminal. -/
  unitRules : List (N × N)
  /-- Binary productions, encoded as a source and two replacement nonterminals. -/
  binRules : List (N × N × N)

namespace BinCFG

variable {N T : Type}

/-- Parse-tree derivations for the four forms of binarized productions. -/
inductive Yield (G : BinCFG N T) : N → List T → Prop where
  | eps {A : N} : A ∈ G.epsRules → Yield G A []
  | tm {A : N} {a : T} : (A, a) ∈ G.termRules → Yield G A [a]
  | unit {A B : N} {w : List T} : (A, B) ∈ G.unitRules → Yield G B w → Yield G A w
  | bin {A B C : N} {w1 w2 : List T} :
      (A, B, C) ∈ G.binRules → Yield G B w1 → Yield G C w2 → Yield G A (w1 ++ w2)

end BinCFG

namespace CFGtoBin

variable {N T : Type}

/-- Lift each symbol to the corresponding nonterminal of the binarized grammar. -/
def symNT : Symbol N T → BinNT N T
  | Symbol.nt A => BinNT.orig A
  | Symbol.tm a => BinNT.tm a

/-- Binary rules generated when expanding a tail of length ≥ 2. -/
def tailBinRules : List (Symbol N T) → List (BinNT N T × BinNT N T × BinNT N T)
  | [] => []
  | [_] => []
  | [s1, s2] => [(BinNT.tail [s1, s2], symNT s1, symNT s2)]
  | s1 :: s2 :: s3 :: rest =>
    (BinNT.tail (s1 :: s2 :: s3 :: rest), symNT s1, BinNT.tail (s2 :: s3 :: rest)) ::
      tailBinRules (s2 :: s3 :: rest)

/-- Encode a right-hand side of length at least two as a chain of binary productions. -/
def ruleBinRules (A : N) : List (Symbol N T) → List (BinNT N T × BinNT N T × BinNT N T)
  | [] => []
  | [_] => []
  | [s1, s2] => [(BinNT.orig A, symNT s1, symNT s2)]
  | s1 :: s2 :: s3 :: rest =>
    (BinNT.orig A, symNT s1, BinNT.tail (s2 :: s3 :: rest)) ::
      tailBinRules (s2 :: s3 :: rest)

/-- Collect the terminal symbols occurring in a right-hand side. -/
def rhsTerminals (rhs : List (Symbol N T)) : List T :=
  rhs.filterMap fun
    | Symbol.tm a => some a
    | Symbol.nt _ => none

/-- Binarize a context-free grammar by introducing names for terminals and rule suffixes. -/
def toBinCFG (G : CFG N T) : BinCFG (BinNT N T) T where
  start := BinNT.orig G.start
  epsRules := G.rules.filterMap fun (A, rhs) =>
    match rhs with
    | [] => some (BinNT.orig A)
    | _ => none
  termRules :=
    (G.rules.filterMap fun (A, rhs) =>
      match rhs with
      | [Symbol.tm a] => some (BinNT.orig A, a)
      | _ => none) ++
    (G.rules.flatMap fun (_, rhs) => (rhsTerminals rhs).map fun a => (BinNT.tm a, a))
  unitRules := G.rules.filterMap fun (A, rhs) =>
    match rhs with
    | [Symbol.nt B] => some (BinNT.orig A, BinNT.orig B)
    | _ => none
  binRules := G.rules.flatMap fun (A, rhs) => ruleBinRules A rhs

theorem tailBinRules_sound {rhs : List (Symbol N T)} {X Y Z : BinNT N T}
    (h : (X, Y, Z) ∈ tailBinRules rhs) :
    (∃ s1 s2, X = BinNT.tail [s1, s2] ∧ Y = symNT s1 ∧ Z = symNT s2) ∨
    (∃ s1 s2 s3 rest, X = BinNT.tail (s1 :: s2 :: s3 :: rest) ∧
      Y = symNT s1 ∧ Z = BinNT.tail (s2 :: s3 :: rest)) := by
  match rhs with
  | [] => simp [tailBinRules] at h
  | [_] => simp [tailBinRules] at h
  | [s1, s2] =>
    simp [tailBinRules] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    left; exact ⟨s1, s2, rfl, rfl, rfl⟩
  | s1 :: s2 :: s3 :: rest =>
    simp only [tailBinRules, List.mem_cons] at h
    rcases h with h1 | h2
    · obtain ⟨rfl, rfl, rfl⟩ := h1
      right; exact ⟨s1, s2, s3, rest, rfl, rfl, rfl⟩
    · exact tailBinRules_sound h2

theorem ruleBinRules_sound {A : N} {rhs : List (Symbol N T)} {X Y Z : BinNT N T}
    (h : (X, Y, Z) ∈ ruleBinRules A rhs) :
    (X = BinNT.orig A ∧
      ((∃ s1 s2, rhs = [s1, s2] ∧ Y = symNT s1 ∧ Z = symNT s2) ∨
       (∃ s1 s2 s3 rest, rhs = s1 :: s2 :: s3 :: rest ∧
         Y = symNT s1 ∧ Z = BinNT.tail (s2 :: s3 :: rest)))) ∨
    (∃ s1 s2, X = BinNT.tail [s1, s2] ∧ Y = symNT s1 ∧ Z = symNT s2) ∨
    (∃ s1 s2 s3 rest, X = BinNT.tail (s1 :: s2 :: s3 :: rest) ∧
      Y = symNT s1 ∧ Z = BinNT.tail (s2 :: s3 :: rest)) := by
  match rhs with
  | [] => simp [ruleBinRules] at h
  | [_] => simp [ruleBinRules] at h
  | [s1, s2] =>
    simp [ruleBinRules] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    left; exact ⟨rfl, Or.inl ⟨s1, s2, rfl, rfl, rfl⟩⟩
  | s1 :: s2 :: s3 :: rest =>
    simp only [ruleBinRules, List.mem_cons] at h
    rcases h with h1 | h2
    · obtain ⟨rfl, rfl, rfl⟩ := h1
      left; exact ⟨rfl, Or.inr ⟨s1, s2, s3, rest, rfl, rfl, rfl⟩⟩
    · right; exact tailBinRules_sound h2

/-- Interpret lifted nonterminals, terminal names, and rule suffixes as their original yields. -/
def interp (G : CFG N T) : BinNT N T → List T → Prop
  | BinNT.orig A, w => CFG.Yield G A w
  | BinNT.tm a, w => w = [a]
  | BinNT.tail rhs, w => CFG.YieldList G rhs w

theorem interp_symNT {G : CFG N T} {s : Symbol N T} {w : List T}
    (h : interp G (symNT s) w) : CFG.YieldList G [s] w := by
  cases s with
  | nt A => simpa using CFG.YieldList.cons_nt h CFG.YieldList.nil
  | tm a =>
    simp [symNT, interp] at h
    subst h
    exact CFG.YieldList.cons_tm CFG.YieldList.nil

theorem toBinCFG_sound {G : CFG N T} {X : BinNT N T} {w : List T}
    (h : BinCFG.Yield (toBinCFG G) X w) : interp G X w := by
  induction h with
  | @eps X hmem =>
    simp [toBinCFG] at hmem
    obtain ⟨A, rhs, hr, hmatch⟩ := hmem
    cases rhs with
    | nil =>
      simp at hmatch; subst hmatch
      exact CFG.Yield.rule hr CFG.YieldList.nil
    | cons _ _ => simp at hmatch
  | @tm X a hmem =>
    simp [toBinCFG] at hmem
    rcases hmem with ⟨A, rhs, hr, hmatch⟩ | ⟨A, rhs, _, ha, rfl, rfl⟩
    · cases rhs with
      | nil => simp at hmatch
      | cons s t =>
        cases s with
        | nt _ => simp at hmatch
        | tm b =>
          cases t with
          | nil =>
            simp at hmatch; obtain ⟨rfl, rfl⟩ := hmatch
            exact CFG.Yield.rule hr (CFG.YieldList.cons_tm CFG.YieldList.nil)
          | cons _ _ => simp at hmatch
    · rfl
  | @unit X Y w hmem _ ih =>
    simp [toBinCFG] at hmem
    obtain ⟨A, rhs, hr, hmatch⟩ := hmem
    cases rhs with
    | nil => simp at hmatch
    | cons s t =>
      cases s with
      | tm _ => simp at hmatch
      | nt B =>
        cases t with
        | nil =>
          simp at hmatch; obtain ⟨rfl, rfl⟩ := hmatch
          exact CFG.Yield.rule hr (by simpa using CFG.YieldList.cons_nt ih CFG.YieldList.nil)
        | cons _ _ => simp at hmatch
  | @bin X Y Z w1 w2 hmem _ _ ih1 ih2 =>
    simp [toBinCFG] at hmem
    obtain ⟨A, rhs, hr, hrb⟩ := hmem
    rcases ruleBinRules_sound hrb with
      ⟨rfl, ⟨s1, s2, rfl, rfl, rfl⟩ | ⟨s1, s2, s3, rest, rfl, rfl, rfl⟩⟩ |
      ⟨s1, s2, rfl, rfl, rfl⟩ |
      ⟨s1, s2, s3, rest, rfl, rfl, rfl⟩
    · exact CFG.Yield.rule hr (by simpa using CFG.YieldList.append (interp_symNT ih1) (interp_symNT ih2))
    · exact CFG.Yield.rule hr (by simpa using CFG.YieldList.append (interp_symNT ih1) ih2)
    · simpa [interp] using CFG.YieldList.append (interp_symNT ih1) (interp_symNT ih2)
    · simpa [interp] using CFG.YieldList.append (interp_symNT ih1) ih2

theorem mem_rhsTerminals {a : T} {rhs : List (Symbol N T)} (h : Symbol.tm a ∈ rhs) :
    a ∈ rhsTerminals rhs := by
  induction rhs with
  | nil => simp at h
  | cons s t ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · simp [rhsTerminals]
    · simp only [rhsTerminals, List.filterMap_cons]
      cases s with
      | tm b => exact List.mem_cons_of_mem b (ih ht)
      | nt B => exact ih ht

theorem term_yield_of_mem {G : CFG N T} {A : N} {rhs : List (Symbol N T)} {a : T}
    (hr : (A, rhs) ∈ G.rules) (ha : Symbol.tm a ∈ rhs) :
    BinCFG.Yield (toBinCFG G) (BinNT.tm a) [a] := by
  apply BinCFG.Yield.tm
  simp [toBinCFG]
  right
  exact ⟨A, rhs, hr, mem_rhsTerminals ha⟩

/-- Helper inductive capturing `YieldList` where every NT has already been translated into `BinCFG.Yield`. -/
inductive YieldListBin (BG : BinCFG (BinNT N T) T) : List (Symbol N T) → List T → Prop where
  | nil : YieldListBin BG [] []
  | cons_tm {a : T} {rhs : List (Symbol N T)} {w : List T} :
      YieldListBin BG rhs w → YieldListBin BG (Symbol.tm a :: rhs) (a :: w)
  | cons_nt {B : N} {rhs : List (Symbol N T)} {w1 w2 : List T} :
      BinCFG.Yield BG (BinNT.orig B) w1 → YieldListBin BG rhs w2 →
      YieldListBin BG (Symbol.nt B :: rhs) (w1 ++ w2)

theorem yieldListBin_head {G : CFG N T} {s : Symbol N T} {rhs : List (Symbol N T)} {w : List T}
    (h : YieldListBin (toBinCFG G) (s :: rhs) w)
    (htm : ∀ a, s = Symbol.tm a → BinCFG.Yield (toBinCFG G) (BinNT.tm a) [a]) :
    ∃ w1 w2, w = w1 ++ w2 ∧
      BinCFG.Yield (toBinCFG G) (symNT s) w1 ∧
      YieldListBin (toBinCFG G) rhs w2 := by
  cases s with
  | tm a =>
    cases h with
    | cons_tm hrest =>
      exact ⟨[a], _, rfl, htm a rfl, hrest⟩
  | nt B =>
    cases h with
    | cons_nt hy hrest =>
      exact ⟨_, _, rfl, hy, hrest⟩

theorem yieldListBin_tail {G : CFG N T} {A0 : N} {rhs0 : List (Symbol N T)}
    (hr0 : (A0, rhs0) ∈ G.rules) :
    ∀ rhs w,
      (∀ s, s ∈ rhs → s ∈ rhs0) →
      (∀ r, r ∈ tailBinRules rhs → r ∈ (toBinCFG G).binRules) →
      YieldListBin (toBinCFG G) rhs w →
      rhs.length ≥ 2 →
      BinCFG.Yield (toBinCFG G) (BinNT.tail rhs) w := by
  intro rhs
  induction rhs with
  | nil => intro _ _ _ _ hlen; simp at hlen
  | cons s1 t ih =>
    intro w hsub hrules hyl hlen
    cases t with
    | nil => simp at hlen
    | cons s2 t2 =>
      cases t2 with
      | nil =>
        have hbin : (BinNT.tail [s1, s2], symNT s1, symNT s2) ∈ (toBinCFG G).binRules :=
          hrules _ (by simp [tailBinRules])
        obtain ⟨w1, w23, hw1, hy1, hrest1⟩ := yieldListBin_head hyl (fun a ha =>
          term_yield_of_mem hr0 (hsub (Symbol.tm a) (by simp [ha])))
        obtain ⟨w2, w3, hw2, hy2, hrest2⟩ := yieldListBin_head hrest1 (fun a ha =>
          term_yield_of_mem hr0 (hsub (Symbol.tm a) (by simp [ha])))
        cases hrest2
        rw [hw1, hw2, List.append_nil]
        exact BinCFG.Yield.bin hbin hy1 hy2
      | cons s3 rest =>
        have hbin : (BinNT.tail (s1 :: s2 :: s3 :: rest), symNT s1, BinNT.tail (s2 :: s3 :: rest)) ∈
            (toBinCFG G).binRules :=
          hrules _ (by simp [tailBinRules])
        obtain ⟨w1, w2, hw1, hy1, hrest1⟩ := yieldListBin_head hyl (fun a ha =>
          term_yield_of_mem hr0 (hsub (Symbol.tm a) (by simp [ha])))
        have htail := ih w2
          (fun s hs => hsub s (List.mem_cons_of_mem s1 hs))
          (fun r hr => hrules r (by simp [tailBinRules, hr]))
          hrest1 (by simp)
        rw [hw1]
        exact BinCFG.Yield.bin hbin hy1 htail

mutual
  theorem toBinCFG_complete {G : CFG N T} {A : N} {w : List T} :
      CFG.Yield G A w → BinCFG.Yield (toBinCFG G) (BinNT.orig A) w
    | CFG.Yield.rule (rhs := rhs) hr hyl_raw =>
      let hyl := toBinCFG_complete_list hyl_raw
      match rhs, hyl with
      | [], YieldListBin.nil =>
        BinCFG.Yield.eps (by
          simp [toBinCFG]
          exact ⟨A, [], hr, rfl⟩)
      | [Symbol.tm a], YieldListBin.cons_tm YieldListBin.nil =>
        BinCFG.Yield.tm (by
          simp [toBinCFG]
          exact ⟨A, [Symbol.tm a], hr, rfl⟩)
      | [Symbol.nt B], YieldListBin.cons_nt hy YieldListBin.nil => by
        rw [List.append_nil]
        apply BinCFG.Yield.unit _ hy
        simp [toBinCFG]
        exact ⟨A, [Symbol.nt B], hr, rfl⟩
      | [s1, s2], hyl => by
        have hbin : (BinNT.orig A, symNT s1, symNT s2) ∈ (toBinCFG G).binRules := by
          simp [toBinCFG]
          exact ⟨A, [s1, s2], hr, by simp [ruleBinRules]⟩
        obtain ⟨w1, w23, hw1, hy1, hrest1⟩ := yieldListBin_head hyl (fun a ha =>
          term_yield_of_mem hr (by simp [ha]))
        obtain ⟨w2, w3, hw2, hy2, hrest2⟩ := yieldListBin_head hrest1 (fun a ha =>
          term_yield_of_mem hr (by simp [ha]))
        cases hrest2
        rw [hw1, hw2, List.append_nil]
        exact BinCFG.Yield.bin hbin hy1 hy2
      | s1 :: s2 :: s3 :: rest, hyl => by
        have hbin : (BinNT.orig A, symNT s1, BinNT.tail (s2 :: s3 :: rest)) ∈ (toBinCFG G).binRules := by
          simp [toBinCFG]
          exact ⟨A, s1 :: s2 :: s3 :: rest, hr, by simp [ruleBinRules]⟩
        obtain ⟨w1, w2, hw1, hy1, hrest1⟩ := yieldListBin_head hyl (fun a ha =>
          term_yield_of_mem hr (by simp [ha]))
        have htail_rules : ∀ r, r ∈ tailBinRules (s2 :: s3 :: rest) → r ∈ (toBinCFG G).binRules := by
          intro r hrm
          simp [toBinCFG]
          exact ⟨A, s1 :: s2 :: s3 :: rest, hr, by simp [ruleBinRules, hrm]⟩
        have htail := yieldListBin_tail hr (s2 :: s3 :: rest) w2
          (fun s hs => List.mem_cons_of_mem s1 hs)
          htail_rules hrest1 (by simp)
        rw [hw1]
        exact BinCFG.Yield.bin hbin hy1 htail

  theorem toBinCFG_complete_list {G : CFG N T} {rhs : List (Symbol N T)} {w : List T} :
      CFG.YieldList G rhs w → YieldListBin (toBinCFG G) rhs w
    | CFG.YieldList.nil => YieldListBin.nil
    | CFG.YieldList.cons_tm h => YieldListBin.cons_tm (toBinCFG_complete_list h)
    | CFG.YieldList.cons_nt hy hyl =>
      YieldListBin.cons_nt (toBinCFG_complete hy) (toBinCFG_complete_list hyl)
end

theorem toBinCFG_yield_iff (G : CFG N T) (A : N) (w : List T) :
    BinCFG.Yield (toBinCFG G) (BinNT.orig A) w ↔ CFG.Yield G A w :=
  ⟨toBinCFG_sound, toBinCFG_complete⟩

end CFGtoBin

/-! ### Stage 2: Eliminating ε-rules (`BinCFG → NoEpsCFG`) -/

/-- A binarized grammar with terminal, unary, and binary productions. -/
structure NoEpsCFG (N T : Type) where
  /-- Start nonterminal of the epsilon-free grammar. -/
  start : N
  /-- Terminal productions of the epsilon-free grammar. -/
  termRules : List (N × T)
  /-- Unary productions of the epsilon-free grammar. -/
  unitRules : List (N × N)
  /-- Binary productions of the epsilon-free grammar. -/
  binRules : List (N × N × N)

namespace NoEpsCFG

variable {N T : Type}

/-- Parse-tree derivations in an epsilon-free binarized grammar. -/
inductive Yield (G : NoEpsCFG N T) : N → List T → Prop where
  | tm {A : N} {a : T} : (A, a) ∈ G.termRules → Yield G A [a]
  | unit {A B : N} {w : List T} : (A, B) ∈ G.unitRules → Yield G B w → Yield G A w
  | bin {A B C : N} {w1 w2 : List T} :
      (A, B, C) ∈ G.binRules → Yield G B w1 → Yield G C w2 → Yield G A (w1 ++ w2)

theorem yield_nonempty {G : NoEpsCFG N T} {A : N} {w : List T} (h : Yield G A w) : w ≠ [] := by
  induction h with
  | tm _ => simp
  | unit _ _ ih => exact ih
  | bin _ _ _ ih1 _ =>
    intro hnil
    exact ih1 (List.append_eq_nil_iff.mp hnil).1

end NoEpsCFG

namespace BinToNoEps

variable {N T : Type} [DecidableEq N]

/-- List the start symbol and all nonterminals occurring in the rules. -/
def allNTsRaw (G : BinCFG N T) : List N :=
  G.start ::
    (G.epsRules ++
     G.termRules.map Prod.fst ++
     G.unitRules.flatMap (fun (A, B) => [A, B]) ++
     G.binRules.flatMap (fun (A, B, C) => [A, B, C]))

/-- Enumerate the nonterminals that appear in the grammar, without repetition. -/
def allNTs (G : BinCFG N T) : List N :=
  dedupList (allNTsRaw G)

/-- Test whether one step can establish nullability using already nullable nonterminals. -/
def nullPred (G : BinCFG N T) (s : List N) (A : N) : Bool :=
  (A ∈ s) ||
  (A ∈ G.epsRules) ||
  G.unitRules.any (fun (X, Y) => X == A && Y ∈ s) ||
  G.binRules.any (fun (X, Y, Z) => X == A && Y ∈ s && Z ∈ s)

/-- Compute the nullability fixed point by bounded iteration over the finite symbol list. -/
def nullableList (G : BinCFG N T) : List N :=
  iterN (stepFilter (allNTs G) (nullPred G)) (allNTs G).length []

theorem nullPred_mono (G : BinCFG N T) :
    ∀ s1 s2, (∀ x, x ∈ s1 → x ∈ s2) → ∀ x, nullPred G s1 x = true → nullPred G s2 x = true := by
  intro s1 s2 hsub x hx
  simp only [nullPred, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq] at hx ⊢
  rcases hx with ((h1 | h2) | ⟨⟨X, Y⟩, hm, rfl, hy⟩) | ⟨⟨X, Y, Z⟩, hm, ⟨rfl, hy⟩, hz⟩
  · left; left; left; exact hsub x h1
  · left; left; right; exact h2
  · left; right; exact ⟨(X, Y), hm, rfl, hsub Y hy⟩
  · right; exact ⟨(X, Y, Z), hm, ⟨rfl, hsub Y hy⟩, hsub Z hz⟩

theorem nullPred_infl (G : BinCFG N T) :
    ∀ s x, x ∈ s → x ∈ allNTs G → nullPred G s x = true := by
  intro s x hx _
  simp [nullPred, hx]

theorem nullableList_sound {G : BinCFG N T} {A : N} (h : A ∈ nullableList G) :
    BinCFG.Yield G A [] := by
  apply fixpoint_sound (Q := fun X => BinCFG.Yield G X []) _ (allNTs G).length [] (by simp) A h
  intro s hs x _ hpx
  simp only [nullPred, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq] at hpx
  rcases hpx with ((h1 | h2) | ⟨⟨X, Y⟩, hm, rfl, hy⟩) | ⟨⟨X, Y, Z⟩, hm, ⟨rfl, hy⟩, hz⟩
  · exact hs x h1
  · exact BinCFG.Yield.eps h2
  · exact BinCFG.Yield.unit hm (hs Y hy)
  · simpa using BinCFG.Yield.bin hm (hs Y hy) (hs Z hz)

theorem mem_allNTs_of_eps {G : BinCFG N T} {A : N} (h : A ∈ G.epsRules) : A ∈ allNTs G := by
  rw [allNTs, mem_dedupList]
  simp [allNTsRaw, h]

theorem mem_allNTs_of_unit_left {G : BinCFG N T} {A B : N} (h : (A, B) ∈ G.unitRules) :
    A ∈ allNTs G := by
  rw [allNTs, mem_dedupList]
  simp only [allNTsRaw, List.mem_cons, List.mem_append, List.mem_flatMap]
  right; left; right
  exact ⟨(A, B), h, by simp⟩

theorem mem_allNTs_of_bin_left {G : BinCFG N T} {A B C : N} (h : (A, B, C) ∈ G.binRules) :
    A ∈ allNTs G := by
  rw [allNTs, mem_dedupList]
  simp only [allNTsRaw, List.mem_cons, List.mem_append, List.mem_flatMap]
  right; right
  exact ⟨(A, B, C), h, by simp⟩

theorem nullableList_complete {G : BinCFG N T} {A : N} (h : BinCFG.Yield G A []) :
    A ∈ nullableList G := by
  generalize hw : ([] : List T) = w at h
  induction h with
  | @eps X heps =>
    apply fixpoint_closed (nodup_dedupList _) (nullPred_mono G) (nullPred_infl G) X
      (mem_allNTs_of_eps heps)
    simp [nullPred, heps]
  | tm _ => simp at hw
  | @unit X Y w' hu _ ih =>
    have hY := ih hw
    apply fixpoint_closed (nodup_dedupList _) (nullPred_mono G) (nullPred_infl G) X
      (mem_allNTs_of_unit_left hu)
    simp only [nullPred, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq]
    left; right
    exact ⟨(X, Y), hu, rfl, hY⟩
  | @bin X Y Z w1 w2 hb _ _ ih1 ih2 =>
    have ⟨h1, h2⟩ := List.append_eq_nil_iff.mp hw.symm
    have hY := ih1 h1.symm
    have hZ := ih2 h2.symm
    apply fixpoint_closed (nodup_dedupList _) (nullPred_mono G) (nullPred_infl G) X
      (mem_allNTs_of_bin_left hb)
    simp only [nullPred, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq]
    right
    exact ⟨(X, Y, Z), hb, ⟨rfl, hY⟩, hZ⟩

/-- Remove empty productions, adding unary rules when a binary child can disappear. -/
def toNoEps (G : BinCFG N T) : NoEpsCFG N T where
  start := G.start
  termRules := G.termRules
  unitRules :=
    G.unitRules ++
    (G.binRules.filterMap fun (A, B, C) =>
      if B ∈ nullableList G then some (A, C) else none) ++
    (G.binRules.filterMap fun (A, B, C) =>
      if C ∈ nullableList G then some (A, B) else none)
  binRules := G.binRules

theorem toNoEps_sound {G : BinCFG N T} {A : N} {w : List T}
    (h : NoEpsCFG.Yield (toNoEps G) A w) : BinCFG.Yield G A w ∧ w ≠ [] := by
  refine ⟨?_, NoEpsCFG.yield_nonempty h⟩
  induction h with
  | tm htm => exact BinCFG.Yield.tm htm
  | @unit A B w hu _ ih =>
    simp only [toNoEps, List.mem_append, List.mem_filterMap] at hu
    rcases hu with (hu1 | ⟨⟨X, Y, Z⟩, hb, hif⟩) | ⟨⟨X, Y, Z⟩, hb, hif⟩
    · exact BinCFG.Yield.unit hu1 ih
    · split at hif
      · next hnull =>
        simp at hif; obtain ⟨rfl, rfl⟩ := hif
        simpa using BinCFG.Yield.bin hb (nullableList_sound hnull) ih
      · simp at hif
    · split at hif
      · next hnull =>
        simp at hif; obtain ⟨rfl, rfl⟩ := hif
        simpa using BinCFG.Yield.bin hb ih (nullableList_sound hnull)
      · simp at hif
  | bin hb _ _ ih1 ih2 =>
    exact BinCFG.Yield.bin hb ih1 ih2

theorem toNoEps_complete {G : BinCFG N T} {A : N} {w : List T}
    (h : BinCFG.Yield G A w) (hne : w ≠ []) : NoEpsCFG.Yield (toNoEps G) A w := by
  induction h with
  | eps _ => exact absurd rfl hne
  | tm htm => exact NoEpsCFG.Yield.tm htm
  | @unit A B w' hu _ ih =>
    have hu' : (A, B) ∈ (toNoEps G).unitRules := by
      simp [toNoEps, hu]
    exact NoEpsCFG.Yield.unit hu' (ih hne)
  | @bin A B C w1 w2 hb hB hC ih1 ih2 =>
    by_cases hw1 : w1 = []
    · subst hw1
      simp at hne
      have hnull : B ∈ nullableList G := nullableList_complete hB
      have hu : (A, C) ∈ (toNoEps G).unitRules := by
        simp only [toNoEps, List.mem_append, List.mem_filterMap]
        left; right
        exact ⟨(A, B, C), hb, by simp [hnull]⟩
      simpa using NoEpsCFG.Yield.unit hu (ih2 hne)
    · by_cases hw2 : w2 = []
      · subst hw2
        simp at hne
        have hnull : C ∈ nullableList G := nullableList_complete hC
        have hu : (A, B) ∈ (toNoEps G).unitRules := by
          simp only [toNoEps, List.mem_append, List.mem_filterMap]
          right
          exact ⟨(A, B, C), hb, by simp [hnull]⟩
        simpa using NoEpsCFG.Yield.unit hu (ih1 hne)
      · exact NoEpsCFG.Yield.bin hb (ih1 hw1) (ih2 hw2)

theorem toNoEps_yield_iff (G : BinCFG N T) (A : N) (w : List T) :
    NoEpsCFG.Yield (toNoEps G) A w ↔ BinCFG.Yield G A w ∧ w ≠ [] :=
  ⟨toNoEps_sound, fun ⟨h, hne⟩ => toNoEps_complete h hne⟩

end BinToNoEps

/-! ### Stage 3: Eliminating unit rules (`NoEpsCFG → CNF`) -/

/-- A Context-Free Grammar in Chomsky Normal Form:
    every rule is either `A → a` (`termRules`) or `A → B C` (`binRules`). -/
structure CNF (N T : Type) where
  /-- Start nonterminal of the grammar in Chomsky normal form. -/
  start : N
  /-- Productions whose right-hand side consists of one terminal. -/
  termRules : List (N × T)
  /-- Productions whose right-hand side consists of two nonterminals. -/
  binRules : List (N × N × N)

namespace CNF

variable {N T : Type}

/-- Parse-tree derivations in epsilon-free Chomsky normal form. -/
inductive Yield (G : CNF N T) : N → List T → Prop where
  | tm {A : N} {a : T} : (A, a) ∈ G.termRules → Yield G A [a]
  | bin {A B C : N} {w1 w2 : List T} :
      (A, B, C) ∈ G.binRules → Yield G B w1 → Yield G C w2 → Yield G A (w1 ++ w2)

/-- Words derived from the start nonterminal in Chomsky normal form. -/
def Lang (G : CNF N T) (w : List T) : Prop :=
  Yield G G.start w

end CNF

namespace NoEpsToCNF

variable {N T : Type} [DecidableEq N]

/-- Reflexive transitive closure of the unary productions. -/
inductive UnitStar (G : NoEpsCFG N T) : N → N → Prop where
  | refl (A : N) : UnitStar G A A
  | step {A B C : N} : (A, B) ∈ G.unitRules → UnitStar G B C → UnitStar G A C

/-- List the start symbol and the nonterminals occurring in the epsilon-free rules. -/
def allNTsRaw (G : NoEpsCFG N T) : List N :=
  G.start ::
    (G.termRules.map Prod.fst ++
     G.unitRules.flatMap (fun (A, B) => [A, B]) ++
     G.binRules.flatMap (fun (A, B, C) => [A, B, C]))

/-- Enumerate the nonterminals used by the epsilon-free grammar. -/
def allNTs (G : NoEpsCFG N T) : List N :=
  dedupList (allNTsRaw G)

/-- Enumerate ordered pairs of nonterminals that can participate in a unary path. -/
def allPairs (G : NoEpsCFG N T) : List (N × N) :=
  dedupList ((allNTs G).flatMap fun A => (allNTs G).map fun B => (A, B))

/-- Test whether a pair is reflexive, a direct unary rule, or reachable by extending a known path.
-/
def unitPred (G : NoEpsCFG N T) (s : List (N × N)) (p : N × N) : Bool :=
  (p ∈ s) ||
  (p.1 == p.2) ||
  G.unitRules.any (fun (X, Y) => X == p.1 && (Y, p.2) ∈ s)

/-- Compute all unary paths by bounded finite fixed-point iteration. -/
def unitReach (G : NoEpsCFG N T) : List (N × N) :=
  iterN (stepFilter (allPairs G) (unitPred G)) (allPairs G).length []

theorem unitPred_mono (G : NoEpsCFG N T) :
    ∀ s1 s2, (∀ x, x ∈ s1 → x ∈ s2) → ∀ x, unitPred G s1 x = true → unitPred G s2 x = true := by
  intro s1 s2 hsub ⟨A, B⟩ hx
  simp only [unitPred, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq] at hx ⊢
  rcases hx with (h1 | h2) | ⟨⟨X, Y⟩, hu, rfl, hy⟩
  · left; left; exact hsub (A, B) h1
  · left; right; exact h2
  · right; exact ⟨(X, Y), hu, rfl, hsub (Y, B) hy⟩

theorem unitPred_infl (G : NoEpsCFG N T) :
    ∀ s x, x ∈ s → x ∈ allPairs G → unitPred G s x = true := by
  intro s x hx _
  simp [unitPred, hx]

theorem unitReach_sound {G : NoEpsCFG N T} {A B : N} (h : (A, B) ∈ unitReach G) :
    UnitStar G A B := by
  apply fixpoint_sound (Q := fun p => UnitStar G p.1 p.2) _ (allPairs G).length [] (by simp) (A, B) h
  intro s hs ⟨X, Y⟩ _ hpx
  simp only [unitPred, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq] at hpx
  rcases hpx with (h1 | h2) | ⟨⟨U, V⟩, hu, hUX, hVY⟩
  · exact hs (X, Y) h1
  · subst h2; exact UnitStar.refl X
  · subst hUX; exact UnitStar.step hu (hs (V, Y) hVY)

theorem mem_allPairs {G : NoEpsCFG N T} {A B : N}
    (hA : A ∈ allNTs G) (hB : B ∈ allNTs G) : (A, B) ∈ allPairs G := by
  rw [allPairs, mem_dedupList]
  exact List.mem_flatMap.mpr ⟨A, hA, List.mem_map.mpr ⟨B, hB, rfl⟩⟩

theorem mem_allNTs_of_term {G : NoEpsCFG N T} {A : N} {a : T} (h : (A, a) ∈ G.termRules) :
    A ∈ allNTs G := by
  rw [allNTs, mem_dedupList]
  simp only [allNTsRaw, List.mem_cons, List.mem_append, List.mem_map]
  right; left; left
  exact ⟨(A, a), h, rfl⟩

theorem mem_allNTs_of_unit_left {G : NoEpsCFG N T} {A B : N} (h : (A, B) ∈ G.unitRules) :
    A ∈ allNTs G := by
  rw [allNTs, mem_dedupList]
  simp only [allNTsRaw, List.mem_cons, List.mem_append, List.mem_flatMap]
  right; left; right
  exact ⟨(A, B), h, by simp⟩

theorem mem_allNTs_of_bin_left {G : NoEpsCFG N T} {A B C : N} (h : (A, B, C) ∈ G.binRules) :
    A ∈ allNTs G := by
  rw [allNTs, mem_dedupList]
  simp only [allNTsRaw, List.mem_cons, List.mem_append, List.mem_flatMap]
  right; right
  exact ⟨(A, B, C), h, by simp⟩

theorem unitReach_complete {G : NoEpsCFG N T} {A B : N}
    (h : UnitStar G A B) (hB : B ∈ allNTs G) : (A, B) ∈ unitReach G := by
  induction h with
  | refl X =>
    apply fixpoint_closed (nodup_dedupList _) (unitPred_mono G) (unitPred_infl G) (X, X)
      (mem_allPairs hB hB)
    simp [unitPred]
  | @step X Y Z hu _ ih =>
    have hYZ := ih hB
    have hX : X ∈ allNTs G := mem_allNTs_of_unit_left hu
    apply fixpoint_closed (nodup_dedupList _) (unitPred_mono G) (unitPred_infl G) (X, Z)
      (mem_allPairs hX hB)
    simp only [unitPred, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq]
    right
    exact ⟨(X, Y), hu, rfl, hYZ⟩

/-- Eliminate unary productions by copying terminal and binary rules along unary paths. -/
def toCNF (G : NoEpsCFG N T) : CNF N T where
  start := G.start
  termRules := (unitReach G).flatMap fun (A, B) =>
    G.termRules.filterMap fun (B', a) => if B' = B then some (A, a) else none
  binRules := (unitReach G).flatMap fun (A, B) =>
    G.binRules.filterMap fun (B', C, D) => if B' = B then some (A, C, D) else none

omit [DecidableEq N] in
theorem yield_of_unitStar {G : NoEpsCFG N T} {A B : N} {w : List T}
    (hu : UnitStar G A B) (hy : NoEpsCFG.Yield G B w) : NoEpsCFG.Yield G A w := by
  induction hu with
  | refl _ => exact hy
  | step hstep _ ih => exact NoEpsCFG.Yield.unit hstep (ih hy)

theorem toCNF_sound {G : NoEpsCFG N T} {A : N} {w : List T}
    (h : CNF.Yield (toCNF G) A w) : NoEpsCFG.Yield G A w := by
  induction h with
  | @tm A a htm =>
    simp only [toCNF, List.mem_flatMap, List.mem_filterMap] at htm
    obtain ⟨⟨X, B⟩, hreach, ⟨B', a'⟩, htmG, hif⟩ := htm
    split at hif
    · next hEq =>
      simp at hif; obtain ⟨rfl, rfl⟩ := hif; subst hEq
      exact yield_of_unitStar (unitReach_sound hreach) (NoEpsCFG.Yield.tm htmG)
    · simp at hif
  | @bin A C D w1 w2 hb _ _ ih1 ih2 =>
    simp only [toCNF, List.mem_flatMap, List.mem_filterMap] at hb
    obtain ⟨⟨X, B⟩, hreach, ⟨B', C', D'⟩, hbG, hif⟩ := hb
    split at hif
    · next hEq =>
      simp at hif; obtain ⟨rfl, rfl, rfl⟩ := hif; subst hEq
      exact yield_of_unitStar (unitReach_sound hreach) (NoEpsCFG.Yield.bin hbG ih1 ih2)
    · simp at hif

theorem toCNF_complete_aux {G : NoEpsCFG N T} {A B : N} {w : List T}
    (hu : UnitStar G A B) (hy : NoEpsCFG.Yield G B w) : CNF.Yield (toCNF G) A w := by
  induction hy generalizing A with
  | @tm X a htm =>
    have hreach := unitReach_complete hu (mem_allNTs_of_term htm)
    apply CNF.Yield.tm
    simp only [toCNF, List.mem_flatMap, List.mem_filterMap]
    exact ⟨(A, X), hreach, (X, a), htm, by simp⟩
  | @unit X Y w' hstep _ ih =>
    exact ih (by
      clear ih
      induction hu with
      | refl _ => exact UnitStar.step hstep (UnitStar.refl _)
      | step h1 _ ihu => exact UnitStar.step h1 (ihu hstep))
  | @bin X C D w1 w2 hb _ _ ih1 ih2 =>
    have hreach := unitReach_complete hu (mem_allNTs_of_bin_left hb)
    have hb' : (A, C, D) ∈ (toCNF G).binRules := by
      simp only [toCNF, List.mem_flatMap, List.mem_filterMap]
      exact ⟨(A, X), hreach, (X, C, D), hb, by simp⟩
    exact CNF.Yield.bin hb' (ih1 (UnitStar.refl C)) (ih2 (UnitStar.refl D))

theorem toCNF_yield_iff (G : NoEpsCFG N T) (A : N) (w : List T) :
    CNF.Yield (toCNF G) A w ↔ NoEpsCFG.Yield G A w :=
  ⟨toCNF_sound, toCNF_complete_aux (UnitStar.refl A)⟩

end NoEpsToCNF

/-! ### Full CFG → CNF Conversion Theorem -/

/-- Convert any finite Context-Free Grammar into Chomsky Normal Form. -/
def cfgToCNF [DecidableEq N] [DecidableEq T] (G : CFG N T) : CNF (BinNT N T) T :=
  NoEpsToCNF.toCNF (BinToNoEps.toNoEps (CFGtoBin.toBinCFG G))

/-- Chomsky Normal Form Theorem:
    For any finite CFG `G`, `cfgToCNF G` generates exactly the non-empty strings of `G`. -/
theorem cfgToCNF_lang [DecidableEq N] [DecidableEq T] (G : CFG N T) (w : List T) :
    (cfgToCNF G).Lang w ↔ G.Lang w ∧ w ≠ [] := by
  unfold CNF.Lang cfgToCNF
  rw [NoEpsToCNF.toCNF_yield_iff, BinToNoEps.toNoEps_yield_iff]
  change BinCFG.Yield (CFGtoBin.toBinCFG G) (BinNT.orig G.start) w ∧ w ≠ [] ↔ G.Lang w ∧ w ≠ []
  rw [CFGtoBin.toBinCFG_yield_iff, CFG.lang_iff_yield]

end FormalLinguistics
