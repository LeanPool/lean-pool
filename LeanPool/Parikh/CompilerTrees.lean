/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.CompilerSupport
public import LeanPool.Parikh.BoundedEnumeration

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# Executable base and cycle families

Enumerate declared finite syntax, filter the accepted predicates, and remove
only duplicate trees. Unused symbols are allowed. Cycle heights use the exact
active alphabet, matching the general grammar formula.
Source: `lem:finite`, `sec:effective`.
-/
namespace Parikh
namespace EncodedGrammar

/-- The existing active alphabet computed from the finite input syntax. -/
@[expose] def activeLabels (g : EncodedGrammar) : Finset (Fin (g.extraNonterminalCount + 1)) :=
  {g.initial} ∪ g.rules.toFinset.biUnion (fun r =>
    {r.input} ∪ (r.output.filterMap fun s => match s with
      | .terminal _ => none
      | .nonterminal A => some A).toFinset)

theorem activeLabels_eq (g : EncodedGrammar) :
    g.activeLabels = activeNonterminals g.decode := by
  classical
  unfold activeLabels activeNonterminals
  have heq : (fun a b : g.decode.NT => Classical.propDecidable (a = b)) =
      instDecidableEqFin (g.extraNonterminalCount + 1) := Subsingleton.elim _ _
  rw [heq]
  congr 3
  funext r
  congr 3
  funext s
  cases s <;> rfl

/-- The active alphabet is bounded by the declared finite nonterminal count. -/
theorem active_card_le (g : EncodedGrammar) :
    (activeNonterminals g.decode).card ≤ g.size.nonterminals := by
  classical
  calc
    (activeNonterminals g.decode).card = g.activeLabels.card :=
      congrArg Finset.card g.activeLabels_eq.symm
    _ ≤ Fintype.card (Fin (g.extraNonterminalCount + 1)) := Finset.card_le_univ _
    _ = g.size.nonterminals := by simp [size]

/-- Enumeration already guarantees validity; test completeness, start root and
pathwise simplicity using finite lists. -/
@[expose] def baseTest (g : EncodedGrammar)
    (B : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) : Bool :=
  decide (B.holes = [] ∧ B.root = .nonterminal g.initial) &&
    B.labelPaths.all (fun p => decide p.Nodup)

theorem baseTest_correct (g : EncodedGrammar)
    (B : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1)))
    (hv : Valid g.decode B) : g.baseTest B = true ↔ IsBase g.decode B := by
  unfold baseTest
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨hh, hr⟩, hs⟩
    exact ⟨⟨hv, hh⟩, hr, hs⟩
  · rintro ⟨⟨_, hh⟩, hr, hs⟩
    exact ⟨⟨hh, hr⟩, hs⟩

/-- Test a nontrivial same-root/hole context and the exact active-height bound. -/
@[expose] def cycleTest (g : EncodedGrammar)
    (C : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) : Bool :=
  decide (∃ A, C.holes = [A] ∧ C.root = .nonterminal A ∧ 0 < C.productionSize) &&
    decide (C.height ≤ g.activeLabels.card + 1)

theorem cycleTest_correct (g : EncodedGrammar)
    (C : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1)))
    (hv : Valid g.decode C) : g.cycleTest C = true ↔ IsBoundedCycle g.decode C := by
  unfold cycleTest
  rw [activeLabels_eq]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨A, hh, hr, hp⟩, hheight⟩
    exact ⟨⟨A, ⟨hv, hh⟩, hr, hp⟩, hheight⟩
  · rintro ⟨⟨A, ⟨_, hh⟩, hr, hp⟩, hheight⟩
    exact ⟨⟨A, hh, hr, hp⟩, hheight⟩

/-- Duplicate-free syntax lists, keeping distinct trees even at equal weights. -/
@[expose] def baseTrees (g : EncodedGrammar) :
    List (ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) :=
  letI := ParseTree.decEq (T := Fin g.terminalCount) (N := Fin (g.extraNonterminalCount + 1))
  ((boundedEnumeration.enumerate g (g.size.nonterminals + 1)).filter g.baseTest).dedup

/-- Enumerate bounded cycle contexts, retaining one copy of each syntax tree. -/
@[expose] def cycleTrees (g : EncodedGrammar) :
    List (ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) :=
  letI := ParseTree.decEq (T := Fin g.terminalCount) (N := Fin (g.extraNonterminalCount + 1))
  ((boundedEnumeration.enumerate g (g.size.nonterminals + 1)).filter g.cycleTest).dedup

theorem baseTrees_nodup (g : EncodedGrammar) : g.baseTrees.Nodup := by
  let _ := ParseTree.decEq (T := Fin g.terminalCount) (N := Fin (g.extraNonterminalCount + 1))
  unfold baseTrees
  exact List.nodup_dedup _

theorem cycleTrees_nodup (g : EncodedGrammar) : g.cycleTrees.Nodup := by
  let _ := ParseTree.decEq (T := Fin g.terminalCount) (N := Fin (g.extraNonterminalCount + 1))
  unfold cycleTrees
  exact List.nodup_dedup _

/-- Every simple complete start tree is enumerated, including epsilon trees. -/
theorem mem_baseTrees (g : EncodedGrammar)
    (B : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) :
    B ∈ g.baseTrees ↔ IsBase g.decode B := by
  let _ := ParseTree.decEq (T := Fin g.terminalCount) (N := Fin (g.extraNonterminalCount + 1))
  change B ∈ ((boundedEnumeration.enumerate g (g.size.nonterminals + 1)).filter
    g.baseTest).dedup ↔ _
  rw [List.mem_dedup, List.mem_filter]
  constructor
  · rintro ⟨hm, ht⟩
    exact (g.baseTest_correct B ((boundedEnumeration.correct g _ B).mp hm).1).mp ht
  · intro hb
    have hh : B.height ≤ g.size.nonterminals :=
      (simple_height g.decode B hb.1 hb.2.2).trans g.active_card_le
    exact ⟨(boundedEnumeration.correct g _ B).mpr ⟨hb.1.1, hh.trans (Nat.le_succ _)⟩,
      (g.baseTest_correct B hb.1.1).mpr hb⟩

/-- Cycle enumeration uses precisely the frozen active-height predicate. -/
theorem mem_cycleTrees (g : EncodedGrammar)
    (C : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) :
    C ∈ g.cycleTrees ↔ IsBoundedCycle g.decode C := by
  let _ := ParseTree.decEq (T := Fin g.terminalCount) (N := Fin (g.extraNonterminalCount + 1))
  change C ∈ ((boundedEnumeration.enumerate g (g.size.nonterminals + 1)).filter
    g.cycleTest).dedup ↔ _
  rw [List.mem_dedup, List.mem_filter]
  constructor
  · rintro ⟨hm, ht⟩
    exact (g.cycleTest_correct C ((boundedEnumeration.correct g _ C).mp hm).1).mp ht
  · intro hc
    obtain ⟨A, ha⟩ := hc.1
    have hh := hc.2.trans (Nat.add_le_add_right g.active_card_le 1)
    exact ⟨(boundedEnumeration.correct g _ C).mpr ⟨ha.1.1, hh⟩,
      (g.cycleTest_correct C ha.1.1).mpr hc⟩

end EncodedGrammar
end Parikh
