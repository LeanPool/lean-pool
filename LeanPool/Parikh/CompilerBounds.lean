/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.CompilerTrees
import LeanPool.Parikh.BoundedFamilySupport
import LeanPool.Parikh.InsertionSequences

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# Bounds for executable tree families

Specialize the existing counting cover and leaf-norm results to the declared
encoded alphabet. This covers unused symbols and duplicate input productions
without changing the accepted grammar-size definitions.
Source: `lem:count-trees`, `thm:size-bound`.
-/
namespace Parikh
namespace EncodedGrammar

/-- The executable exact families satisfy the declared syntax budgets. -/
theorem tree_budgets (g : EncodedGrammar) :
    g.baseTrees.length ≤ g.size.trees ∧ g.cycleTrees.length ≤ g.size.trees ∧
      ∀ t, IsBase g.decode t ∨ IsBoundedCycle g.decode t → norm t.weight ≤ g.size.positions := by
  classical
  let s := g.size
  have hb : ∀ r ∈ g.decode.rules, r.output.length ≤ s.branching := by
    intro r hr
    change r ∈ g.rules.toFinset at hr
    have hm : r.output.length ∈ g.rules.map (fun r => r.output.length) :=
      List.mem_map.mpr ⟨r, List.mem_toFinset.mp hr, rfl⟩
    have hfold : r.output.length ≤ (g.rules.map fun r => r.output.length).foldl max 0 := by
      rw [List.foldl_max_eq_max (List.ne_nil_of_mem hm), Nat.zero_max]
      exact List.le_max_of_mem hm
    exact hfold.trans (Nat.le_max_right _ _)
  have hq : 1 + Fintype.card (Fin g.terminalCount) +
      (activeNonterminals g.decode).card + g.decode.rules.card ≤ s.records := by
    have hn := g.active_card_le
    change (activeNonterminals g.decode).card ≤ g.extraNonterminalCount + 1 at hn
    change 1 + Fintype.card (Fin g.terminalCount) + (activeNonterminals g.decode).card +
      g.rules.toFinset.card ≤ 1 + g.terminalCount + (g.extraNonterminalCount + 1) +
        g.rules.toFinset.card
    simp only [Fintype.card_fin]
    omega
  have hbounded : ∀ t, IsBase g.decode t ∨ IsBoundedCycle g.decode t →
      ActiveOpen g.decode t ∧ t.height ≤ s.nonterminals + 1 := by
    intro t ht
    rcases ht with hbase | hcycle
    · refine ⟨⟨hbase.1.1, ?_⟩, ?_⟩
      · simp [hbase.1.2]
      · exact ((simple_height g.decode t hbase.1 hbase.2.2).trans g.active_card_le).trans
          (Nat.le_succ _)
    · obtain ⟨⟨A, hc⟩, hh⟩ := hcycle
      refine ⟨⟨hc.1.1, ?_⟩, hh.trans (Nat.add_le_add_right g.active_card_le 1)⟩
      intro B hB
      have hBA : B = A := by simpa only [hc.1.2, List.mem_singleton] using hB
      subst B
      exact hc.1.1.support_active hc.root_mem_support
  let family := treeFamily g.decode (s.nonterminals + 1)
  have hmem : ∀ t, IsBase g.decode t ∨ IsBoundedCycle g.decode t → t ∈ family := by
    intro t ht
    obtain ⟨ho, hh⟩ := hbounded t ht
    exact mem_treeFamily g.decode _ t ho hh
  have hcard : family.card ≤ s.trees := by
    simpa only [GrammarSize.trees, GrammarSize.positions, heightPositions, Nat.add_assoc] using
      card_treeFamily_le g.decode s.branching s.records hq hb (s.nonterminals + 1)
  refine ⟨?_, ?_, ?_⟩
  · rw [← List.toFinset_card_of_nodup g.baseTrees_nodup]
    exact (Finset.card_le_card (show g.baseTrees.toFinset ⊆ family from
      fun B hB => hmem B (Or.inl ((g.mem_baseTrees B).mp (List.mem_toFinset.mp hB))))).trans hcard
  · rw [← List.toFinset_card_of_nodup g.cycleTrees_nodup]
    exact (Finset.card_le_card (show g.cycleTrees.toFinset ⊆ family from
      fun C hC => hmem C (Or.inr ((g.mem_cycleTrees C).mp (List.mem_toFinset.mp hC))))).trans hcard
  · intro t ht
    obtain ⟨ho, hh⟩ := hbounded t ht
    rw [ParseTree.norm_weight_eq_length]
    simpa only [GrammarSize.positions, heightPositions, Nat.add_assoc] using
      yield_length_le_heightPositions g.decode s.branching hb _ t ho.1 hh

end EncodedGrammar
end Parikh
