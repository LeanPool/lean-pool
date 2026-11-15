/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.Activation
import LeanPool.Parikh.FiniteRepresentation
import LeanPool.Parikh.InsertionSequences

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# Joining the tree description to the grammar language

The earlier modules give a semilinear union of tree components. Here we prove
that this union is exactly the grammar image: insertions turn component vectors
into words, and decomposition puts each derived word into a component.

`treeRepresentation_correct` packages this equality with semilinearity.
The public theorems in `Statements.lean` project its two conclusions; the
regular-language specialization reuses the same result. Keeping this argument
in a shared module avoids an import cycle between the public statements and
regular realization.

Source: `thm:main`, `thm:parikh-statement`.
-/
namespace Parikh
variable {T : Type*}

/-- The exact tree formula and its semilinearity together give the grammar image
(`thm:main`, `thm:parikh-statement`). No finite nonterminal assumption is needed. -/
theorem treeRepresentation_correct [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    treeRepresentation g = image g.language ∧ IsSemilinearSet (image g.language) := by
  have heq : treeRepresentation g = image g.language := by
    classical
    ext v
    constructor
    · -- Realize a component vector by insertions, then read the resulting word.
      rintro ⟨B, D, hB, _, hD, hv⟩
      rw [← one_linear g B D hB.1 hD] at hv
      obtain ⟨t, Cs, hseq, _, hweight⟩ := hv
      obtain ⟨ht, hroot, _, _, _⟩ := hseq.accounting hB.1
      refine ⟨t.yield, ?_, hweight⟩
      exact (g.mem_language_iff t.yield).mpr
        ((derives_iff_tree g g.initial t.yield).mpr
          ⟨t, ht, hroot.trans hB.2.1, rfl⟩)
    · -- Decompose a word's derivation tree and collect the contexts it uses.
      rintro ⟨w, hw, rfl⟩
      obtain ⟨t, ht, hroot, hyield⟩ :=
        (derives_iff_tree g g.initial w).mp ((g.mem_language_iff w).mp hw)
      obtain ⟨B, Cs, hB, hBroot, hsimple, hbounded, hseq⟩ := decomposition g t ht
      have hD := hseq.contextsActivatable hB
      refine ⟨B, Cs.toFinset, ⟨hB, hBroot.trans hroot, hsimple⟩,
        fun C hC => hbounded C (List.mem_toFinset.mp hC), hD, ?_⟩
      rw [← one_linear g B Cs.toFinset hB hD]
      exact ⟨t, Cs, hseq, fun C => List.mem_toFinset.symm,
        by simp only [ParseTree.weight, hyield]⟩
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact treeRepresentation_isSemilinearSet g

end Parikh
