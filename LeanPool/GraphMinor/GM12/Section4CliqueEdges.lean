/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM12.Section4PairEnumeration

/-!
# The clique edge enumeration and its ordered ends

In XII (4.4), page 251, each path label stands for one pair of
clique vertices. Sending a pair with smaller endpoint first to its
unordered pair is a bijection with the edges of the complete graph.
This keeps the path labels aligned with the actual target edge
labels when the enlarged branches form a controlled minor.
-/

public section

namespace GraphMinor.GM12

open Set Graph

/-- The smaller endpoint in the enumeration by larger endpoint. -/
@[expose] def cliquePairLower {p : ℕ} (e : Σ j : Fin p, Fin j.val) : Fin p :=
  ⟨e.2.val, e.2.isLt.trans e.1.isLt⟩

theorem cliquePairLower_lt {p : ℕ} (e : Σ j : Fin p, Fin j.val) :
    cliquePairLower e < e.1 := e.2.isLt

/-- The lower and upper endpoints determine the sorted clique edge. -/
theorem cliquePair_ends_injective {p : ℕ} :
    Function.Injective (fun e : Σ j : Fin p, Fin j.val => (cliquePairLower e, e.1)) := by
  rintro ⟨j, i⟩ ⟨k, l⟩ heq
  have hupper : j = k := congrArg Prod.snd heq
  subst k
  have hlower := congrArg (fun q : Fin p × Fin p => q.1.val) heq
  have hil : i = l := Fin.ext hlower
  subst l
  rfl

/-- The sorted pairs are in bijection with the actual edge set of
the clique, as in XII (4.4), page 251. -/
noncomputable def cliquePairEdgeEquiv (p : ℕ) :
    (Σ j : Fin p, Fin j.val) ≃ (GM16.completeGraph p).edgeSet := by
  let f : (Σ j : Fin p, Fin j.val) → (GM16.completeGraph p).edgeSet := fun e =>
    ⟨s(cliquePairLower e, e.1), cliquePairLower e, e.1, (cliquePairLower_lt e).ne, rfl⟩
  have hf : Function.Injective f := by
    intro e e' heq
    have hpair := congrArg Subtype.val heq
    rcases Sym2.eq_iff.mp hpair with ⟨hl, hu⟩ | ⟨hl, hu⟩
    · exact cliquePair_ends_injective (Prod.ext hl hu)
    · have he := cliquePairLower_lt e
      have he' := cliquePairLower_lt e'
      rw [hl, hu] at he
      exact False.elim (lt_asymm he he')
  have hs : Function.Surjective f := by
    rintro ⟨e, x, y, hxy, he⟩
    subst e
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · refine ⟨⟨y, ⟨x.val, hlt⟩⟩, Subtype.ext ?_⟩
      rfl
    · refine ⟨⟨x, ⟨y.val, hgt⟩⟩, Subtype.ext ?_⟩
      exact Sym2.eq_swap
  exact Equiv.ofBijective f ⟨hf, hs⟩

/-- The complete graph's edge labels can be matched with the path
indices, retaining the corresponding ordered vertex pair. -/
noncomputable def cliqueEdgeEnumeration (p : ℕ) :
    Fin (p * (p - 1) / 2) ≃ (GM16.completeGraph p).edgeSet :=
  (Classical.choice (nonempty_clique_pair_enumeration p)).trans (cliquePairEdgeEquiv p)

end GraphMinor.GM12
