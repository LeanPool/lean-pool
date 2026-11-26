/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Bool.Basic
import LeanPool.GraphMinor.GM12.Section4CliqueEdges

/-!
# The oriented ports of a clique

Each edge of the clique in XII (4.5), page 252, has one port at
each of its ends. Enumerate unordered vertex pairs by their larger
endpoint, then choose which end is the current port with a Boolean
index. This gives a bijection with ordered pairs of distinct
vertices. Switching the Boolean index reverses the ordered pair.
-/

public section

namespace GraphMinor.GM12

/-- The clique edge ports are in bijection with ordered pairs of
distinct vertices, and changing the chosen end reverses the pair.
This is the port labelling for XII (4.5), page 252. -/
theorem exists_clique_port_bijection (p : ℕ) :
    ∃ ψ : (Fin (p * (p - 1) / 2) × Bool) ≃ {q : Fin p × Fin p // q.1 ≠ q.2},
      ∀ i b, (ψ (i, !b)).val = ((ψ (i, b)).val.2, (ψ (i, b)).val.1) := by
  let f : ((Σ j : Fin p, Fin j.val) × Bool) → {q : Fin p × Fin p // q.1 ≠ q.2} :=
    fun x => if x.2 then ⟨(x.1.1, cliquePairLower x.1), (cliquePairLower_lt x.1).ne'⟩
      else ⟨(cliquePairLower x.1, x.1.1), (cliquePairLower_lt x.1).ne⟩
  have hf : Function.Injective f := by
    rintro ⟨e, b⟩ ⟨e', b'⟩ heq
    have hpair := congrArg Subtype.val heq
    cases b <;> cases b'
    · exact Prod.ext (cliquePair_ends_injective hpair) rfl
    · have hlow := cliquePairLower_lt e
      have hhigh := cliquePairLower_lt e'
      have h1 := congrArg Prod.fst hpair
      have h2 := congrArg Prod.snd hpair
      change cliquePairLower e = e'.1 at h1
      change e.1 = cliquePairLower e' at h2
      rw [h1, h2] at hlow
      exact False.elim (lt_asymm hlow hhigh)
    · have hlow := cliquePairLower_lt e
      have hhigh := cliquePairLower_lt e'
      have h1 := congrArg Prod.fst hpair
      have h2 := congrArg Prod.snd hpair
      change e.1 = cliquePairLower e' at h1
      change cliquePairLower e = e'.1 at h2
      rw [h1, h2] at hlow
      exact False.elim (lt_asymm hlow hhigh)
    · have hends : (cliquePairLower e, e.1) = (cliquePairLower e', e'.1) :=
        Prod.ext (congrArg Prod.snd hpair) (congrArg Prod.fst hpair)
      exact Prod.ext (cliquePair_ends_injective hends) rfl
  have hs : Function.Surjective f := by
    rintro ⟨⟨v, w⟩, hvw⟩
    rcases lt_or_gt_of_ne hvw with hlt | hgt
    · exact ⟨(⟨w, ⟨v.val, hlt⟩⟩, false), Subtype.ext rfl⟩
    · exact ⟨(⟨v, ⟨w.val, hgt⟩⟩, true), Subtype.ext rfl⟩
  let ε := Classical.choice (nonempty_clique_pair_enumeration p)
  let ψ := (Equiv.prodCongr ε (Equiv.refl Bool)).trans (Equiv.ofBijective f ⟨hf, hs⟩)
  refine ⟨ψ, ?_⟩
  intro i b
  cases b <;> rfl

end GraphMinor.GM12
