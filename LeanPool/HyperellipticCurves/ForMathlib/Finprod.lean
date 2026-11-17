/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Algebra.BigOperators.Finprod

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Folding a finsum along a two-to-one map

A Mathlib-gap combinatorial fact: if `e` is an involution whose only fixed point is `z₀`, `ζ`
identifies exactly the `e`-orbits, and `g` vanishes off the range of `ζ`, then
`∑ᶠ z, g (ζ z) + g (ζ z₀) = 2 * ∑ᶠ b, g b` (`finsum_comp_two_to_one`), and its
consequence for a pair of counting functions exchanged by `e`
(`finsum_eq_of_conj_pair_two_to_one`: then `∑ E = ∑ g`).
Also `finprod_mem_curry`/`finsum_mem_curry`: currying a finite product over
pairs whose second component ranges over a moving set.
-/

@[expose] public section

/-- **Currying a product over pairs whose second component ranges over a moving set.** The
support hypothesis is what makes both sides genuine finite products. -/
@[to_additive /-- **Currying a sum over pairs whose second component ranges over a moving
set.** The support hypothesis is what makes both sides genuine finite sums. -/]
theorem finprod_mem_curry {α β M : Type*} [CommMonoid M] (s : α → Set β) (g : α → β → M)
    (hfin : {p : α × β | p.2 ∈ s p.1 ∧ g p.1 p.2 ≠ 1}.Finite) :
    ∏ᶠ (p : α × β) (_ : p.2 ∈ s p.1), g p.1 p.2 = ∏ᶠ a, ∏ᶠ b ∈ s a, g a b := by
  classical
  have hsupp : Function.HasFiniteMulSupport fun p : α × β ↦ (s p.1).mulIndicator (g p.1) p.2 := by
    refine hfin.subset fun p hp ↦ ?_
    rw [Function.mem_mulSupport, Set.mulIndicator_apply] at hp
    split_ifs at hp with hmem
    · exact ⟨hmem, hp⟩
    · exact absurd rfl hp
  have h₁ : ∏ᶠ (p : α × β) (_ : p.2 ∈ s p.1), g p.1 p.2
      = ∏ᶠ p : α × β, (s p.1).mulIndicator (g p.1) p.2 :=
    finprod_mem_def {p : α × β | p.2 ∈ s p.1} _
  rw [h₁, finprod_curry _ hsupp]
  exact finprod_congr fun a ↦ by rw [finprod_mem_def]

/-- The fiber of `ζ` over `ζ w` inside a finite `e`-stable set `s`: it is `{w}` when `w` is the
fixed point `z₀` and `{w, e w}` otherwise, so its `g ∘ ζ`-sum is `1`, resp. `2`, times `g (ζ w)`. -/
private theorem finsum_comp_two_to_one_fiber {α β : Type*} [DecidableEq β]
    {ζ : α → β} {e : α → α} {z₀ : α} {g : β → ℕ} (hζe : ∀ z, ζ (e z) = ζ z)
    (hfib : ∀ z z', ζ z' = ζ z → z' = z ∨ z' = e z) (hfix : ∀ z, e z = z ↔ z = z₀)
    {s : Finset α} (hes : ∀ z ∈ s, e z ∈ s) {w : α} (hws : w ∈ s) :
    (∑ z ∈ s with ζ z = ζ w, g (ζ z)) = (if ζ w = ζ z₀ then 1 else 2) * g (ζ w) := by
  classical
  by_cases hew : e w = w
  · have hw0 : w = z₀ := (hfix w).mp hew
    subst hw0
    have hfil : {z ∈ s | ζ z = ζ w} = {w} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_singleton]
      refine ⟨fun ⟨_, hζz⟩ ↦ (hfib w z hζz).elim id (fun h ↦ by rw [h, hew]), ?_⟩
      rintro rfl
      exact ⟨hws, rfl⟩
    rw [hfil, Finset.sum_singleton, ite_eq_left rfl, one_mul]
  · have hbne : ζ w ≠ ζ z₀ := by
      intro hc
      rcases hfib z₀ w hc with rfl | hwz
      · exact hew ((hfix w).mpr rfl)
      · rw [(hfix z₀).mpr rfl] at hwz
        exact hew ((hfix w).mpr hwz)
    have hfil : {z ∈ s | ζ z = ζ w} = {w, e w} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      refine ⟨fun ⟨_, hζz⟩ ↦ hfib w z hζz, ?_⟩
      rintro (rfl | rfl)
      · exact ⟨hws, rfl⟩
      · exact ⟨hes w hws, hζe w⟩
    rw [hfil, Finset.sum_pair (fun h ↦ hew h.symm), ite_eq_right hbne, hζe]
    ring

-- An `e`-stable finite superset of the support, containing the distinguished point, together
-- with the two support inclusions its image supplies.
private theorem exists_finset_stable {α β : Type*} [DecidableEq β] {ζ : α → β}
    {e : α → α} {z₀ : α} {g : β → ℕ} (hζe : ∀ z, ζ (e z) = ζ z) (hfix : ∀ z, e z = z ↔ z = z₀)
    (hrange : ∀ b, b ∉ Set.range ζ → g b = 0)
    (hsupp : (Function.support fun z ↦ g (ζ z)).Finite) :
    ∃ s : Finset α, z₀ ∈ s ∧ (∀ z ∈ s, e z ∈ s) ∧
      (Function.support fun z ↦ g (ζ z)) ⊆ ↑s ∧ Function.support g ⊆ ↑(s.image ζ) := by
  classical
  refine ⟨insert z₀ hsupp.toFinset, Finset.mem_insert_self .., fun z hz ↦ ?_, fun z hz ↦
    Finset.mem_insert_of_mem (hsupp.mem_toFinset.mpr hz), fun b hb ↦ ?_⟩
  · rcases Finset.mem_insert.mp hz with h | hz
    · rw [h, (hfix z₀).mpr rfl]
      exact Finset.mem_insert_self ..
    · refine Finset.mem_insert_of_mem ?_
      rw [Set.Finite.mem_toFinset] at hz ⊢
      rwa [Function.mem_support, hζe]
  · rw [Function.mem_support] at hb
    obtain ⟨z, rfl⟩ := not_not.mp fun hr ↦ hb (hrange b hr)
    exact Finset.mem_image_of_mem ζ (Finset.mem_insert_of_mem
      (hsupp.mem_toFinset.mpr (by rwa [Function.mem_support])))

/-- Folding a finsum along a two-to-one map: if `e` is an involution whose only fixed point is
`z₀`, `ζ` identifies exactly the `e`-orbits, and `g` vanishes off the range of `ζ`, then
`∑ᶠ z, g (ζ z) + g (ζ z₀) = 2 * ∑ᶠ b, g b`. -/
theorem finsum_comp_two_to_one {α β : Type*} {ζ : α → β} {e : α → α} {z₀ : α} {g : β → ℕ}
    (hζe : ∀ z, ζ (e z) = ζ z)
    (hfib : ∀ z z', ζ z' = ζ z → z' = z ∨ z' = e z)
    (hfix : ∀ z, e z = z ↔ z = z₀)
    (hrange : ∀ b, b ∉ Set.range ζ → g b = 0)
    (hsupp : (Function.support fun z ↦ g (ζ z)).Finite) :
    (∑ᶠ z, g (ζ z)) + g (ζ z₀) = 2 * ∑ᶠ b, g b := by
  classical
  obtain ⟨s, hzs, hes, hsuppζ, hsuppg⟩ := exists_finset_stable hζe hfix hrange hsupp
  set t : Finset β := s.image ζ
  have hb₀ : ζ z₀ ∈ t := Finset.mem_image_of_mem ζ hzs
  rw [finsum_eq_finsetSum_of_support_subset _ hsuppζ,
    finsum_eq_finsetSum_of_support_subset _ hsuppg,
    ← Finset.sum_fiberwise_of_maps_to (fun z hz ↦ Finset.mem_image_of_mem ζ hz)
      (fun z ↦ g (ζ z))]
  have hfibsum : ∀ b ∈ t, (∑ z ∈ s with ζ z = b, g (ζ z))
      = (if b = ζ z₀ then 1 else 2) * g b := fun b hb ↦ by
    obtain ⟨w, hws, rfl⟩ := Finset.mem_image.mp hb
    exact finsum_comp_two_to_one_fiber hζe hfib hfix hes hws
  rw [Finset.sum_congr rfl hfibsum]
  have herase : ∑ b ∈ t.erase (ζ z₀), (if b = ζ z₀ then 1 else 2) * g b
      = ∑ b ∈ t.erase (ζ z₀), 2 * g b :=
    Finset.sum_congr rfl fun b hb ↦ by rw [ite_eq_right (Finset.ne_of_mem_erase hb)]
  rw [← Finset.add_sum_erase t (fun b ↦ (if b = ζ z₀ then 1 else 2) * g b) hb₀,
    ← Finset.add_sum_erase t g hb₀, ite_eq_left rfl, one_mul, herase, mul_add,
    Finset.mul_sum]
  ring

private theorem finsum_ite_two_mul {α : Type*} [DecidableEq α] {p : α → ℕ} {z₀ : α}
    (hp : (Function.support p).Finite) :
    (∑ᶠ z, if z = z₀ then 2 * p z else p z) = (∑ᶠ z, p z) + p z₀ := by
  rw [show (fun z ↦ if z = z₀ then 2 * p z else p z)
      = fun z ↦ p z + (if z = z₀ then p z else 0) from funext fun z ↦ by
    by_cases h : z = z₀
    · rw [ite_eq_left h, ite_eq_left h, two_mul]
    · rw [ite_eq_right h, ite_eq_right h, add_zero]]
  have hifsupp : (Function.support fun z ↦ if z = z₀ then p z else 0).Finite :=
    (Set.finite_singleton z₀).subset fun z hz ↦ by by_contra hne; exact hz (ite_eq_right hne)
  rw [finsum_add_distrib hp hifsupp, finsum_eq_single _ z₀ (fun b hb ↦ ite_eq_right hb),
    ite_eq_left rfl]

/-- **A conjugate pair of counting functions sums to the base of a two-to-one fold.** If `E'`
is `E` composed with the involution `e`, and the pair `E + E'` is the pullback `g ∘ ζ` of a
base function — doubled at the fixed point `z₀` of `e` — then `∑ E = ∑ g`. -/
theorem finsum_eq_of_conj_pair_two_to_one {α β : Type*} [DecidableEq α] {ζ : α → β}
    {e : α → α} {z₀ : α} {g : β → ℕ} {E E' : α → ℕ} (hζe : ∀ z, ζ (e z) = ζ z)
    (hfib : ∀ z z', ζ z' = ζ z → z' = z ∨ z' = e z) (hfix : ∀ z, e z = z ↔ z = z₀)
    (hrange : ∀ b, b ∉ Set.range ζ → g b = 0)
    (hsupp : (Function.support fun z ↦ g (ζ z)).Finite) (hebij : Function.Bijective e)
    (hEe : ∀ z, E (e z) = E' z)
    (hpair : ∀ z, E z + E' z = if z = z₀ then 2 * g (ζ z) else g (ζ z)) :
    (∑ᶠ z, E z) = ∑ᶠ b, g b := by
  -- both functions vanish wherever the pullback does
  have hzero (z : α) (h0 : g (ζ z) = 0) : E z + E' z = 0 := by rw [hpair z, h0, mul_zero, ite_self]
  have hEsupp : (Function.support E).Finite :=
    hsupp.subset fun z hz h0 ↦ hz (Nat.eq_zero_of_add_eq_zero_right (hzero z h0))
  have hE'supp : (Function.support E').Finite :=
    hsupp.subset fun z hz h0 ↦ hz (Nat.eq_zero_of_add_eq_zero_left (hzero z h0))
  -- the involution reindexes the conjugate sum
  have hreidx : ∑ᶠ z, E' z = ∑ᶠ z, E z :=
    (finsum_congr fun z ↦ (hEe z).symm).trans (finsum_comp (g := E) e hebij)
  have h2 : 2 * (∑ᶠ z, E z) = 2 * ∑ᶠ b, g b :=
    calc 2 * (∑ᶠ z, E z) = (∑ᶠ z, E z) + (∑ᶠ z, E' z) := by rw [hreidx, two_mul]
      _ = ∑ᶠ z, (E z + E' z) := (finsum_add_distrib hEsupp hE'supp).symm
      _ = (∑ᶠ z, g (ζ z)) + g (ζ z₀) := by
          rw [finsum_congr hpair]
          exact finsum_ite_two_mul hsupp
      _ = 2 * ∑ᶠ b, g b := finsum_comp_two_to_one hζe hfib hfix hrange hsupp
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

end
