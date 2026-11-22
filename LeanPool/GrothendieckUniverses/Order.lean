/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.GrothendieckUniverses.Classification

/-!
# The order of universes and the universe axiom

From the classification `U = V_ (rank U)` we deduce that Grothendieck universes are totally
ordered by membership (equivalently by inclusion), that `V_ ω` is the least universe, that the
intersection of a nonempty set of universes is its least element and again a universe, that a
set lying in some universe lies in a least one (Gabriel 1962, Ch. 0, §1), and that the universe
axiom « every set lies in a universe » holds in `ZFSet.{u}` exactly when the inaccessible
cardinals of `Cardinal.{u}` are unbounded (Williams 1969, p. 3).

## References

* P. Gabriel, *Des catégories abéliennes*, Bull. Soc. Math. France 90 (1962), 323–448.
* N. H. Williams, *On Grothendieck universes*, Compositio Math. 21 (1969), 1–3.
-/

@[expose] public section

namespace LeanPool.GrothendieckUniverses

open ZFSet Cardinal Ordinal Order

universe u

namespace IsGrothendieckUniverse

variable {U V : ZFSet.{u}}

/-- One universe is an element of another exactly when its rank is smaller. -/
theorem mem_iff_rank_lt_rank (hU : IsGrothendieckUniverse U) (hV : IsGrothendieckUniverse V) :
    U ∈ V ↔ rank U < rank V := by
  conv_lhs => rw [hU.eq_vonNeumann_rank, hV.eq_vonNeumann_rank]
  exact vonNeumann_mem_vonNeumann_iff

/-- One universe is a subset of another exactly when its rank is smaller or equal. -/
theorem subset_iff_rank_le_rank (hU : IsGrothendieckUniverse U) (hV : IsGrothendieckUniverse V) :
    U ⊆ V ↔ rank U ≤ rank V := by
  conv_lhs => rw [hU.eq_vonNeumann_rank, hV.eq_vonNeumann_rank]
  exact vonNeumann_subset_vonNeumann_iff

/-- **Universes are totally ordered by membership**: of two universes, one is an element of the
other or they are equal. -/
theorem mem_or_eq_or_mem (hU : IsGrothendieckUniverse U) (hV : IsGrothendieckUniverse V) :
    U ∈ V ∨ U = V ∨ V ∈ U := by
  rw [hU.mem_iff_rank_lt_rank hV, hV.mem_iff_rank_lt_rank hU]
  rcases lt_trichotomy (rank U) (rank V) with h | h | h
  · exact .inl h
  · right; left
    rw [hU.eq_vonNeumann_rank, hV.eq_vonNeumann_rank, h]
  · exact .inr (.inr h)

/-- Universes are totally ordered by inclusion. -/
theorem subset_or_subset (hU : IsGrothendieckUniverse U) (hV : IsGrothendieckUniverse V) :
    U ⊆ V ∨ V ⊆ U := by
  rw [hU.subset_iff_rank_le_rank hV, hV.subset_iff_rank_le_rank hU]
  exact le_total _ _

/-- `V_ ω`, the set of hereditarily finite sets, is contained in every universe. -/
theorem vonNeumann_omega0_subset (hU : IsGrothendieckUniverse U) : V_ ω ⊆ U := by
  rw [isGrothendieckUniverse_vonNeumann_omega0.subset_iff_rank_le_rank hU, rank_vonNeumann]
  exact hU.omega0_le_rank

end IsGrothendieckUniverse

/-- The intersection of a nonempty set of universes is a universe: it is the least element of
the set. -/
theorem sInter_mem_of_forall_isGrothendieckUniverse {S : ZFSet.{u}} (hS : S.Nonempty)
    (h : ∀ U ∈ S, IsGrothendieckUniverse U) : ⋂₀ S ∈ S := by
  obtain ⟨W, hW, hmin⟩ :=
    Ordinal.lt_wf.has_min (rank '' (S : Set ZFSet.{u})) (hS.image rank)
  obtain ⟨U, hU, rfl⟩ := hW
  have hUV : ∀ V ∈ S, U ⊆ V := fun V hV =>
    ((h U hU).subset_iff_rank_le_rank (h V hV)).2 (not_lt.1 (hmin _ ⟨V, hV, rfl⟩))
  have heq : ⋂₀ S = U := by
    ext z
    rw [mem_sInter hS]
    exact ⟨fun hz => hz U hU, fun hz V hV => hUV V hV hz⟩
  rw [heq]
  exact hU

/-- The intersection of a nonempty set of universes is a universe. -/
theorem isGrothendieckUniverse_sInter {S : ZFSet.{u}} (hS : S.Nonempty)
    (h : ∀ U ∈ S, IsGrothendieckUniverse U) : IsGrothendieckUniverse (⋂₀ S) :=
  h _ (sInter_mem_of_forall_isGrothendieckUniverse hS h)

/-- **The least universe containing a set** (Gabriel 1962, Ch. 0, §1): if a set lies in some
universe, it lies in a least one. -/
theorem exists_least_isGrothendieckUniverse {x : ZFSet.{u}}
    (h : ∃ U, IsGrothendieckUniverse U ∧ x ∈ U) :
    ∃ U, IsGrothendieckUniverse U ∧ x ∈ U ∧
      ∀ V, IsGrothendieckUniverse V → x ∈ V → U ⊆ V := by
  let s : Set Ordinal.{u} := {o | ∃ U, IsGrothendieckUniverse U ∧ x ∈ U ∧ rank U = o}
  have hs : s.Nonempty := by
    obtain ⟨U, hU, hx⟩ := h
    exact ⟨_, U, hU, hx, rfl⟩
  obtain ⟨U, hU, hx, hrank⟩ := csInf_mem hs
  refine ⟨U, hU, hx, fun V hV hxV => (hU.subset_iff_rank_le_rank hV).2 ?_⟩
  rw [hrank]
  exact csInf_le' ⟨V, hV, hxV, rfl⟩

/-- A stage `V_ o` is a universe exactly when `o = ω` or `o = κ.ord` for an inaccessible `κ`. -/
theorem isGrothendieckUniverse_vonNeumann_iff {o : Ordinal.{u}} :
    IsGrothendieckUniverse (V_ o) ↔
      o = ω ∨ ∃ κ : Cardinal.{u}, κ.IsInaccessible ∧ o = κ.ord := by
  simp [isGrothendieckUniverse_iff]

/-- A successor stage `V_ (o + 1)` is never a universe; for instance `{∅} = V_ 1` and
`V_ (ω + 1)` are not universes. -/
theorem not_isGrothendieckUniverse_vonNeumann_add_one (o : Ordinal.{u}) :
    ¬ IsGrothendieckUniverse (V_ (o + 1)) := fun h => by
  have := h.isSuccLimit_rank
  rw [rank_vonNeumann] at this
  exact Order.not_isSuccLimit_add_one o this

/-- The stage `V_ (ω + ω)` is not a universe, although its rank is a limit ordinal: it fails the
axiom on unions of families indexed by an element. -/
theorem not_isGrothendieckUniverse_vonNeumann_omega0_add_omega0 :
    ¬ IsGrothendieckUniverse (V_ (ω + ω : Ordinal.{u})) := by
  rw [isGrothendieckUniverse_vonNeumann_iff]
  rintro (h | ⟨κ, hκ, h⟩)
  · exact (lt_add_of_pos_right ω omega0_pos).ne' h
  · have hcard : (ω + ω : Ordinal.{u}).card = ℵ₀ := by simp
    rw [h, card_ord] at hcard
    exact hκ.aleph0_lt.ne' hcard

/-- If some universe contains `ω`, then `Cardinal.{u}` has an inaccessible cardinal. -/
theorem exists_isInaccessible_of_omega_mem {U : ZFSet.{u}} (hU : IsGrothendieckUniverse U)
    (h : ZFSet.omega ∈ U) : ∃ κ : Cardinal.{u}, κ.IsInaccessible :=
  ⟨_, hU.isInaccessible_card.2 h⟩

/-- `V_ ω` is an element of `V_ κ.ord` for every inaccessible `κ`. -/
theorem vonNeumann_omega0_mem_vonNeumann {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    V_ ω ∈ V_ κ.ord := by
  rw [vonNeumann_mem_vonNeumann_iff, lt_ord, card_omega0]
  exact hκ.aleph0_lt

/-- **The universe axiom** (Williams 1969, p. 3): every set lies in a universe exactly when every
cardinal lies below an inaccessible cardinal. -/
theorem forall_exists_isGrothendieckUniverse_iff :
    (∀ x : ZFSet.{u}, ∃ U, IsGrothendieckUniverse U ∧ x ∈ U) ↔
      ∀ c : Cardinal.{u}, ∃ κ : Cardinal.{u}, κ.IsInaccessible ∧ c < κ := by
  refine ⟨fun h c => ?_, fun h x => ?_⟩
  · obtain ⟨U, hU, hx⟩ := h (V_ (max c.ord ω))
    rw [hU.mem_iff_rank_lt, rank_vonNeumann, max_lt_iff] at hx
    refine ⟨card U, hU.isInaccessible_card.2 (hU.omega_mem_iff_omega0_lt_rank.2 hx.2), ?_⟩
    rw [← ord_lt_ord, hU.ord_card]
    exact hx.1
  · obtain ⟨κ, hκ, hlt⟩ := h (rank x).card
    refine ⟨_, isGrothendieckUniverse_vonNeumann hκ, ?_⟩
    rw [mem_vonNeumann, lt_ord]
    exact hlt

end LeanPool.GrothendieckUniverses
