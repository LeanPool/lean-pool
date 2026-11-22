/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.GrothendieckUniverses.VonNeumann

/-!
# Williams's classification of Grothendieck universes

Every Grothendieck universe `U` equals the stage `V_ (rank U)` of the von Neumann hierarchy.
This is proved by `∈`-induction: if `y ∈ U` then `V_ (rank y)`, the union of the power sets
`𝒫 (V_ (rank z))` over `z ∈ y`, lies in `U`. Writing `θ = rank U`, the axiom on unions of
families indexed by an element shows that every family of ordinals below `θ` indexed by an
element of `U` is bounded below `θ`. From this, `θ` is an initial ordinal and its cardinal
`κ = card U` is regular and a strong limit, so `U = V_ κ.ord`. Hence (Williams 1969, Theorems 1
and 2, after Kruse 1965):

* `isGrothendieckUniverse_iff`: the universes are `V_ ω` and the `V_ κ.ord`, `κ` inaccessible;
* `IsGrothendieckUniverse.eq_vonNeumann_card`: every universe `U` is `V_ (card U).ord`;
* `IsGrothendieckUniverse.isInaccessible_card`: `card U` is inaccessible iff `ω ∈ U`;
* `IsGrothendieckUniverse.mem_iff_subset_and_card_lt`: Kruse's criterion, `x ∈ U` iff `x ⊆ U`
  and `card x < card U`.

The argument for `U = V_ (rank U)` does not use the axiom of choice; choice enters only through
the cardinal arithmetic of the second half.

## References

* A. H. Kruse, *Grothendieck universes and the super-complete models of Shepherdson*,
  Compositio Math. 17 (1965), 96–101.
* N. H. Williams, *On Grothendieck universes*, Compositio Math. 21 (1969), 1–3.
-/

@[expose] public section

namespace LeanPool.GrothendieckUniverses

open ZFSet Cardinal Ordinal Order

universe u

/-- The von Neumann stage `V_ (rank y)` is the union of the power sets `𝒫 (V_ (rank z))` over
the elements `z ∈ y`. -/
theorem vonNeumann_rank_eq_iUnion (y : ZFSet.{u}) :
    V_ (rank y) = ⋃ z : y, powerset (V_ (rank z.1)) := by
  ext x
  simp only [mem_vonNeumann, mem_iUnion, mem_powerset, subset_vonNeumann, lt_rank_iff]
  exact ⟨fun ⟨z, hz, h⟩ => ⟨⟨z, hz⟩, h⟩, fun ⟨z, h⟩ => ⟨z.1, z.2, h⟩⟩

namespace IsGrothendieckUniverse

variable {U x y : ZFSet.{u}} (hU : IsGrothendieckUniverse U)
include hU

omit hU in
/-- If `y` lies in a universe `U`, so does the stage `V_ (rank y)`; proved by `∈`-induction,
without choice or cardinal arithmetic. -/
theorem vonNeumann_rank_mem (hU : IsGrothendieckUniverse U) (hy : y ∈ U) : V_ (rank y) ∈ U := by
  induction y using ZFSet.inductionOn with | h y ih
  rw [vonNeumann_rank_eq_iUnion]
  exact hU.iUnion_mem y hy _ fun z =>
    hU.powerset_mem _ (ih z.1 z.2 (hU.mem_of_mem hy z.2))

/-- **A universe is the stage of its rank**: `U = V_ (rank U)`. -/
theorem eq_vonNeumann_rank : U = V_ (rank U) := by
  refine le_antisymm (subset_vonNeumann_self U) fun x hx => ?_
  rw [mem_vonNeumann] at hx
  obtain ⟨y, hy, hxy⟩ := lt_rank_iff.1 hx
  exact hU.mem_of_subset (hU.vonNeumann_rank_mem hy)
    ((subset_vonNeumann_self x).trans (vonNeumann_subset_of_le hxy))

/-- Membership in a universe is decided by rank. -/
theorem mem_iff_rank_lt : x ∈ U ↔ rank x < rank U := by
  conv_lhs => rw [hU.eq_vonNeumann_rank]
  exact mem_vonNeumann

/-- The rank of a universe is a limit ordinal. -/
theorem isSuccLimit_rank : IsSuccLimit (rank U) := by
  refine isSuccLimit_iff.2 ⟨?_, isSuccPrelimit_of_succ_lt fun o ho => ?_⟩
  · intro h
    have := hU.mem_iff_rank_lt.1 hU.empty_mem
    simp [h] at this
  · have h : V_ o ∈ U := hU.mem_iff_rank_lt.2 (by simpa using ho)
    simpa using hU.mem_iff_rank_lt.1 (hU.powerset_mem _ h)

/-- The rank of a universe is at least `ω`. -/
theorem omega0_le_rank : ω ≤ rank U := omega0_le_of_isSuccLimit hU.isSuccLimit_rank

/-- A family of ordinals below `rank U` indexed by an element of `U` is bounded below `rank U`:
this is axiom UA4 applied to the family of stages `V_ (g i)`. -/
theorem iSup_lt_rank (hy : y ∈ U) (g : y → Ordinal.{u}) (hg : ∀ i, g i < rank U) :
    ⨆ i, g i < rank U := by
  have : (⋃ i, V_ (g i)) ∈ U :=
    hU.iUnion_mem y hy _ fun i => hU.mem_iff_rank_lt.2 (by simpa using hg i)
  simpa using hU.mem_iff_rank_lt.1 this

/-- A family of ordinals below `rank U`, indexed by a type no larger than an element of `U`, is
bounded below `rank U`. -/
theorem exists_lt_rank_forall_le (hy : y ∈ U) {β : Type (u + 1)} (hβ : #β ≤ #y)
    (f : β → Ordinal.{u}) (hf : ∀ b, f b < rank U) : ∃ s < rank U, ∀ b, f b ≤ s := by
  rcases isEmpty_or_nonempty β with hβ' | hβ'
  · exact ⟨0, hU.isSuccLimit_rank.bot_lt, fun b => isEmptyElim b⟩
  obtain ⟨e⟩ := (le_def β y).1 hβ
  refine ⟨⨆ i, f (Function.invFun e i), hU.iSup_lt_rank hy _ fun i => hf _, fun b => ?_⟩
  have := Ordinal.le_iSup (fun i => f (Function.invFun e i)) (e b)
  rwa [Function.leftInverse_invFun e.injective b] at this

/-- Every element of a universe has cardinality smaller than `(rank U).card`. -/
theorem card_lt_card_rank (hx : x ∈ U) : card x < (rank U).card := by
  by_contra! h
  have hβ : #(Set.Iio (rank U)) ≤ #x := by
    rw [cardinalMk_Iio, cardinalMk_coe_sort]
    exact Cardinal.lift_le.2 h
  obtain ⟨s, hs, hs'⟩ := hU.exists_lt_rank_forall_le hx hβ Subtype.val fun b => b.2
  have := hs' ⟨s + 1, hU.isSuccLimit_rank.add_one_lt hs⟩
  exact (lt_add_one s).not_ge this

/-- The rank of a universe is an initial ordinal. -/
theorem ord_card_rank : (rank U).card.ord = rank U := by
  refine (ord_card_le _).antisymm (not_lt.1 fun h => ?_)
  have hmem : (rank U).card.ord.toZFSet ∈ U := hU.mem_iff_rank_lt.2 (by simpa using h)
  simpa using hU.card_lt_card_rank hmem

/-- The cardinal `(rank U).card` of a universe is a strong limit. -/
theorem isStrongLimit_card_rank : (rank U).card.IsStrongLimit := by
  refine ⟨?_, fun c hc => ?_⟩
  · rw [Ne, card_eq_zero]
    exact hU.isSuccLimit_rank.ne_bot
  · have hmem : c.ord.toZFSet ∈ U := by
      rw [hU.mem_iff_rank_lt, rank_toZFSet, ← hU.ord_card_rank]
      exact ord_lt_ord.2 hc
    simpa using hU.card_lt_card_rank (hU.powerset_mem _ hmem)

/-- The cardinal `(rank U).card` of a universe is regular. -/
theorem isRegular_card_rank : (rank U).card.IsRegular := by
  refine ⟨?_, ?_⟩
  · simpa using card_le_card hU.omega0_le_rank
  rw [hU.ord_card_rank]
  by_contra! h
  have hmem : (rank U).cof.ord.toZFSet ∈ U := by
    rw [hU.mem_iff_rank_lt, rank_toZFSet]
    conv_rhs => rw [← hU.ord_card_rank]
    exact ord_lt_ord.2 h
  obtain ⟨s, hs, hs'⟩ := exists_cof_eq (Set.Iio (rank U))
  have hβ : #s ≤ #((rank U).cof.ord.toZFSet) := by
    rw [hs', cof_Iio, ← lift_cof, cardinalMk_coe_sort, card_toZFSet, card_ord]
  obtain ⟨t, ht, ht'⟩ := hU.exists_lt_rank_forall_le hmem hβ (fun b => b.1.1) fun b => b.1.2
  obtain ⟨b, hb, hb'⟩ := hs ⟨t + 1, hU.isSuccLimit_rank.add_one_lt ht⟩
  exact (lt_add_one t).not_ge ((Subtype.mk_le_mk.1 hb').trans (ht' ⟨b, hb⟩))

/-- **The cardinal of a universe** is the cardinal of its rank (Williams 1969, Theorem 2). -/
theorem card_eq_card_rank : card U = (rank U).card := by
  conv_lhs => rw [hU.eq_vonNeumann_rank, ← hU.ord_card_rank]
  exact card_vonNeumann_ord hU.isRegular_card_rank hU.isStrongLimit_card_rank

/-- The cardinal of a universe is regular. -/
theorem isRegular_card : (card U).IsRegular := hU.card_eq_card_rank ▸ hU.isRegular_card_rank

/-- The cardinal of a universe is a strong limit. -/
theorem isStrongLimit_card : (card U).IsStrongLimit :=
  hU.card_eq_card_rank ▸ hU.isStrongLimit_card_rank

/-- The initial ordinal of the cardinal of a universe is its rank. -/
theorem ord_card : (card U).ord = rank U := by
  rw [hU.card_eq_card_rank, hU.ord_card_rank]

/-- **A universe is the stage of its cardinal**: `U = V_ (card U).ord` (Williams 1969,
Theorems 1 and 2). This holds for every universe, `V_ ω` included. -/
theorem eq_vonNeumann_card : U = V_ (card U).ord := by
  rw [hU.ord_card]
  exact hU.eq_vonNeumann_rank

/-- `ω` lies in a universe exactly when its rank exceeds `ω`. -/
theorem omega_mem_iff_omega0_lt_rank : ZFSet.omega ∈ U ↔ ω < rank U := by
  rw [hU.mem_iff_rank_lt, rank_omega]

/-- **The cardinal of a universe** is inaccessible exactly when the universe contains `ω`
(Williams 1969, Theorems 1 and 2). -/
theorem isInaccessible_card : (card U).IsInaccessible ↔ ZFSet.omega ∈ U := by
  rw [hU.omega_mem_iff_omega0_lt_rank, ← hU.ord_card, lt_ord, card_omega0, isInaccessible_def]
  exact ⟨fun h => h.1, fun h => ⟨h, hU.isRegular_card, hU.isStrongLimit_card⟩⟩

/-- **Kruse's criterion**: a set lies in a universe `U` exactly when it is a subset of `U` of
cardinality smaller than `card U` (Kruse 1965, Theorem 1). -/
theorem mem_iff_subset_and_card_lt : x ∈ U ↔ x ⊆ U ∧ card x < card U := by
  refine ⟨fun hx => ⟨hU.subset_of_mem hx, hU.card_lt_card hx⟩, fun ⟨hsub, hcard⟩ => ?_⟩
  rw [hU.mem_iff_rank_lt]
  have hlt : ⨆ z : x, rank z.1 + 1 < rank U := by
    apply lift_iSup_lt_of_lt_cof
    · rw [cardinalMk_coe_sort, ← lift_cof, ← hU.ord_card, hU.isRegular_card.cof_ord,
        Cardinal.lift_lift, Cardinal.lift_lt]
      exact hcard
    · exact fun z => hU.isSuccLimit_rank.add_one_lt (hU.mem_iff_rank_lt.1 (hsub z.2))
  refine lt_of_le_of_lt (rank_le_iff.2 fun z hz => ?_) hlt
  exact (lt_add_one _).trans_le (Ordinal.le_iSup (fun z : x => rank z.1 + 1) ⟨z, hz⟩)

/-- A universe contains `ω` exactly when it has an infinite element. -/
theorem omega_mem_iff_exists_aleph0_le_card :
    ZFSet.omega ∈ U ↔ ∃ x ∈ U, ℵ₀ ≤ card x := by
  refine ⟨fun h => ⟨ZFSet.omega, h, card_omega.ge⟩, fun ⟨x, hx, hcard⟩ => ?_⟩
  rw [← hU.isInaccessible_card, isInaccessible_def]
  exact ⟨hcard.trans_lt (hU.card_lt_card hx), hU.isRegular_card, hU.isStrongLimit_card⟩

end IsGrothendieckUniverse

/-- **Universes are the regular strong limit stages**: a set is a universe exactly when it is
`V_ κ.ord` for a regular strong limit cardinal `κ` (which is then its cardinality). -/
theorem isGrothendieckUniverse_iff_exists_isRegular {U : ZFSet.{u}} :
    IsGrothendieckUniverse U ↔
      ∃ κ : Cardinal.{u}, κ.IsRegular ∧ κ.IsStrongLimit ∧ U = V_ κ.ord :=
  ⟨fun hU => ⟨card U, hU.isRegular_card, hU.isStrongLimit_card, hU.eq_vonNeumann_card⟩,
    fun ⟨_, hr, hs, h⟩ => h ▸ isGrothendieckUniverse_vonNeumann_of_isRegular hr hs⟩

/-- **Williams's theorem** (Williams 1969, Theorem 1, after Kruse 1965): the universes are
`V_ ω` and the stages `V_ κ.ord` at the inaccessible cardinals `κ`. -/
theorem isGrothendieckUniverse_iff {U : ZFSet.{u}} :
    IsGrothendieckUniverse U ↔
      U = V_ Ordinal.omega0 ∨ ∃ κ : Cardinal.{u}, κ.IsInaccessible ∧ U = V_ κ.ord := by
  refine ⟨fun hU => ?_, ?_⟩
  · by_cases h : ZFSet.omega ∈ U
    · exact .inr ⟨card U, hU.isInaccessible_card.2 h, hU.eq_vonNeumann_card⟩
    · left
      rw [hU.omega_mem_iff_omega0_lt_rank, not_lt] at h
      rw [hU.eq_vonNeumann_rank, h.antisymm hU.omega0_le_rank]
  · rintro (rfl | ⟨κ, hκ, rfl⟩)
    · exact isGrothendieckUniverse_vonNeumann_omega0
    · exact isGrothendieckUniverse_vonNeumann hκ

end LeanPool.GrothendieckUniverses
