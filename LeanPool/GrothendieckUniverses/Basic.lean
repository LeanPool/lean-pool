/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.SetTheory.ZFC.Cardinal
public import Mathlib.SetTheory.ZFC.Ordinal
public import Mathlib.SetTheory.ZFC.Rank

/-!
# Grothendieck universes and their closure properties

A Grothendieck universe is a set `U : ZFSet` that is transitive, closed under power sets and
singletons, closed under unions of families of its elements indexed by one of its elements, and
nonempty. These are the axioms UA1–UA5 of Williams (1969), a variant of the axioms U1–U5 of
Gabriel (1962, Ch. 0, §1) in which nonemptiness replaces closure under ordered pairs.

We derive the elementary closure properties: the empty set, subsets, binary unions, unordered
and ordered pairs, unions, ranges of families, cartesian products and sets of functions all stay
inside a universe, and every element of a universe has strictly smaller cardinality than the
universe. We also record that Mathlib's `ZFSet.omega` is the von Neumann ordinal `ω`.

## References

* P. Gabriel, *Des catégories abéliennes*, Bull. Soc. Math. France 90 (1962), 323–448.
* N. H. Williams, *On Grothendieck universes*, Compositio Math. 21 (1969), 1–3.
-/

@[expose] public section

namespace LeanPool.GrothendieckUniverses

open ZFSet Cardinal

universe u

/-- A **Grothendieck universe**, with the axioms of Williams (1969), after Gabriel (1962):
transitive, closed under power sets, singletons and unions of families indexed by an element,
and nonempty. -/
structure IsGrothendieckUniverse (U : ZFSet.{u}) : Prop where
  /-- Every element of an element of `U` is in `U`. -/
  isTransitive : U.IsTransitive
  /-- `U` is closed under power sets. -/
  powerset_mem : ∀ x ∈ U, x.powerset ∈ U
  /-- `U` is closed under singletons. -/
  singleton_mem : ∀ x ∈ U, ({x} : ZFSet.{u}) ∈ U
  /-- The union of a family of elements of `U` indexed by an element of `U` is in `U`. -/
  iUnion_mem : ∀ I ∈ U, ∀ f : I → ZFSet.{u}, (∀ i, f i ∈ U) → iUnion f ∈ U
  /-- `U` is nonempty. -/
  nonempty : U ≠ ∅

/-- The empty set is not a universe. -/
theorem not_isGrothendieckUniverse_empty : ¬ IsGrothendieckUniverse (∅ : ZFSet.{u}) :=
  fun h => h.nonempty rfl

namespace IsGrothendieckUniverse

variable {U x y : ZFSet.{u}} (hU : IsGrothendieckUniverse U)
include hU

/-- An element of an element of a universe lies in the universe. -/
theorem mem_of_mem (hy : y ∈ U) (hxy : x ∈ y) : x ∈ U := hU.isTransitive _ hy hxy

/-- An element of a universe is a subset of it. -/
theorem subset_of_mem (hx : x ∈ U) : x ⊆ U := hU.isTransitive _ hx

/-- A universe is closed under subsets of its elements. -/
theorem mem_of_subset (hy : y ∈ U) (hxy : x ⊆ y) : x ∈ U :=
  hU.mem_of_mem (hU.powerset_mem y hy) (mem_powerset.2 hxy)

/-- The empty set lies in every universe. -/
theorem empty_mem : (∅ : ZFSet.{u}) ∈ U := by
  obtain ⟨x, hx⟩ := (eq_empty_or_nonempty U).resolve_left hU.nonempty
  exact hU.mem_of_subset hx (empty_subset x)

/-- A universe is closed under separation. -/
theorem sep_mem (hx : x ∈ U) (p : ZFSet.{u} → Prop) : x.sep p ∈ U :=
  hU.mem_of_subset hx sep_subset

/-- A universe is closed under binary intersections. -/
theorem inter_mem (hx : x ∈ U) : x ∩ y ∈ U := hU.sep_mem hx _

/-- A universe is closed under differences. -/
theorem sdiff_mem (hx : x ∈ U) : x \ y ∈ U :=
  hU.mem_of_subset hx fun _ hz => (mem_sdiff.1 hz).1

/-- A universe is closed under unions `⋃₀`. -/
theorem sUnion_mem (hx : x ∈ U) : ⋃₀ x ∈ U := by
  have := hU.iUnion_mem x hx (fun i => i.1) fun i => hU.mem_of_mem hx i.2
  convert this using 1
  ext z
  simp [mem_sUnion, mem_iUnion]

/-- A universe is closed under binary unions: `x ∪ y` is the union of a family indexed by the
two-element set `𝒫 {∅}`. -/
theorem union_mem (hx : x ∈ U) (hy : y ∈ U) : x ∪ y ∈ U := by
  have hI : powerset {(∅ : ZFSet.{u})} ∈ U :=
    hU.powerset_mem _ (hU.singleton_mem _ hU.empty_mem)
  classical
  have := hU.iUnion_mem _ hI (fun i => if i.1 = ∅ then x else y) fun i => by
    split_ifs <;> assumption
  convert this using 1
  ext z
  simp only [mem_union, mem_iUnion]
  constructor
  · rintro (h | h)
    · exact ⟨⟨∅, by simp⟩, by simpa using h⟩
    · have hne : ({∅} : ZFSet.{u}) ≠ ∅ := fun h' => by
        simpa using ZFSet.ext_iff.1 h' ∅
      exact ⟨⟨{∅}, by simp⟩, by simpa [hne] using h⟩
  · rintro ⟨i, hi⟩
    split_ifs at hi
    · exact .inl hi
    · exact .inr hi

/-- A universe is closed under insertion. -/
theorem insert_mem (hx : x ∈ U) (hy : y ∈ U) : insert x y ∈ U := by
  rw [insert_eq]
  exact hU.union_mem (hU.singleton_mem _ hx) hy

/-- A universe is closed under unordered pairs. -/
theorem pair_mem (hx : x ∈ U) (hy : y ∈ U) : ({x, y} : ZFSet.{u}) ∈ U :=
  hU.insert_mem hx (hU.singleton_mem _ hy)

/-- An unordered pair lies in a universe exactly when both its elements do. -/
theorem pair_mem_iff : ({x, y} : ZFSet.{u}) ∈ U ↔ x ∈ U ∧ y ∈ U :=
  ⟨fun h => ⟨hU.mem_of_mem h (by simp), hU.mem_of_mem h (by simp)⟩,
    fun h => hU.pair_mem h.1 h.2⟩

/-- An ordered pair lies in a universe exactly when both its components do. -/
theorem orderedPair_mem_iff : pair x y ∈ U ↔ x ∈ U ∧ y ∈ U := by
  rw [pair, hU.pair_mem_iff, hU.pair_mem_iff]
  refine ⟨fun h => h.2, fun h => ⟨hU.singleton_mem _ h.1, h⟩⟩

/-- A universe is closed under ordered pairs (Gabriel's axiom U3). -/
theorem orderedPair_mem (hx : x ∈ U) (hy : y ∈ U) : pair x y ∈ U :=
  (hU.orderedPair_mem_iff).2 ⟨hx, hy⟩

/-- The range of a family of elements of `U` indexed by an element of `U` lies in `U`. -/
theorem range_mem {I : ZFSet.{u}} (hI : I ∈ U) (f : I → ZFSet.{u}) (hf : ∀ i, f i ∈ U) :
    range f ∈ U := by
  have := hU.iUnion_mem I hI (fun i => {f i}) fun i => hU.singleton_mem _ (hf i)
  convert this using 1
  ext z
  simp [mem_range, mem_iUnion, eq_comm]

/-- A universe is closed under cartesian products. -/
theorem prod_mem (hx : x ∈ U) (hy : y ∈ U) : prod x y ∈ U := by
  refine hU.mem_of_subset (hU.powerset_mem _ (hU.powerset_mem _ (hU.union_mem hx hy))) ?_
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.1 hz
  rw [mem_powerset]
  intro w hw
  rw [mem_powerset]
  rcases mem_pair.1 hw with rfl | rfl <;> intro t ht
  · rw [mem_singleton.1 ht]; exact mem_union.2 (.inl ha)
  · rcases mem_pair.1 ht with rfl | rfl
    · exact mem_union.2 (.inl ha)
    · exact mem_union.2 (.inr hb)

/-- A universe is closed under sets of functions. -/
theorem funs_mem (hx : x ∈ U) (hy : y ∈ U) : funs x y ∈ U :=
  hU.mem_of_subset (hU.powerset_mem _ (hU.prod_mem hx hy)) fun _ hf =>
    mem_powerset.2 (mem_funs.1 hf).1

/-- Every element of a universe has strictly smaller cardinality than the universe. -/
theorem card_lt_card (hx : x ∈ U) : card x < card U :=
  (cantor _).trans_le <| by
    rw [← card_powerset]
    exact card_mono (hU.subset_of_mem (hU.powerset_mem x hx))

end IsGrothendieckUniverse

/-! ### The von Neumann ordinal `ω` -/

/-- The finite von Neumann ordinal `n` is Mathlib's pre-set `PSet.ofNat n`. -/
theorem toZFSet_natCast (n : ℕ) : (n : Ordinal.{u}).toZFSet = mk (PSet.ofNat n) := by
  induction n with
  | zero => simp; rfl
  | succ n ih => rw [Nat.cast_succ, Ordinal.toZFSet_add_one, ih]; rfl

/-- Mathlib's `ZFSet.omega` is the von Neumann ordinal `ω`. -/
theorem omega_eq_toZFSet_omega0 : omega.{u} = Ordinal.omega0.toZFSet := by
  ext x
  rw [← mk_out x, omega, mk_mem_iff, PSet.mem_def, Ordinal.mem_toZFSet_iff]
  constructor
  · rintro ⟨⟨n⟩, h⟩
    exact ⟨n, Ordinal.natCast_lt_omega0 n, by rw [toZFSet_natCast]; exact (sound h).symm⟩
  · rintro ⟨a, ha, h⟩
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 ha
    rw [toZFSet_natCast] at h
    exact ⟨⟨n⟩, (exact h).symm⟩

/-- The rank of `ω` is `ω`. -/
@[simp]
theorem rank_omega : rank omega.{u} = Ordinal.omega0 := by
  rw [omega_eq_toZFSet_omega0, Ordinal.rank_toZFSet]

/-- The cardinality of `ω` is `ℵ₀`. -/
@[simp]
theorem card_omega : card omega.{u} = ℵ₀ := by
  rw [omega_eq_toZFSet_omega0, Ordinal.card_toZFSet, Ordinal.card_omega0]

end LeanPool.GrothendieckUniverses
