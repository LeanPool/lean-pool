/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.PairAssignmentFacts
public import LeanPool.ApollonianSuperharmonic.TileCornerMultiplicity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.NoCheckerboardCellVertex
public import Mathlib.Algebra.Order.Ring.Star

/-!
# FiniteSquareIncidenceIdentities

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open scoped BigOperators

-- [TABLET NODE: FiniteSquareIncidenceIdentities]
namespace SquareIncidenceProof

private theorem hbagcard :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
      ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
    cornerBag.card = 4 * T.cells.card := by
  classical
  intro T I cornerBag
  simp [cornerBag, Nat.mul_comm]

private theorem hcountpos :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
      ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
    ∀ (z : GaussianInt), (z ∈ cornerBag.toFinset) → (1 ≤ cornerBag.count z) := by
  classical
  intro T I cornerBag z hz
  rw [Multiset.mem_toFinset] at hz
  exact Multiset.count_pos.mpr hz

private abbrev hvertexSet :=
  TileCornerMultiplicity.vertexSupport

private theorem hvertexCard :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
      ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
    ((cornerBag.toFinset : Set GaussianInt) = FootprintVertices T) → (cornerBag.toFinset.card =
        (FootprintVertices T).ncard) := by
  classical
  intro T I cornerBag hvertexSet
  have h := congrArg Set.ncard hvertexSet
  simpa using h

private theorem hcountle :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
      ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
    ∀ (z : GaussianInt), cornerBag.count z ≤ 4 := by
  classical
  intro T I cornerBag z
  let around : Finset GaussianInt := {z, z - 1, z - I, z - 1 - I}
  have hcornerNodup (c : GaussianInt) :
      ([c, c + 1, c + I, c + 1 + I] : List GaussianInt).Nodup := by
    simp [I, Zsqrtd.ext_iff]
  have hfilter :
      T.cells.filter (fun c => z ∈ ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)) ⊆
        around := by
    intro c hc
    rw [Finset.mem_filter] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc.2 with h | h | h | h
    · subst c
      simp [around]
    · subst z
      simp [around, I, Zsqrtd.ext_iff]
    · subst z
      simp [around, I, Zsqrtd.ext_iff]
    · subst z
      simp [around, I, Zsqrtd.ext_iff]
  calc
    cornerBag.count z = ∑ c ∈ T.cells,
        ([c, c + 1, c + I, c + 1 + I] : List GaussianInt).count z := by
      dsimp only [cornerBag]
      rw [Multiset.count_bind]
      simp
    _ = (T.cells.filter (fun c =>
        z ∈ ([c, c + 1, c + I, c + 1 + I] : List GaussianInt))).card := by
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro c hc
      exact (hcornerNodup c).count
    _ ≤ around.card := Finset.card_le_card hfilter
    _ ≤ 4 := by
      dsimp only [around]
      calc
        ({z, z - 1, z - I, z - 1 - I} : Finset GaussianInt).card ≤
            ({z - 1, z - I, z - 1 - I} : Finset GaussianInt).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ (({z - I, z - 1 - I} : Finset GaussianInt).card + 1) + 1 := by
          have h := Finset.card_insert_le (z - 1)
            ({z - I, z - 1 - I} : Finset GaussianInt)
          omega
        _ ≤ (({z - 1 - I} : Finset GaussianInt).card + 1 + 1) + 1 := by
          have h := Finset.card_insert_le (z - I)
            ({z - 1 - I} : Finset GaussianInt)
          omega
        _ ≤ 4 := by simp

private abbrev hcornerCount := ApollonianSuperharmonic.TileCornerMultiplicity.cornerCount

private theorem hweighted :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
      ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
    let N : Nat → Nat := fun k =>
      (cornerBag.toFinset.filter fun z => cornerBag.count z = k).card
    (∀ (z : GaussianInt), (z ∈ cornerBag.toFinset) → (1 ≤ cornerBag.count z)) → ((∀ (z :
        GaussianInt), cornerBag.count z ≤ 4) → (∑ z ∈ cornerBag.toFinset, cornerBag.count z =
      N 1 + 2 * N 2 + 3 * N 3 + 4 * N 4)) := by
  classical
  intro T I cornerBag N hcountpos hcountle
  rw [show (∑ z ∈ cornerBag.toFinset, cornerBag.count z) =
      ∑ z ∈ cornerBag.toFinset,
        ((if cornerBag.count z = 1 then 1 else 0) +
         (if cornerBag.count z = 2 then 2 else 0) +
         (if cornerBag.count z = 3 then 3 else 0) +
         (if cornerBag.count z = 4 then 4 else 0)) by
    apply Finset.sum_congr rfl
    intro z hz
    have hp := hcountpos z hz
    have hl := hcountle z
    have hc : cornerBag.count z = 1 ∨ cornerBag.count z = 2 ∨
        cornerBag.count z = 3 ∨ cornerBag.count z = 4 := by omega
    rcases hc with hc | hc | hc | hc <;> simp [hc]]
  simp only [Finset.sum_add_distrib]
  simp [N, Finset.sum_ite, Nat.mul_comm]

private theorem hunweighted :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
      ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
    let N : Nat → Nat := fun k =>
      (cornerBag.toFinset.filter fun z => cornerBag.count z = k).card
    (∀ (z : GaussianInt), (z ∈ cornerBag.toFinset) → (1 ≤ cornerBag.count z)) → ((∀ (z :
        GaussianInt), cornerBag.count z ≤ 4) → (cornerBag.toFinset.card = N 1 + N 2 + N 3 + N 4))
        := by
  classical
  intro T I cornerBag N hcountpos hcountle
  rw [show cornerBag.toFinset.card = ∑ z ∈ cornerBag.toFinset, 1 by simp]
  rw [show (∑ z ∈ cornerBag.toFinset, 1) =
      ∑ z ∈ cornerBag.toFinset,
        ((if cornerBag.count z = 1 then 1 else 0) +
         (if cornerBag.count z = 2 then 1 else 0) +
         (if cornerBag.count z = 3 then 1 else 0) +
         (if cornerBag.count z = 4 then 1 else 0)) by
    apply Finset.sum_congr rfl
    intro z hz
    have hp := hcountpos z hz
    have hl := hcountle z
    have hc : cornerBag.count z = 1 ∨ cornerBag.count z = 2 ∨
        cornerBag.count z = 3 ∨ cornerBag.count z = 4 := by omega
    rcases hc with hc | hc | hc | hc <;> simp [hc]]
  simp only [Finset.sum_add_distrib]
  simp [N]

private theorem hedgeBagCard :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    edgeBag.card = 4 * T.cells.card := by
  classical
  intro T I edgeBag
  simp [edgeBag, Nat.mul_comm]

private theorem hedgeCountPos :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    ∀ (e : GaussianInt × Bool), (e ∈ edgeBag.toFinset) → (1 ≤ edgeBag.count e) := by
  classical
  intro T I edgeBag e he
  rw [Multiset.mem_toFinset] at he
  exact Multiset.count_pos.mpr he

private theorem hedgeCountFalse :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    ∀ (z : GaussianInt), edgeBag.count (z, false) =
      (if z ∈ T.cells then 1 else 0) + (if z - I ∈ T.cells then 1 else 0) := by
  classical
  intro T I edgeBag z
  dsimp only [edgeBag]
  rw [Multiset.count_bind]
  rw [← Finset.sum_eq_multiset_sum]
  simp only [Multiset.coe_count, List.count_cons, beq_iff_eq,
    Prod.mk.injEq, and_false, ite_false,
    and_true, Bool.true_eq_false, Nat.zero_add,
    List.count_nil, add_zero]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq']
  have heq : ∀ c : GaussianInt, (c + I = z) ↔ (c = z - I) := by
    intro c
    constructor <;> intro h
    · rw [← h]
      ring
    · rw [h]
      ring
  simp_rw [heq]
  rw [Finset.sum_ite_eq']
  omega

private theorem hedgeCountTrue :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    ∀ (z : GaussianInt), edgeBag.count (z, true) =
      (if z ∈ T.cells then 1 else 0) + (if z - 1 ∈ T.cells then 1 else 0) := by
  classical
  intro T I edgeBag z
  dsimp only [edgeBag]
  rw [Multiset.count_bind]
  rw [← Finset.sum_eq_multiset_sum]
  simp only [Multiset.coe_count, List.count_cons, beq_iff_eq,
    Prod.mk.injEq, and_false, ite_false,
    and_true, Bool.false_eq_true, Nat.zero_add,
    List.count_nil, add_zero]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq']
  have heq : ∀ c : GaussianInt, (c + 1 = z) ↔ (c = z - 1) := by
    intro c
    constructor <;> intro h
    · rw [← h]
      ring
    · rw [h]
      ring
  simp_rw [heq]
  rw [Finset.sum_ite_eq']
  omega

private theorem hedgeCountLe :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    (∀ (z : GaussianInt), edgeBag.count (z, false) = (if z ∈ T.cells then 1 else 0) + (if z - I ∈
        T.cells then 1 else 0)) → ((∀ (z : GaussianInt), edgeBag.count (z, true) = (if z ∈
        T.cells then 1 else 0) + (if z - 1 ∈ T.cells then 1 else 0)) → (∀ (e : GaussianInt ×
        Bool), edgeBag.count e ≤ 2)) := by
  classical
  intro T I edgeBag hedgeCountFalse hedgeCountTrue e
  rcases e with ⟨z, b⟩
  cases b
  · rw [hedgeCountFalse]
    split_ifs <;> omega
  · rw [hedgeCountTrue]
    split_ifs <;> omega

private theorem hedgeMultiplicity :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    (∀ (e : GaussianInt × Bool), (e ∈ edgeBag.toFinset) → (1 ≤ edgeBag.count e)) → ((∀ (e :
        GaussianInt × Bool), edgeBag.count e ≤ 2) → (edgeBag.card =
        (edgeBag.toFinset.filter fun e => edgeBag.count e = 1).card +
          2 * (edgeBag.toFinset.filter fun e => edgeBag.count e = 2).card)) := by
  classical
  intro T I edgeBag hedgeCountPos hedgeCountLe
  rw [← Multiset.toFinset_sum_count_eq edgeBag]
  rw [show (∑ e ∈ edgeBag.toFinset, edgeBag.count e) =
      ∑ e ∈ edgeBag.toFinset,
        ((if edgeBag.count e = 1 then 1 else 0) +
         (if edgeBag.count e = 2 then 2 else 0)) by
    apply Finset.sum_congr rfl
    intro e he
    have hp := hedgeCountPos e he
    have hl := hedgeCountLe e
    have hc : edgeBag.count e = 1 ∨ edgeBag.count e = 2 := by omega
    rcases hc with hc | hc <;> simp [hc]]
  simp [Finset.sum_add_distrib, Finset.sum_ite, Nat.mul_comm]

private theorem hedgePartition :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    (∀ (e : GaussianInt × Bool), (e ∈ edgeBag.toFinset) → (1 ≤ edgeBag.count e)) → ((∀ (e :
        GaussianInt × Bool), edgeBag.count e ≤ 2) → (edgeBag.toFinset.card =
      (edgeBag.toFinset.filter fun e => edgeBag.count e = 1).card +
        (edgeBag.toFinset.filter fun e => edgeBag.count e = 2).card)) := by
  classical
  intro T I edgeBag hedgeCountPos hedgeCountLe
  rw [show edgeBag.toFinset.card = ∑ e ∈ edgeBag.toFinset, 1 by simp]
  rw [show (∑ e ∈ edgeBag.toFinset, 1) =
      ∑ e ∈ edgeBag.toFinset,
        ((if edgeBag.count e = 1 then 1 else 0) +
         (if edgeBag.count e = 2 then 1 else 0)) by
    apply Finset.sum_congr rfl
    intro e he
    have hp := hedgeCountPos e he
    have hl := hedgeCountLe e
    have hc : edgeBag.count e = 1 ∨ edgeBag.count e = 2 := by omega
    rcases hc with hc | hc <;> simp [hc]]
  simp [Finset.sum_add_distrib]

private theorem hedgeIdentity :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    (edgeBag.card = 4 * T.cells.card) → ((edgeBag.card = (edgeBag.toFinset.filter fun e =>
        edgeBag.count e = 1).card + 2 * (edgeBag.toFinset.filter fun e => edgeBag.count e =
        2).card) → ((edgeBag.toFinset.card = (edgeBag.toFinset.filter fun e => edgeBag.count e =
        1).card + (edgeBag.toFinset.filter fun e => edgeBag.count e = 2).card) → (2 *
        edgeBag.toFinset.card = 4 * T.cells.card +
      (edgeBag.toFinset.filter fun e => edgeBag.count e = 1).card))) := by
  classical
  intro T I edgeBag hedgeBagCard hedgeMultiplicity hedgePartition
  rw [hedgePartition, ← hedgeBagCard] at ⊢
  omega

private abbrev pair_eq :=
  @PairAssignmentFacts.finsetPair GaussianInt inferInstance

private theorem edgeOf_injective :
    let I : GaussianInt := ⟨0, 1⟩
    let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
      if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
    (∀ {a : GaussianInt},
        ∀ {b : GaussianInt},
          ∀ {c : GaussianInt},
            ∀ {d : GaussianInt},
              ({ a, b } : Finset GaussianInt) = { c, d } → a = c ∧ b = d ∨ a = d ∧ b = c) →
      Function.Injective edgeOf := by
  classical
  intro I edgeOf pair_eq
  rintro ⟨z, b⟩ ⟨w, d⟩ h
  cases b <;> cases d
  · change ({z, z + 1} : Finset GaussianInt) = {w, w + 1} at h
    replace h := pair_eq h
    rcases h with ⟨h, _⟩ | ⟨h1, h2⟩
    · subst w; rfl
    · exfalso
      have h1r := congrArg Zsqrtd.re h1
      have h2r := congrArg Zsqrtd.re h2
      norm_num at h1r h2r
      omega
  · change ({z, z + 1} : Finset GaussianInt) = {w, w + I} at h
    replace h := pair_eq h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exfalso
    · have h1i := congrArg Zsqrtd.im h1
      have h2i := congrArg Zsqrtd.im h2
      dsimp only [I] at h1i h2i
      norm_num at h1i h2i
      omega
    · have h1r := congrArg Zsqrtd.re h1
      have h2r := congrArg Zsqrtd.re h2
      norm_num at h1r h2r
      omega
  · change ({z, z + I} : Finset GaussianInt) = {w, w + 1} at h
    replace h := pair_eq h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exfalso
    · have h1r := congrArg Zsqrtd.re h1
      have h2r := congrArg Zsqrtd.re h2
      norm_num at h1r h2r
      omega
    · have h1i := congrArg Zsqrtd.im h1
      have h2i := congrArg Zsqrtd.im h2
      dsimp only [I] at h1i h2i
      norm_num at h1i h2i
      omega
  · change ({z, z + I} : Finset GaussianInt) = {w, w + I} at h
    replace h := pair_eq h
    rcases h with ⟨h, _⟩ | ⟨h1, h2⟩
    · subst w; rfl
    · exfalso
      have h1i := congrArg Zsqrtd.im h1
      have h2i := congrArg Zsqrtd.im h2
      dsimp only [I] at h1i h2i
      norm_num at h1i h2i
      omega

private theorem hedgeSet :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
      if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
    ((edgeBag.toFinset.image edgeOf : Finset (Finset GaussianInt)) :
        Set (Finset GaussianInt)) = FootprintEdges T := by
  classical
  intro T I edgeBag edgeOf
  ext e
  change e ∈ edgeBag.toFinset.image edgeOf ↔ e ∈ FootprintEdges T
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Multiset.mem_toFinset] at hp
    dsimp only [edgeBag] at hp
    rw [Multiset.mem_bind] at hp
    rcases hp with ⟨c, hc, hp⟩
    have hp' : p = (c, false) ∨ p = (c, true) ∨
        p = (c + I, false) ∨ p = (c + 1, true) := by
      simpa using hp
    rcases hp' with rfl | rfl | rfl | rfl
    · exact ⟨c, hc, Or.inl rfl⟩
    · exact ⟨c, hc, Or.inr (Or.inl rfl)⟩
    · refine ⟨c, hc, Or.inr (Or.inr (Or.inr ?_))⟩
      change ({c + I, c + I + 1} : Finset GaussianInt) =
        {c + I, c + 1 + I}
      congr 1; ring
    · exact ⟨c, hc, Or.inr (Or.inr (Or.inl rfl))⟩
  · rintro ⟨c, hc, he | he | he | he⟩
    · refine ⟨(c, false), ?_, ?_⟩
      · rw [Multiset.mem_toFinset]
        exact Multiset.mem_bind.mpr ⟨c, hc, by simp⟩
      · simpa [edgeOf] using he.symm
    · refine ⟨(c, true), ?_, ?_⟩
      · rw [Multiset.mem_toFinset]
        exact Multiset.mem_bind.mpr ⟨c, hc, by simp⟩
      · simpa [edgeOf] using he.symm
    · refine ⟨(c + 1, true), ?_, ?_⟩
      · rw [Multiset.mem_toFinset]
        exact Multiset.mem_bind.mpr ⟨c, hc, by simp⟩
      · simpa [edgeOf] using he.symm
    · refine ⟨(c + I, false), ?_, ?_⟩
      · rw [Multiset.mem_toFinset]
        exact Multiset.mem_bind.mpr ⟨c, hc, by simp⟩
      · rw [he]
        change ({c + I, c + I + 1} : Finset GaussianInt) =
          {c + I, c + 1 + I}
        congr 1; ring

private theorem hedgeCard :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
      if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
    (Function.Injective edgeOf) → ((((edgeBag.toFinset.image edgeOf : Finset (Finset
        GaussianInt)) : Set (Finset GaussianInt)) = FootprintEdges T) → (edgeBag.toFinset.card =
        (FootprintEdges T).ncard)) := by
  classical
  intro T I edgeBag edgeOf edgeOf_injective hedgeSet
  have h := congrArg Set.ncard hedgeSet
  rw [Set.ncard_coe_finset] at h
  rw [Finset.card_image_of_injective _ edgeOf_injective] at h
  exact h

private theorem hboundarySet :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    (∀ (z : GaussianInt), edgeBag.count (z, false) = (if z ∈ T.cells then 1 else 0) + (if z - I ∈
        T.cells then 1 else 0)) → ((∀ (z : GaussianInt), edgeBag.count (z, true) = (if z ∈
        T.cells then 1 else 0) + (if z - 1 ∈ T.cells then 1 else 0)) → (
    let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
      if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
    let boundaryTags := edgeBag.toFinset.filter fun e => edgeBag.count e = 1
    ((boundaryTags.image edgeOf : Finset (Finset GaussianInt)) :
        Set (Finset GaussianInt)) = BoundaryFootprintEdges T)) := by
  classical
  intro T I edgeBag hedgeCountFalse hedgeCountTrue edgeOf boundaryTags
  ext e
  change e ∈ boundaryTags.image edgeOf ↔ e ∈ BoundaryFootprintEdges T
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Finset.mem_filter] at hp
    rcases p with ⟨z, b⟩
    cases b
    · refine ⟨z, Or.inl ⟨rfl, ?_⟩⟩
      rw [hedgeCountFalse] at hp
      have hx : (z ∈ T.cells ∧ z - I ∉ T.cells) ∨
          (z ∉ T.cells ∧ z - I ∈ T.cells) := by
        by_cases hz : z ∈ T.cells <;> by_cases hzI : z - I ∈ T.cells
        all_goals simp [hz, hzI] at hp ⊢
      simpa only [I] using hx
    · refine ⟨z, Or.inr ⟨rfl, ?_⟩⟩
      rw [hedgeCountTrue] at hp
      by_cases hz : z ∈ T.cells <;> by_cases hz1 : z - 1 ∈ T.cells
      all_goals simp [hz, hz1] at hp ⊢
  · rintro ⟨z, hz | hz⟩
    · have hx : (z ∈ T.cells ∧ z - I ∉ T.cells) ∨
          (z ∉ T.cells ∧ z - I ∈ T.cells) := by
        simpa only [I] using hz.2
      refine ⟨(z, false), ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · rw [Multiset.mem_toFinset]
          apply Multiset.count_pos.mp
          rw [hedgeCountFalse]
          rcases hx with h | h <;> simp [h.1, h.2]
        · rw [hedgeCountFalse]
          rcases hx with h | h <;> simp [h.1, h.2]
      · simpa [edgeOf] using hz.1.symm
    · refine ⟨(z, true), ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · rw [Multiset.mem_toFinset]
          apply Multiset.count_pos.mp
          rw [hedgeCountTrue]
          rcases hz.2 with h | h <;> simp [h.1, h.2]
        · rw [hedgeCountTrue]
          rcases hz.2 with h | h <;> simp [h.1, h.2]
      · simpa [edgeOf] using hz.1.symm

private theorem hboundaryCard :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
      if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
    (Function.Injective edgeOf) → (
    let boundaryTags := edgeBag.toFinset.filter fun e => edgeBag.count e = 1
    (((boundaryTags.image edgeOf : Finset (Finset GaussianInt)) : Set (Finset GaussianInt)) =
        BoundaryFootprintEdges T) → (boundaryTags.card = (BoundaryFootprintEdges T).ncard)) := by
  classical
  intro T I edgeBag edgeOf edgeOf_injective boundaryTags hboundarySet
  have h := congrArg Set.ncard hboundarySet
  rw [Set.ncard_coe_finset] at h
  rw [Finset.card_image_of_injective _ edgeOf_injective] at h
  exact h

private theorem hboundaryEndpointCard :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    let boundaryTags := edgeBag.toFinset.filter fun e => edgeBag.count e = 1
    let boundaryEndpointBag : Multiset GaussianInt := boundaryTags.1.bind fun p =>
      if p.2 then ([p.1, p.1 + I] : List GaussianInt)
      else ([p.1, p.1 + 1] : List GaussianInt)
    boundaryEndpointBag.card = 2 * boundaryTags.card := by
  classical
  intro T I edgeBag boundaryTags boundaryEndpointBag
  simp only [boundaryEndpointBag, Multiset.card_bind]
  rw [← Finset.sum_eq_multiset_sum]
  change (∑ p ∈ boundaryTags,
      (if p.2 then ([p.1, p.1 + I] : List GaussianInt)
        else ([p.1, p.1 + 1] : List GaussianInt) : Multiset GaussianInt).card) =
    2 * boundaryTags.card
  rw [show (∑ p ∈ boundaryTags,
      (if p.2 then ([p.1, p.1 + I] : List GaussianInt)
        else ([p.1, p.1 + 1] : List GaussianInt) : Multiset GaussianInt).card) =
      boundaryTags.card * 2 by
    apply Finset.sum_const_nat
    rintro ⟨w, b⟩ hp
    cases b <;> simp]
  omega

private theorem hboundaryEndpointCount :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    let boundaryTags := edgeBag.toFinset.filter fun e => edgeBag.count e = 1
    let boundaryEndpointBag : Multiset GaussianInt := boundaryTags.1.bind fun p =>
      if p.2 then ([p.1, p.1 + I] : List GaussianInt)
      else ([p.1, p.1 + 1] : List GaussianInt)
    ∀ (z : GaussianInt), boundaryEndpointBag.count z =
      (if (z, false) ∈ boundaryTags then 1 else 0) +
      (if (z - 1, false) ∈ boundaryTags then 1 else 0) +
      (if (z, true) ∈ boundaryTags then 1 else 0) +
      (if (z - I, true) ∈ boundaryTags then 1 else 0) := by
  classical
  intro T I edgeBag boundaryTags boundaryEndpointBag z
  calc
    boundaryEndpointBag.count z = ∑ p ∈ boundaryTags,
        Multiset.count z (if p.2 then ([p.1, p.1 + I] : List GaussianInt)
          else ([p.1, p.1 + 1] : List GaussianInt) : Multiset GaussianInt) := by
      dsimp only [boundaryEndpointBag]
      rw [Multiset.count_bind]
      exact (Finset.sum_eq_multiset_sum boundaryTags fun p =>
        Multiset.count z (if p.2 then ([p.1, p.1 + I] : List GaussianInt)
          else ([p.1, p.1 + 1] : List GaussianInt) : Multiset GaussianInt)).symm
    _ = ∑ p ∈ boundaryTags,
        ((if p = (z, false) then 1 else 0) +
         (if p = (z - 1, false) then 1 else 0) +
         (if p = (z, true) then 1 else 0) +
         (if p = (z - I, true) then 1 else 0)) := by
      apply Finset.sum_congr rfl
      rintro ⟨w, b⟩ hp
      cases b
      · have hw : (w = z - 1) ↔ (z = w + 1) := by
          constructor <;> intro h
          · rw [h]; ring
          · rw [h]; ring
        simp only [Bool.false_eq,
          Prod.mk.injEq]
        by_cases h0 : z = w <;> by_cases h1 : z = w + 1
        all_goals
          first
          | solve | simp [h0, h1, hw, eq_comm, Zsqrtd.ext_iff]
          | simp [h0, eq_comm, Zsqrtd.ext_iff]
            omega
      · have hw : (w = z - I) ↔ (z = w + I) := by
          constructor <;> intro h
          · rw [h]; ring
          · rw [h]; ring
        simp only [Bool.true_eq, ite_true, Multiset.coe_count,
          List.count_cons, beq_iff_eq, List.count_nil,
          Prod.mk.injEq]
        by_cases h0 : z = w <;> by_cases hI : z = w + I
        all_goals
          first
          | solve | simp [h0, hI, hw, eq_comm, I, Zsqrtd.ext_iff]
          | simp [h0, eq_comm, I, Zsqrtd.ext_iff]
            omega
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      simp []

private theorem hboundaryFalse :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    (∀ (z : GaussianInt), edgeBag.count (z, false) = (if z ∈ T.cells then 1 else 0) + (if z - I ∈
        T.cells then 1 else 0)) → (
    let boundaryTags := edgeBag.toFinset.filter fun e => edgeBag.count e = 1
    ∀ (z : GaussianInt), (z, false) ∈ boundaryTags ↔
      (z ∈ T.cells ∧ z - I ∉ T.cells) ∨
        (z ∉ T.cells ∧ z - I ∈ T.cells)) := by
  classical
  intro T I edgeBag hedgeCountFalse boundaryTags z
  simp only [boundaryTags, Finset.mem_filter, Multiset.mem_toFinset]
  rw [← Multiset.count_pos]
  rw [hedgeCountFalse]
  by_cases hz : z ∈ T.cells <;> by_cases hzI : z - I ∈ T.cells <;>
    simp [hz, hzI]

private theorem hboundaryTrue :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    (∀ (z : GaussianInt), edgeBag.count (z, true) = (if z ∈ T.cells then 1 else 0) + (if z - 1 ∈
        T.cells then 1 else 0)) → (
    let boundaryTags := edgeBag.toFinset.filter fun e => edgeBag.count e = 1
    ∀ (z : GaussianInt), (z, true) ∈ boundaryTags ↔
      (z ∈ T.cells ∧ z - 1 ∉ T.cells) ∨
        (z ∉ T.cells ∧ z - 1 ∈ T.cells)) := by
  classical
  intro T I edgeBag hedgeCountTrue boundaryTags z
  simp only [boundaryTags, Finset.mem_filter, Multiset.mem_toFinset]
  rw [← Multiset.count_pos]
  rw [hedgeCountTrue]
  by_cases hz : z ∈ T.cells <;> by_cases hz1 : z - 1 ∈ T.cells <;>
    simp [hz, hz1]

private theorem hlocalBoundaryDegree :
    ∀ (T : ProtoTile), (NoCheckerboardCellVertex (T.cells : Set LatticeCell)) → (
    let I : GaussianInt := ⟨0, 1⟩
    let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
      ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    (∀ (z : GaussianInt), cornerBag.count z = (if z ∈ T.cells then 1 else 0) + (if z - 1 ∈
        T.cells then 1 else 0) + (if z - I ∈ T.cells then 1 else 0) + (if z - 1 - I ∈ T.cells
        then 1 else 0)) → (
    let boundaryTags := edgeBag.toFinset.filter fun e => edgeBag.count e = 1
    let boundaryEndpointBag : Multiset GaussianInt := boundaryTags.1.bind fun p =>
      if p.2 then ([p.1, p.1 + I] : List GaussianInt)
      else ([p.1, p.1 + 1] : List GaussianInt)
    (∀ (z : GaussianInt), boundaryEndpointBag.count z = (if (z, false) ∈ boundaryTags then 1 else
        0) + (if (z - 1, false) ∈ boundaryTags then 1 else 0) + (if (z, true) ∈ boundaryTags then
        1 else 0) + (if (z - I, true) ∈ boundaryTags then 1 else 0)) → ((∀ (z : GaussianInt), (z,
        false) ∈ boundaryTags ↔ (z ∈ T.cells ∧ z - I ∉ T.cells) ∨ (z ∉ T.cells ∧ z - I ∈
        T.cells)) → ((∀ (z : GaussianInt), (z, true) ∈ boundaryTags ↔ (z ∈ T.cells ∧ z - 1 ∉
        T.cells) ∨ (z ∉ T.cells ∧ z - 1 ∈ T.cells)) → (∀ (z : GaussianInt),
        boundaryEndpointBag.count z =
        if cornerBag.count z = 1 ∨ cornerBag.count z = 2 ∨
            cornerBag.count z = 3 then 2 else 0))))) := by
  classical
  intro T hcheck I cornerBag edgeBag hcornerCount boundaryTags boundaryEndpointBag
      hboundaryEndpointCount hboundaryFalse hboundaryTrue z
  rw [hboundaryEndpointCount, hcornerCount]
  simp only [hboundaryFalse z, hboundaryFalse (z - 1),
    hboundaryTrue z, hboundaryTrue (z - I)]
  have hcomm : z - I - 1 = z - 1 - I := by ring
  rw [hcomm]
  have hno := hcheck z
  by_cases h0 : z ∈ T.cells <;>
    by_cases h1 : z - 1 ∈ T.cells <;>
    by_cases hI : z - I ∈ T.cells <;>
    by_cases h1I : z - 1 - I ∈ T.cells
  all_goals simp [h0, h1, hI, h1I, I] at hno ⊢

private theorem hboundaryVertices :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
      ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    let boundaryTags := edgeBag.toFinset.filter fun e => edgeBag.count e = 1
    let boundaryEndpointBag : Multiset GaussianInt := boundaryTags.1.bind fun p =>
      if p.2 then ([p.1, p.1 + I] : List GaussianInt)
      else ([p.1, p.1 + 1] : List GaussianInt)
    (∀ (z : GaussianInt), boundaryEndpointBag.count z = if cornerBag.count z = 1 ∨
        cornerBag.count z = 2 ∨ cornerBag.count z = 3 then 2 else 0) → (
    let boundaryVertices := cornerBag.toFinset.filter fun z =>
      cornerBag.count z = 1 ∨ cornerBag.count z = 2 ∨ cornerBag.count z = 3
    boundaryEndpointBag.toFinset = boundaryVertices) := by
  classical
  intro T I cornerBag edgeBag boundaryTags boundaryEndpointBag hlocalBoundaryDegree boundaryVertices
  ext z
  simp only [boundaryVertices, Finset.mem_filter, Multiset.mem_toFinset]
  rw [← Multiset.count_pos, ← Multiset.count_pos, hlocalBoundaryDegree]
  by_cases hc : cornerBag.count z = 1 ∨ cornerBag.count z = 2 ∨
      cornerBag.count z = 3
  · rcases hc with hc | hc | hc <;> simp [hc]
  · simp [hc]

private theorem hboundaryVerticesCard :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
      ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
    let N : Nat → Nat := fun k =>
      (cornerBag.toFinset.filter fun z => cornerBag.count z = k).card
    let boundaryVertices := cornerBag.toFinset.filter fun z =>
      cornerBag.count z = 1 ∨ cornerBag.count z = 2 ∨ cornerBag.count z = 3
    boundaryVertices.card = N 1 + N 2 + N 3 := by
  classical
  intro T I cornerBag N boundaryVertices
  change (cornerBag.toFinset.filter fun z =>
    cornerBag.count z = 1 ∨ cornerBag.count z = 2 ∨
      cornerBag.count z = 3).card = N 1 + N 2 + N 3
  rw [Finset.card_filter]
  rw [show (∑ z ∈ cornerBag.toFinset,
      if cornerBag.count z = 1 ∨ cornerBag.count z = 2 ∨
          cornerBag.count z = 3 then 1 else 0) =
      ∑ z ∈ cornerBag.toFinset,
        ((if cornerBag.count z = 1 then 1 else 0) +
         (if cornerBag.count z = 2 then 1 else 0) +
         (if cornerBag.count z = 3 then 1 else 0)) by
    apply Finset.sum_congr rfl
    intro z hz
    by_cases h1 : cornerBag.count z = 1 <;>
      by_cases h2 : cornerBag.count z = 2 <;>
      by_cases h3 : cornerBag.count z = 3 <;> simp [h1, h2, h3] at *]
  simp [Finset.sum_add_distrib, N]

private theorem hboundaryNumerical :
    ∀ (T : ProtoTile),
    let I : GaussianInt := ⟨0, 1⟩
    let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
      ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
    let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
      ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
        List (GaussianInt × Bool))
    let N : Nat → Nat := fun k =>
      (cornerBag.toFinset.filter fun z => cornerBag.count z = k).card
    let boundaryTags := edgeBag.toFinset.filter fun e => edgeBag.count e = 1
    (boundaryTags.card = (BoundaryFootprintEdges T).ncard) → (
    let boundaryEndpointBag : Multiset GaussianInt := boundaryTags.1.bind fun p =>
      if p.2 then ([p.1, p.1 + I] : List GaussianInt)
      else ([p.1, p.1 + 1] : List GaussianInt)
    (boundaryEndpointBag.card = 2 * boundaryTags.card) → ((∀ (z : GaussianInt),
        boundaryEndpointBag.count z = if cornerBag.count z = 1 ∨ cornerBag.count z = 2 ∨
        cornerBag.count z = 3 then 2 else 0) → (
    let boundaryVertices := cornerBag.toFinset.filter fun z =>
      cornerBag.count z = 1 ∨ cornerBag.count z = 2 ∨ cornerBag.count z = 3
    (boundaryEndpointBag.toFinset = boundaryVertices) → ((boundaryVertices.card = N 1 + N 2 + N
        3) → (boundaryTags.card = N 1 + N 2 + N 3))))) := by
  classical
  intro T I cornerBag edgeBag N boundaryTags hboundaryCard boundaryEndpointBag
      hboundaryEndpointCard hlocalBoundaryDegree boundaryVertices hboundaryVertices
      hboundaryVerticesCard
  have hendpointSum : boundaryEndpointBag.card = 2 * boundaryVertices.card := by
    rw [← Multiset.toFinset_sum_count_eq boundaryEndpointBag,
      hboundaryVertices]
    rw [show (∑ z ∈ boundaryVertices, boundaryEndpointBag.count z) =
        ∑ z ∈ boundaryVertices, 2 by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hlocalBoundaryDegree]
      have hc := (Finset.mem_filter.mp hz).2
      simp [hc]]
    simp [Nat.mul_comm]
  rw [hboundaryEndpointCard, hboundaryVerticesCard] at hendpointSum
  omega

end SquareIncidenceProof

theorem FiniteSquareIncidenceIdentities (T : ProtoTile) (hne : T.cells.Nonempty)
    (hcheck : NoCheckerboardCellVertex (T.cells : Set LatticeCell)) :
    let I : GaussianInt := ⟨0, 1⟩
    let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
      ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
    let N : Nat → Nat := fun k =>
      (cornerBag.toFinset.filter fun z => cornerBag.count z = k).card
    4 * T.cells.card = N 1 + 2 * N 2 + 3 * N 3 + 4 * N 4 ∧
      (FootprintVertices T).ncard = N 1 + N 2 + N 3 + N 4 ∧
      2 * (FootprintEdges T).ncard = 4 * T.cells.card +
        (BoundaryFootprintEdges T).ncard ∧
      (BoundaryFootprintEdges T).ncard = N 1 + N 2 + N 3 := by
-- BODY
  classical
  dsimp only
  let I : GaussianInt := ⟨0, 1⟩
  let cornerBag : Multiset GaussianInt := T.cells.1.bind fun c =>
    ([c, c + 1, c + I, c + 1 + I] : List GaussianInt)
  let edgeBag : Multiset (GaussianInt × Bool) := T.cells.1.bind fun c =>
    ([(c, false), (c, true), (c + I, false), (c + 1, true)] :
      List (GaussianInt × Bool))
  let N : Nat → Nat := fun k =>
    (cornerBag.toFinset.filter fun z => cornerBag.count z = k).card
  have hbagcard : cornerBag.card = 4 * T.cells.card := SquareIncidenceProof.hbagcard T
  have hcountpos (z : GaussianInt) (hz : z ∈ cornerBag.toFinset) :
      1 ≤ cornerBag.count z := SquareIncidenceProof.hcountpos T z hz
  have hvertexSet : (cornerBag.toFinset : Set GaussianInt) = FootprintVertices T :=
      SquareIncidenceProof.hvertexSet T hne
  have hvertexCard : cornerBag.toFinset.card = (FootprintVertices T).ncard :=
      SquareIncidenceProof.hvertexCard T hvertexSet
  have hcountle (z : GaussianInt) : cornerBag.count z ≤ 4 := SquareIncidenceProof.hcountle T z
  have hcornerCount (z : GaussianInt) : cornerBag.count z =
      (if z ∈ T.cells then 1 else 0) +
      (if z - 1 ∈ T.cells then 1 else 0) +
      (if z - I ∈ T.cells then 1 else 0) +
      (if z - 1 - I ∈ T.cells then 1 else 0) := SquareIncidenceProof.hcornerCount T z
  have hweighted : ∑ z ∈ cornerBag.toFinset, cornerBag.count z =
      N 1 + 2 * N 2 + 3 * N 3 + 4 * N 4 := SquareIncidenceProof.hweighted T hcountpos hcountle
  have hunweighted : cornerBag.toFinset.card = N 1 + N 2 + N 3 + N 4 :=
      SquareIncidenceProof.hunweighted T hcountpos hcountle
  have hedgeBagCard : edgeBag.card = 4 * T.cells.card := SquareIncidenceProof.hedgeBagCard T
  have hedgeCountPos (e : GaussianInt × Bool) (he : e ∈ edgeBag.toFinset) :
      1 ≤ edgeBag.count e := SquareIncidenceProof.hedgeCountPos T e he
  have hedgeCountFalse (z : GaussianInt) : edgeBag.count (z, false) =
      (if z ∈ T.cells then 1 else 0) + (if z - I ∈ T.cells then 1 else 0) :=
          SquareIncidenceProof.hedgeCountFalse T z
  have hedgeCountTrue (z : GaussianInt) : edgeBag.count (z, true) =
      (if z ∈ T.cells then 1 else 0) + (if z - 1 ∈ T.cells then 1 else 0) :=
          SquareIncidenceProof.hedgeCountTrue T z
  have hedgeCountLe (e : GaussianInt × Bool) : edgeBag.count e ≤ 2 :=
      SquareIncidenceProof.hedgeCountLe T hedgeCountFalse hedgeCountTrue e
  have hedgeMultiplicity :
      edgeBag.card =
        (edgeBag.toFinset.filter fun e => edgeBag.count e = 1).card +
          2 * (edgeBag.toFinset.filter fun e => edgeBag.count e = 2).card :=
              SquareIncidenceProof.hedgeMultiplicity T hedgeCountPos hedgeCountLe
  have hedgePartition : edgeBag.toFinset.card =
      (edgeBag.toFinset.filter fun e => edgeBag.count e = 1).card +
        (edgeBag.toFinset.filter fun e => edgeBag.count e = 2).card :=
            SquareIncidenceProof.hedgePartition T hedgeCountPos hedgeCountLe
  have hedgeIdentity : 2 * edgeBag.toFinset.card = 4 * T.cells.card +
      (edgeBag.toFinset.filter fun e => edgeBag.count e = 1).card :=
          SquareIncidenceProof.hedgeIdentity T hedgeBagCard hedgeMultiplicity hedgePartition
  let edgeOf : GaussianInt × Bool → Finset GaussianInt := fun p =>
    if p.2 then {p.1, p.1 + I} else {p.1, p.1 + 1}
  have pair_eq {a b c d : GaussianInt}
      (h : ({a, b} : Finset GaussianInt) = {c, d}) :
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := SquareIncidenceProof.pair_eq (a := a) (b := b) (c :=
          c) (d := d) h
  have edgeOf_injective : Function.Injective edgeOf := SquareIncidenceProof.edgeOf_injective
      pair_eq
  have hedgeSet :
      ((edgeBag.toFinset.image edgeOf : Finset (Finset GaussianInt)) :
        Set (Finset GaussianInt)) = FootprintEdges T := SquareIncidenceProof.hedgeSet T
  have hedgeCard : edgeBag.toFinset.card = (FootprintEdges T).ncard :=
      SquareIncidenceProof.hedgeCard T edgeOf_injective hedgeSet
  let boundaryTags := edgeBag.toFinset.filter fun e => edgeBag.count e = 1
  have hboundarySet :
      ((boundaryTags.image edgeOf : Finset (Finset GaussianInt)) :
        Set (Finset GaussianInt)) = BoundaryFootprintEdges T := SquareIncidenceProof.hboundarySet
            T hedgeCountFalse hedgeCountTrue
  have hboundaryCard : boundaryTags.card = (BoundaryFootprintEdges T).ncard :=
      SquareIncidenceProof.hboundaryCard T edgeOf_injective hboundarySet
  let boundaryEndpointBag : Multiset GaussianInt := boundaryTags.1.bind fun p =>
    if p.2 then ([p.1, p.1 + I] : List GaussianInt)
    else ([p.1, p.1 + 1] : List GaussianInt)
  have hboundaryEndpointCard : boundaryEndpointBag.card = 2 * boundaryTags.card :=
      SquareIncidenceProof.hboundaryEndpointCard T
  have hboundaryEndpointCount (z : GaussianInt) : boundaryEndpointBag.count z =
      (if (z, false) ∈ boundaryTags then 1 else 0) +
      (if (z - 1, false) ∈ boundaryTags then 1 else 0) +
      (if (z, true) ∈ boundaryTags then 1 else 0) +
      (if (z - I, true) ∈ boundaryTags then 1 else 0) :=
          SquareIncidenceProof.hboundaryEndpointCount T z
  have hboundaryFalse (z : GaussianInt) : (z, false) ∈ boundaryTags ↔
      (z ∈ T.cells ∧ z - I ∉ T.cells) ∨
        (z ∉ T.cells ∧ z - I ∈ T.cells) := SquareIncidenceProof.hboundaryFalse T hedgeCountFalse z
  have hboundaryTrue (z : GaussianInt) : (z, true) ∈ boundaryTags ↔
      (z ∈ T.cells ∧ z - 1 ∉ T.cells) ∨
        (z ∉ T.cells ∧ z - 1 ∈ T.cells) := SquareIncidenceProof.hboundaryTrue T hedgeCountTrue z
  have hlocalBoundaryDegree (z : GaussianInt) :
      boundaryEndpointBag.count z =
        if cornerBag.count z = 1 ∨ cornerBag.count z = 2 ∨
            cornerBag.count z = 3 then 2 else 0 := SquareIncidenceProof.hlocalBoundaryDegree T
                hcheck hcornerCount hboundaryEndpointCount hboundaryFalse hboundaryTrue z
  let boundaryVertices := cornerBag.toFinset.filter fun z =>
    cornerBag.count z = 1 ∨ cornerBag.count z = 2 ∨ cornerBag.count z = 3
  have hboundaryVertices : boundaryEndpointBag.toFinset = boundaryVertices :=
      SquareIncidenceProof.hboundaryVertices T hlocalBoundaryDegree
  have hboundaryVerticesCard : boundaryVertices.card = N 1 + N 2 + N 3 :=
      SquareIncidenceProof.hboundaryVerticesCard T
  have hboundaryNumerical : boundaryTags.card = N 1 + N 2 + N 3 :=
      SquareIncidenceProof.hboundaryNumerical T hboundaryCard hboundaryEndpointCard
      hlocalBoundaryDegree hboundaryVertices hboundaryVerticesCard
  constructor
  · change 4 * T.cells.card = N 1 + 2 * N 2 + 3 * N 3 + 4 * N 4
    rw [← hbagcard, ← hweighted]
    exact (Multiset.toFinset_sum_count_eq cornerBag).symm
  · constructor
    · change (FootprintVertices T).ncard = N 1 + N 2 + N 3 + N 4
      rw [← hvertexCard]
      exact hunweighted
    · constructor
      · rw [← hedgeCard, ← hboundaryCard]
        exact hedgeIdentity
      · change (BoundaryFootprintEdges T).ncard = N 1 + N 2 + N 3
        rw [← hboundaryCard]
        exact hboundaryNumerical

end ApollonianSuperharmonic

end
