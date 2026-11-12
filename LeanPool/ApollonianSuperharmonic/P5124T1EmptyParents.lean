/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5124T1ParentModel
public import LeanPool.ApollonianSuperharmonic.P5124T1BoundaryGeometry
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: P5124T1EmptyParents]

/-!
# P5124T1EmptyParents

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace EmptyParentGeometry

private theorem hDe :
    let D := DiamondTile 1
    let sqE : Set (Finset GaussianInt) := {e |
      e = {⟨-1, 0⟩, ⟨0, 0⟩} ∨ e = {⟨0, 0⟩, ⟨1, 0⟩} ∨
      e = {⟨-1, 2⟩, ⟨0, 2⟩} ∨ e = {⟨0, 2⟩, ⟨1, 2⟩} ∨
      e = {⟨-1, 0⟩, ⟨-1, 1⟩} ∨ e = {⟨1, 0⟩, ⟨1, 1⟩} ∨
      e = {⟨-1, 1⟩, ⟨-1, 2⟩} ∨ e = {⟨1, 1⟩, ⟨1, 2⟩}}
    let r : Int → Int := fun b => min (b + 1) (2 * (1 : Int) - b)
    let H : Int → Int → Prop := fun a b =>
      ((b = 0 ∨ b = 2 * (1 : Int)) ∧ -1 ≤ a ∧ a < 1) ∨
      (1 ≤ b ∧ b < 1 ∧ (a = -b - 1 ∨ a = b)) ∨
      ((1 : Int) < b ∧ b < 2 * (1 : Int) ∧
        (a = b - 2 * (1 : Int) - 1 ∨ a = 2 * (1 : Int) - b))
    let E : Set (Finset GaussianInt) := {e | ∃ a b : Int,
      (H a b ∧ e = {⟨a, b⟩, ⟨a + 1, b⟩}) ∨
      (0 ≤ b ∧ b < 2 * (1 : Int) ∧ (a = -r b ∨ a = r b) ∧
        e = {⟨a, b⟩, ⟨a, b + 1⟩})}
    (BoundaryFootprintEdges D = E ∧ BoundaryFootprintVertices D = {z : GaussianInt | ∃ e ∈ E, z ∈
        e}) → BoundaryFootprintEdges D = sqE := by
  classical
  intro D sqE r H E hgeom
  change BoundaryFootprintEdges (DiamondTile 1) = sqE
  rw [hgeom.1]
  ext e
  constructor
  · rintro ⟨a, b, h⟩
    rcases h with ⟨hh, rfl⟩ | ⟨hb0, hb2, ha, rfl⟩
    · rcases hh with ⟨hrow, hlo, hhi⟩ | ⟨hb1, hb2, ha⟩ | ⟨hb1, hb2, ha⟩
      · rcases hrow with hrow | hrow
        · subst b
          have : a = -1 ∨ a = 0 := by omega
          rcases this with rfl | rfl <;> simp [sqE]
        · subst b
          have : a = -1 ∨ a = 0 := by omega
          rcases this with rfl | rfl <;> simp [sqE]
      · omega
      · omega
    · have hb : b = 0 ∨ b = 1 := by omega
      rcases hb with rfl | rfl <;>
        rcases ha with ha | ha <;> subst a <;> simp [sqE, r]
  · intro he
    rcases he with h | h | h | h | h | h | h | h <;> subst e
    · exact ⟨-1, 0, Or.inl ⟨by norm_num [H], by norm_num⟩⟩
    · exact ⟨0, 0, Or.inl ⟨by norm_num [H], by norm_num⟩⟩
    · exact ⟨-1, 2, Or.inl ⟨by norm_num [H], by norm_num⟩⟩
    · exact ⟨0, 2, Or.inl ⟨by norm_num [H], by norm_num⟩⟩
    · exact ⟨-1, 0, Or.inr ⟨by norm_num, by norm_num, Or.inl (by norm_num [r]), by norm_num⟩⟩
    · exact ⟨1, 0, Or.inr ⟨by norm_num, by norm_num, Or.inr (by norm_num [r]), by norm_num⟩⟩
    · exact ⟨-1, 1, Or.inr ⟨by norm_num, by norm_num, Or.inl (by norm_num [r]), by norm_num⟩⟩
    · exact ⟨1, 1, Or.inr ⟨by norm_num, by norm_num, Or.inr (by norm_num [r]), by norm_num⟩⟩

private theorem hDv :
    let D := DiamondTile 1
    let sqE : Set (Finset GaussianInt) := {e |
      e = {⟨-1, 0⟩, ⟨0, 0⟩} ∨ e = {⟨0, 0⟩, ⟨1, 0⟩} ∨
      e = {⟨-1, 2⟩, ⟨0, 2⟩} ∨ e = {⟨0, 2⟩, ⟨1, 2⟩} ∨
      e = {⟨-1, 0⟩, ⟨-1, 1⟩} ∨ e = {⟨1, 0⟩, ⟨1, 1⟩} ∨
      e = {⟨-1, 1⟩, ⟨-1, 2⟩} ∨ e = {⟨1, 1⟩, ⟨1, 2⟩}}
    let sqV : Set GaussianInt := {⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩,
      ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩}
    let r : Int → Int := fun b => min (b + 1) (2 * (1 : Int) - b)
    let H : Int → Int → Prop := fun a b =>
      ((b = 0 ∨ b = 2 * (1 : Int)) ∧ -1 ≤ a ∧ a < 1) ∨
      (1 ≤ b ∧ b < 1 ∧ (a = -b - 1 ∨ a = b)) ∨
      ((1 : Int) < b ∧ b < 2 * (1 : Int) ∧
        (a = b - 2 * (1 : Int) - 1 ∨ a = 2 * (1 : Int) - b))
    let E : Set (Finset GaussianInt) := {e | ∃ a b : Int,
      (H a b ∧ e = {⟨a, b⟩, ⟨a + 1, b⟩}) ∨
      (0 ≤ b ∧ b < 2 * (1 : Int) ∧ (a = -r b ∨ a = r b) ∧
        e = {⟨a, b⟩, ⟨a, b + 1⟩})}
    (BoundaryFootprintEdges D = E ∧ BoundaryFootprintVertices D = {z : GaussianInt | ∃ e ∈ E, z ∈
        e}) → (BoundaryFootprintEdges D = sqE) → BoundaryFootprintVertices D = sqV := by
  classical
  intro D sqE sqV r H E hgeom hDe
  have hE : E = sqE := hgeom.1.symm.trans hDe
  rw [hgeom.2, hE]
  ext z
  simp only [Set.mem_ofPred_eq, sqE, sqV]
  constructor
  · rintro ⟨e, (h | h | h | h | h | h | h | h), hz⟩ <;> subst e
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz <;> subst z <;> simp []
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz | hz | hz | hz | hz | hz | hz
    · subst z; exact ⟨{⟨-1, 0⟩, ⟨0, 0⟩}, by simp [], by simp⟩
    · subst z; exact ⟨{⟨0, 0⟩, ⟨1, 0⟩}, by simp [], by simp⟩
    · subst z; exact ⟨{⟨1, 0⟩, ⟨1, 1⟩}, by simp [], by simp⟩
    · subst z; exact ⟨{⟨-1, 0⟩, ⟨-1, 1⟩}, by simp [], by simp⟩
    · subst z; exact ⟨{⟨1, 0⟩, ⟨1, 1⟩}, by simp [], by simp⟩
    · subst z; exact ⟨{⟨-1, 1⟩, ⟨-1, 2⟩}, by simp [], by simp⟩
    · subst z; exact ⟨{⟨-1, 2⟩, ⟨0, 2⟩}, by simp [], by simp⟩
    · subst z; exact ⟨{⟨0, 2⟩, ⟨1, 2⟩}, by simp [], by simp⟩

private theorem hBv :
    let D := DiamondTile 1
    let B := TileTranslation D ⟨0, -2⟩
    let sqV : Set GaussianInt := {⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩,
      ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩}
    (BoundaryFootprintVertices D = sqV) →
    let lowV : Set GaussianInt := {⟨-1, -2⟩, ⟨0, -2⟩, ⟨1, -2⟩,
      ⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩}
    (BoundaryFootprintVertices (TileTranslation D ⟨(0 : ℤ), (-2 : ℤ)⟩) =
        GaussianTranslation ⟨(0 : ℤ), (-2 : ℤ)⟩ '' BoundaryFootprintVertices D) →
        BoundaryFootprintVertices B = lowV := by
  classical
  intro D B sqV hDv lowV hBV
  rw [hBV, hDv]
  ext z
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [sqV, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx | hx | hx | hx | hx <;>
      subst x <;> simp [GaussianTranslation, lowV, Zsqrtd.ext_iff]
  · intro hz
    simp only [lowV, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz | hz | hz | hz | hz | hz | hz <;> subst z
    · exact ⟨⟨-1, 0⟩, by simp [sqV], by simp [GaussianTranslation]⟩
    · exact ⟨⟨0, 0⟩, by simp [sqV], by simp [GaussianTranslation]⟩
    · exact ⟨⟨1, 0⟩, by simp [sqV], by simp [GaussianTranslation]⟩
    · exact ⟨⟨-1, 1⟩, by simp [sqV], by simp [GaussianTranslation]⟩
    · exact ⟨⟨1, 1⟩, by simp [sqV], by simp [GaussianTranslation]⟩
    · exact ⟨⟨-1, 2⟩, by simp [sqV], by simp [GaussianTranslation]⟩
    · exact ⟨⟨0, 2⟩, by simp [sqV], by simp [GaussianTranslation]⟩
    · exact ⟨⟨1, 2⟩, by simp [sqV], by simp [GaussianTranslation]⟩

private theorem pairEq :
    ∀ {α : Type}, ∀ [DecidableEq α], ∀ (a : α), ∀ (b : α), ∀ (c : α), ∀ (d : α), ({a, b} : Finset
        α) = {c, d} ↔
        (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  intro α typeDecidability a b c d
  constructor
  · intro h
    have hs : ({a, b} : Set α) = {c, d} := by
      simpa only [Finset.coe_insert, Finset.coe_singleton] using
        congrArg (fun s : Finset α => (s : Set α)) h
    exact Set.pair_eq_pair_iff.mp hs
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.pair_comm _ _

private theorem hDBe :
    let D := DiamondTile 1
    let B := TileTranslation D ⟨0, -2⟩
    let sqE : Set (Finset GaussianInt) := {e |
      e = {⟨-1, 0⟩, ⟨0, 0⟩} ∨ e = {⟨0, 0⟩, ⟨1, 0⟩} ∨
      e = {⟨-1, 2⟩, ⟨0, 2⟩} ∨ e = {⟨0, 2⟩, ⟨1, 2⟩} ∨
      e = {⟨-1, 0⟩, ⟨-1, 1⟩} ∨ e = {⟨1, 0⟩, ⟨1, 1⟩} ∨
      e = {⟨-1, 1⟩, ⟨-1, 2⟩} ∨ e = {⟨1, 1⟩, ⟨1, 2⟩}}
    (BoundaryFootprintEdges D = sqE) →
    let lowE : Set (Finset GaussianInt) := {e |
      e = {⟨-1, -2⟩, ⟨0, -2⟩} ∨ e = {⟨0, -2⟩, ⟨1, -2⟩} ∨
      e = {⟨-1, 0⟩, ⟨0, 0⟩} ∨ e = {⟨0, 0⟩, ⟨1, 0⟩} ∨
      e = {⟨-1, -2⟩, ⟨-1, -1⟩} ∨ e = {⟨1, -2⟩, ⟨1, -1⟩} ∨
      e = {⟨-1, -1⟩, ⟨-1, 0⟩} ∨ e = {⟨1, -1⟩, ⟨1, 0⟩}}
    (BoundaryFootprintEdges B = lowE) →
    let capE : Set (Finset GaussianInt) := {e |
      e = {⟨-1, 0⟩, ⟨0, 0⟩} ∨ e = {⟨0, 0⟩, ⟨1, 0⟩}}
    (∀ {α : Type}, ∀ [DecidableEq α], ∀ (a : α), ∀ (b : α), ∀ (c : α), ∀ (d : α), ({a, b} :
        Finset α) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c)) → BoundaryFootprintEdges D ∩
        BoundaryFootprintEdges B = capE := by
  classical
  intro D B sqE hDe lowE hBe capE pairEq
  rw [hDe, hBe]
  ext e
  change (e ∈ sqE ∧ e ∈ lowE) ↔ e ∈ capE
  constructor
  · rintro ⟨hd, hb⟩
    change e = {⟨-1, 0⟩, ⟨0, 0⟩} ∨ e = {⟨0, 0⟩, ⟨1, 0⟩} ∨
      e = {⟨-1, 2⟩, ⟨0, 2⟩} ∨ e = {⟨0, 2⟩, ⟨1, 2⟩} ∨
      e = {⟨-1, 0⟩, ⟨-1, 1⟩} ∨ e = {⟨1, 0⟩, ⟨1, 1⟩} ∨
      e = {⟨-1, 1⟩, ⟨-1, 2⟩} ∨ e = {⟨1, 1⟩, ⟨1, 2⟩} at hd
    change e = {⟨-1, -2⟩, ⟨0, -2⟩} ∨ e = {⟨0, -2⟩, ⟨1, -2⟩} ∨
      e = {⟨-1, 0⟩, ⟨0, 0⟩} ∨ e = {⟨0, 0⟩, ⟨1, 0⟩} ∨
      e = {⟨-1, -2⟩, ⟨-1, -1⟩} ∨ e = {⟨1, -2⟩, ⟨1, -1⟩} ∨
      e = {⟨-1, -1⟩, ⟨-1, 0⟩} ∨ e = {⟨1, -1⟩, ⟨1, 0⟩} at hb
    change e = {⟨-1, 0⟩, ⟨0, 0⟩} ∨ e = {⟨0, 0⟩, ⟨1, 0⟩}
    rcases hb with hb | hb | hb | hb | hb | hb | hb | hb
    all_goals
      rw [hb] at hd ⊢
      first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | exfalso
        rcases hd with hd | hd | hd | hd | hd | hd | hd | hd
        all_goals
          have hp := (pairEq _ _ _ _).mp hd
          rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
          all_goals
            simp only [Zsqrtd.ext_iff] at h1 h2
            omega
  · intro he
    change e = {⟨-1, 0⟩, ⟨0, 0⟩} ∨ e = {⟨0, 0⟩, ⟨1, 0⟩} at he
    rcases he with he | he
    · subst e
      constructor <;> decide +kernel
    · subst e
      constructor <;> decide +kernel

private theorem hUe :
    let U := P5124T1ParentModel 1 1 true
    (U.cells = {⟨-2, 0⟩}) →
    let unitE : Set (Finset GaussianInt) := {e |
      e = {⟨-2, 0⟩, ⟨-1, 0⟩} ∨ e = {⟨-2, 0⟩, ⟨-2, 1⟩} ∨
      e = {⟨-1, 0⟩, ⟨-1, 1⟩} ∨ e = {⟨-2, 1⟩, ⟨-1, 1⟩}}
    BoundaryFootprintEdges U = unitE := by
  classical
  intro U hUc unitE
  ext e
  constructor
  · intro he
    change ∃ z : GaussianInt, _ at he
    rcases he with ⟨z, he⟩
    cases z with
    | mk x y =>
        simp? [hUc, Zsqrtd.ext_iff,
          sub_eq_add_neg, add_comm] at he
        rcases he with ⟨he, hc⟩ | ⟨he, hc⟩
        all_goals
          rcases hc with hc | hc
          all_goals
            have hx : x = -2 ∨ x = -1 := by omega
            have hy : y = 0 ∨ y = 1 := by omega
            rcases hx with hx | hx <;> rcases hy with hy | hy <;>
              subst x <;> subst y <;> subst e <;> first | omega | decide +kernel
  · intro he
    simp only [unitE, Set.mem_ofPred_eq] at he
    rcases he with he | he | he | he <;> subst e
    · exact ⟨⟨-2, 0⟩, by decide +kernel⟩
    · exact ⟨⟨-2, 0⟩, by decide +kernel⟩
    · exact ⟨⟨-1, 0⟩, by decide +kernel⟩
    · exact ⟨⟨-2, 1⟩, by decide +kernel⟩

private theorem hUv :
    let U := P5124T1ParentModel 1 1 true
    let unitE : Set (Finset GaussianInt) := {e |
      e = {⟨-2, 0⟩, ⟨-1, 0⟩} ∨ e = {⟨-2, 0⟩, ⟨-2, 1⟩} ∨
      e = {⟨-1, 0⟩, ⟨-1, 1⟩} ∨ e = {⟨-2, 1⟩, ⟨-1, 1⟩}}
    let unitV : Set GaussianInt := {⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, 1⟩, ⟨-1, 1⟩}
    (BoundaryFootprintEdges U = unitE) → (U.cells.Nonempty) → BoundaryFootprintVertices U = unitV
        := by
  classical
  intro U unitE unitV hUe hUne
  rw [BoundaryFootprintVertices, ite_eq_left hUne, hUe]
  ext z
  change (∃ e, e ∈ unitE ∧ z ∈ e) ↔ z ∈ unitV
  constructor
  · rintro ⟨e, he, hz⟩
    simp only [unitE, Set.mem_ofPred_eq] at he
    rcases he with he | he | he | he
    all_goals
      subst e
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz <;> subst z <;> simp [unitV]
  · intro hz
    simp only [unitV, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz | hz | hz <;> subst z
    · exact ⟨{⟨-2, 0⟩, ⟨-1, 0⟩}, Or.inl rfl, by simp⟩
    · exact ⟨{⟨-2, 0⟩, ⟨-1, 0⟩}, Or.inl rfl, by simp⟩
    · exact ⟨{⟨-2, 1⟩, ⟨-1, 1⟩}, Or.inr (Or.inr (Or.inr rfl)), by simp⟩
    · exact ⟨{⟨-1, 0⟩, ⟨-1, 1⟩}, Or.inr (Or.inr (Or.inl rfl)), by simp⟩

private theorem hWe :
    let U := P5124T1ParentModel 1 1 true
    let W := P5124T1ParentModel 1 0 false
    let unitE : Set (Finset GaussianInt) := {e |
      e = {⟨-2, 0⟩, ⟨-1, 0⟩} ∨ e = {⟨-2, 0⟩, ⟨-2, 1⟩} ∨
      e = {⟨-1, 0⟩, ⟨-1, 1⟩} ∨ e = {⟨-2, 1⟩, ⟨-1, 1⟩}}
    (BoundaryFootprintEdges U = unitE) → (W = TileTranslation U ⟨3, 0⟩) → (BoundaryFootprintEdges
        (TileTranslation U ⟨(3 : ℤ), (0 : ℤ)⟩) = (fun (e : Finset GaussianInt) =>
        Finset.image (GaussianTranslation ⟨(3 : ℤ), (0 : ℤ)⟩) e) ''
        BoundaryFootprintEdges U) →
    let rightE : Set (Finset GaussianInt) := {e |
      e = {⟨1, 0⟩, ⟨2, 0⟩} ∨ e = {⟨1, 0⟩, ⟨1, 1⟩} ∨
      e = {⟨2, 0⟩, ⟨2, 1⟩} ∨ e = {⟨1, 1⟩, ⟨2, 1⟩}}
    (GaussianTranslation ⟨3, 0⟩ ⟨-2, 0⟩ = ⟨1, 0⟩) → (GaussianTranslation ⟨3, 0⟩ ⟨-1, 0⟩ = ⟨2, 0⟩)
        → (GaussianTranslation ⟨3, 0⟩ ⟨-2, 1⟩ = ⟨1, 1⟩) → (GaussianTranslation ⟨3, 0⟩ ⟨-1, 1⟩ =
        ⟨2, 1⟩) → (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (c : GaussianInt), ∀ (d :
            GaussianInt), (GaussianTranslation ⟨3, 0⟩ a = c) → (GaussianTranslation ⟨3, 0⟩ b = d) →
        ({a, b} : Finset GaussianInt).image (GaussianTranslation ⟨3, 0⟩) = {c, d}) →
        BoundaryFootprintEdges W = rightE := by
  classical
  intro U W unitE hUe hWt hWtE rightE gt20 gt10 gt21 gt11 imagePair
  rw [hWt, hWtE, hUe]
  ext e
  change (∃ f, f ∈ unitE ∧
    f.image (GaussianTranslation ⟨3, 0⟩) = e) ↔ e ∈ rightE
  constructor
  · rintro ⟨f, hf, rfl⟩
    change f = {⟨-2, 0⟩, ⟨-1, 0⟩} ∨
      f = {⟨-2, 0⟩, ⟨-2, 1⟩} ∨
      f = {⟨-1, 0⟩, ⟨-1, 1⟩} ∨
      f = {⟨-2, 1⟩, ⟨-1, 1⟩} at hf
    rcases hf with hf | hf | hf | hf
    · subst f
      rw [imagePair _ _ _ _ gt20 gt10]
      exact Or.inl rfl
    · subst f
      rw [imagePair _ _ _ _ gt20 gt21]
      exact Or.inr (Or.inl rfl)
    · subst f
      rw [imagePair _ _ _ _ gt10 gt11]
      exact Or.inr (Or.inr (Or.inl rfl))
    · subst f
      rw [imagePair _ _ _ _ gt21 gt11]
      exact Or.inr (Or.inr (Or.inr rfl))
  · intro he
    change e = {⟨1, 0⟩, ⟨2, 0⟩} ∨ e = {⟨1, 0⟩, ⟨1, 1⟩} ∨
      e = {⟨2, 0⟩, ⟨2, 1⟩} ∨ e = {⟨1, 1⟩, ⟨2, 1⟩} at he
    rcases he with he | he | he | he
    · subst e
      refine ⟨({⟨-2, 0⟩, ⟨-1, 0⟩} : Finset GaussianInt),
        ?_, imagePair _ _ _ _ gt20 gt10⟩
      change ({⟨-2, 0⟩, ⟨-1, 0⟩} : Finset GaussianInt) = _ ∨ _ ∨ _ ∨ _
      exact Or.inl rfl
    · subst e
      refine ⟨({⟨-2, 0⟩, ⟨-2, 1⟩} : Finset GaussianInt),
        ?_, imagePair _ _ _ _ gt20 gt21⟩
      change _ ∨ ({⟨-2, 0⟩, ⟨-2, 1⟩} : Finset GaussianInt) = _ ∨ _ ∨ _
      exact Or.inr (Or.inl rfl)
    · subst e
      refine ⟨({⟨-1, 0⟩, ⟨-1, 1⟩} : Finset GaussianInt),
        ?_, imagePair _ _ _ _ gt10 gt11⟩
      change _ ∨ _ ∨ ({⟨-1, 0⟩, ⟨-1, 1⟩} : Finset GaussianInt) = _ ∨ _
      exact Or.inr (Or.inr (Or.inl rfl))
    · subst e
      refine ⟨({⟨-2, 1⟩, ⟨-1, 1⟩} : Finset GaussianInt),
        ?_, imagePair _ _ _ _ gt21 gt11⟩
      change _ ∨ _ ∨ _ ∨
        ({⟨-2, 1⟩, ⟨-1, 1⟩} : Finset GaussianInt) = _
      exact Or.inr (Or.inr (Or.inr rfl))

private theorem hWv :
    let U := P5124T1ParentModel 1 1 true
    let W := P5124T1ParentModel 1 0 false
    let unitV : Set GaussianInt := {⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, 1⟩, ⟨-1, 1⟩}
    (BoundaryFootprintVertices U = unitV) → (W = TileTranslation U ⟨3, 0⟩) →
        (BoundaryFootprintVertices (TileTranslation U ⟨(3 : ℤ), (0 : ℤ)⟩) =
        GaussianTranslation ⟨(3 : ℤ), (0 : ℤ)⟩ '' BoundaryFootprintVertices U) →
    let rightV : Set GaussianInt := {⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩}
    (GaussianTranslation ⟨3, 0⟩ ⟨-2, 0⟩ = ⟨1, 0⟩) → (GaussianTranslation ⟨3, 0⟩ ⟨-1, 0⟩ = ⟨2, 0⟩)
        → (GaussianTranslation ⟨3, 0⟩ ⟨-2, 1⟩ = ⟨1, 1⟩) → (GaussianTranslation ⟨3, 0⟩ ⟨-1, 1⟩ =
        ⟨2, 1⟩) → BoundaryFootprintVertices W = rightV := by
  classical
  intro U W unitV hUv hWt hWtV rightV gt20 gt10 gt21 gt11
  rw [hWt, hWtV, hUv]
  ext z
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [unitV, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx <;>
      subst x <;> decide +kernel
  · intro hz
    simp only [rightV, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz | hz | hz <;> subst z
    · refine ⟨⟨-2, 0⟩, ?_, gt20⟩
      change (⟨-2, 0⟩ : GaussianInt) = ⟨-2, 0⟩ ∨ _
      exact Or.inl rfl
    · refine ⟨⟨-1, 0⟩, ?_, gt10⟩
      change _ ∨ (⟨-1, 0⟩ : GaussianInt) = ⟨-1, 0⟩ ∨ _
      exact Or.inr (Or.inl rfl)
    · refine ⟨⟨-2, 1⟩, ?_, gt21⟩
      change _ ∨ _ ∨ (⟨-2, 1⟩ : GaussianInt) = ⟨-2, 1⟩ ∨ _
      exact Or.inr (Or.inr (Or.inl rfl))
    · refine ⟨⟨-1, 1⟩, ?_, gt11⟩
      change _ ∨ _ ∨ _ ∨ (⟨-1, 1⟩ : GaussianInt) = ⟨-1, 1⟩
      exact Or.inr (Or.inr (Or.inr rfl))

private theorem hDUe :
    let D := DiamondTile 1
    let U := P5124T1ParentModel 1 1 true
    let sqE : Set (Finset GaussianInt) := {e |
      e = {⟨-1, 0⟩, ⟨0, 0⟩} ∨ e = {⟨0, 0⟩, ⟨1, 0⟩} ∨
      e = {⟨-1, 2⟩, ⟨0, 2⟩} ∨ e = {⟨0, 2⟩, ⟨1, 2⟩} ∨
      e = {⟨-1, 0⟩, ⟨-1, 1⟩} ∨ e = {⟨1, 0⟩, ⟨1, 1⟩} ∨
      e = {⟨-1, 1⟩, ⟨-1, 2⟩} ∨ e = {⟨1, 1⟩, ⟨1, 2⟩}}
    (BoundaryFootprintEdges D = sqE) →
    let unitE : Set (Finset GaussianInt) := {e |
      e = {⟨-2, 0⟩, ⟨-1, 0⟩} ∨ e = {⟨-2, 0⟩, ⟨-2, 1⟩} ∨
      e = {⟨-1, 0⟩, ⟨-1, 1⟩} ∨ e = {⟨-2, 1⟩, ⟨-1, 1⟩}}
    (BoundaryFootprintEdges U = unitE) →
    let leftE : Set (Finset GaussianInt) := {e | e = {⟨-1, 0⟩, ⟨-1, 1⟩}}
    BoundaryFootprintEdges D ∩ BoundaryFootprintEdges U = leftE := by
  classical
  intro D U sqE hDe unitE hUe leftE
  rw [hDe, hUe]
  ext e
  change (e ∈ sqE ∧ e ∈ unitE) ↔ e ∈ leftE
  constructor
  · rintro ⟨hd, hu⟩
    change e = {⟨-2, 0⟩, ⟨-1, 0⟩} ∨ e = {⟨-2, 0⟩, ⟨-2, 1⟩} ∨
      e = {⟨-1, 0⟩, ⟨-1, 1⟩} ∨ e = {⟨-2, 1⟩, ⟨-1, 1⟩} at hu
    rcases hu with hu | hu | hu | hu
    all_goals
      first
      | rw [hu]
        decide +kernel
      | have hno : e ∉ sqE := by rw [hu]; decide +kernel
        exact False.elim (hno hd)
  · intro he
    subst e
    exact ⟨by decide +kernel, by decide +kernel⟩

private theorem hDWe :
    let D := DiamondTile 1
    let W := P5124T1ParentModel 1 0 false
    let sqE : Set (Finset GaussianInt) := {e |
      e = {⟨-1, 0⟩, ⟨0, 0⟩} ∨ e = {⟨0, 0⟩, ⟨1, 0⟩} ∨
      e = {⟨-1, 2⟩, ⟨0, 2⟩} ∨ e = {⟨0, 2⟩, ⟨1, 2⟩} ∨
      e = {⟨-1, 0⟩, ⟨-1, 1⟩} ∨ e = {⟨1, 0⟩, ⟨1, 1⟩} ∨
      e = {⟨-1, 1⟩, ⟨-1, 2⟩} ∨ e = {⟨1, 1⟩, ⟨1, 2⟩}}
    (BoundaryFootprintEdges D = sqE) →
    let rightE : Set (Finset GaussianInt) := {e |
      e = {⟨1, 0⟩, ⟨2, 0⟩} ∨ e = {⟨1, 0⟩, ⟨1, 1⟩} ∨
      e = {⟨2, 0⟩, ⟨2, 1⟩} ∨ e = {⟨1, 1⟩, ⟨2, 1⟩}}
    (BoundaryFootprintEdges W = rightE) →
    let rightTouchE : Set (Finset GaussianInt) := {e | e = {⟨1, 0⟩, ⟨1, 1⟩}}
    BoundaryFootprintEdges D ∩ BoundaryFootprintEdges W = rightTouchE := by
  classical
  intro D W sqE hDe rightE hWe rightTouchE
  rw [hDe, hWe]
  ext e
  change (e ∈ sqE ∧ e ∈ rightE) ↔ e ∈ rightTouchE
  constructor
  · rintro ⟨hd, hw⟩
    change e = {⟨1, 0⟩, ⟨2, 0⟩} ∨ e = {⟨1, 0⟩, ⟨1, 1⟩} ∨
      e = {⟨2, 0⟩, ⟨2, 1⟩} ∨ e = {⟨1, 1⟩, ⟨2, 1⟩} at hw
    rcases hw with hw | hw | hw | hw
    all_goals
      first
      | rw [hw]
        decide +kernel
      | have hno : e ∉ sqE := by rw [hw]; decide +kernel
        exact False.elim (hno hd)
  · intro he
    subst e
    exact ⟨by decide +kernel, by decide +kernel⟩

private theorem path2Decomp :
    ∀ {x : GaussianInt}, ∀ {y : GaussianInt}, ∀ {a : GaussianInt}, ∀ {b : GaussianInt}, ∀ {l₁ :
        List GaussianInt}, ∀ {l₂ : List GaussianInt}, ([x, y] = l₁ ++ a :: b :: l₂) → a = x ∧ b =
        y ∧ l₁ = [] ∧ l₂ = [] := by
  classical
  intro x y a b l₁ l₂ hp
  have hlen := congrArg List.length hp
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  have hl : l₁.length + l₂.length = 0 := by omega
  cases l₁ with
  | nil =>
    cases l₂ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hp
      rcases hp with ⟨hxa, hyb, _⟩
      subst a
      subst b
      exact ⟨rfl, rfl, rfl, rfl⟩
    | cons z zs =>
        simp only [List.length_cons] at hl
        have hpos : 0 < (z :: zs).length := by simp
        omega
  | cons z zs =>
      simp only [List.length_cons] at hl
      have hpos : 0 < (z :: zs).length := by simp
      omega

private theorem path3Decomp :
    ∀ {x : GaussianInt}, ∀ {y : GaussianInt}, ∀ {z : GaussianInt}, ∀ {a : GaussianInt}, ∀ {b :
        GaussianInt}, ∀ {l₁ : List GaussianInt}, ∀ {l₂ : List GaussianInt}, ([x, y, z] = l₁ ++ a
        :: b :: l₂) → (a = x ∧ b = y ∧ l₁ = [] ∧ l₂ = [z]) ∨
      (a = y ∧ b = z ∧ l₁ = [x] ∧ l₂ = []) := by
  classical
  intro x y z a b l₁ l₂ hp
  have hlen := congrArg List.length hp
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  have hl : l₁.length + l₂.length = 1 := by omega
  cases l₁ with
  | nil =>
    cases l₂ with
    | nil => omega
    | cons c cs =>
      have hcs : cs = [] := by
        cases cs with
        | nil => rfl
        | cons d ds =>
            simp only [List.length_cons] at hl
            have hpos : 0 < (d :: ds).length := by simp
            omega
      subst cs
      simp only [List.nil_append, List.cons.injEq] at hp
      rcases hp with ⟨hxa, hyb, hzc, _⟩
      subst a
      subst b
      subst c
      exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | cons c cs =>
    have hcs : cs = [] := by
      cases cs with
      | nil => rfl
      | cons d ds =>
          simp only [List.length_cons] at hl
          have hpos : 0 < (d :: ds).length := by simp
          omega
    subst cs
    cases l₂ with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hp
      rcases hp with ⟨hxa, hyb, hzc, _⟩
      subst a
      subst b
      subst c
      exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
    | cons d ds =>
        simp only [List.length_cons] at hl
        have hpos : 0 < (d :: ds).length := by simp
        omega

private theorem simplePath2 :
    (∀ {x : GaussianInt}, ∀ {y : GaussianInt}, ∀ {a : GaussianInt}, ∀ {b : GaussianInt}, ∀ {l₁ :
        List GaussianInt}, ∀ {l₂ : List GaussianInt}, ([x, y] = l₁ ++ a :: b :: l₂) → a = x ∧ b =
        y ∧ l₁ = [] ∧ l₂ = []) → ∀ (x : GaussianInt), ∀ (y : GaussianInt), ([x, y].Nodup) → (y =
        x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) → SimpleGridPath ({x, y} : Set
        GaussianInt) {e : Finset GaussianInt | e = {x, y}} := by
  classical
  intro path2Decomp x y hnodup hstep
  refine ⟨[x, y], hnodup, by simp, by simp, ?_, ?_⟩
  · intro a b l₁ l₂ hp
    obtain ⟨rfl, rfl, rfl, rfl⟩ := path2Decomp hp
    exact hstep
  · intro e
    constructor
    · intro he
      change e = {x, y} at he
      subst e
      exact ⟨x, y, [], [], by simp, rfl⟩
    · rintro ⟨a, b, l₁, l₂, hp, he⟩
      obtain ⟨rfl, rfl, rfl, rfl⟩ := path2Decomp hp
      simpa using he

private theorem simplePath3 :
    (∀ {x : GaussianInt}, ∀ {y : GaussianInt}, ∀ {z : GaussianInt}, ∀ {a : GaussianInt}, ∀ {b :
        GaussianInt}, ∀ {l₁ : List GaussianInt}, ∀ {l₂ : List GaussianInt}, ([x, y, z] = l₁ ++ a
        :: b :: l₂) → (a = x ∧ b = y ∧ l₁ = [] ∧ l₂ = [z]) ∨ (a = y ∧ b = z ∧ l₁ = [x] ∧ l₂ =
        [])) → ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (z : GaussianInt), ([x, y, z].Nodup) →
        (y = x + 1) → (z = y + 1) → SimpleGridPath ({x, y, z} : Set GaussianInt)
        {e : Finset GaussianInt | e = {x, y} ∨ e = {y, z}} := by
  classical
  intro path3Decomp x y z hnodup hxy hyz
  refine ⟨[x, y, z], hnodup, by simp, by simp, ?_, ?_⟩
  · intro a b l₁ l₂ hp
    rcases path3Decomp hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact Or.inl hxy
    · exact Or.inl hyz
  · intro e
    constructor
    · intro he
      change e = {x, y} ∨ e = {y, z} at he
      rcases he with he | he
      · subst e; exact ⟨x, y, [], [z], by simp, rfl⟩
      · subst e; exact ⟨y, z, [x], [], by simp, rfl⟩
    · rintro ⟨a, b, l₁, l₂, hp, he⟩
      rcases path3Decomp hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inl he
      · exact Or.inr he

end EmptyParentGeometry

namespace EmptyParentContacts

private theorem lower_contact :
    let D := DiamondTile 1
    let B := TileTranslation D ⟨0, -2⟩
    let C := P5124T1ParentModel 1 2 true
    (C.cells = ∅) → (C.anchor = ⟨1, 0⟩) → (¬ C.cells.Nonempty) → (BoundaryFootprintVertices
        (DiamondTile (1 : ℕ)) = {⟨(-1 : ℤ), (0 : ℤ)⟩, ⟨(0 : ℤ), (0 :
        ℤ)⟩, ⟨(1 : ℤ), (0 : ℤ)⟩, ⟨(-1 : ℤ), (1 : ℤ)⟩, ⟨(1 :
        ℤ), (1 : ℤ)⟩, ⟨(-1 : ℤ), (2 : ℤ)⟩, ⟨(0 : ℤ), (2 : ℤ)⟩,
        ⟨(1 : ℤ), (2 : ℤ)⟩}) → (BoundaryFootprintVertices (TileTranslation
        (DiamondTile (1 : ℕ)) ⟨(0 : ℤ), (-2 : ℤ)⟩) = {⟨(-1 : ℤ), (-2 :
        ℤ)⟩, ⟨(0 : ℤ), (-2 : ℤ)⟩, ⟨(1 : ℤ), (-2 : ℤ)⟩, ⟨(-1 :
        ℤ), (-1 : ℤ)⟩, ⟨(1 : ℤ), (-1 : ℤ)⟩, ⟨(-1 : ℤ), (0 : ℤ)⟩, ⟨(0 : ℤ), (0 : ℤ)⟩, ⟨(1 : ℤ), (0
            : ℤ)⟩}) →
        (D.cells.Nonempty) → (B.cells.Nonempty) → (Disjoint D.cells B.cells) → (SimpleGridPath
        (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices B) (BoundaryFootprintEdges D ∩
        BoundaryFootprintEdges B)) → TouchingTriple D B C := by
  classical
  intro D B C hCc hCa hCne hDv hBv hDn hBn hDBdis pDB
  let sqV : Set GaussianInt := {⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩,
    ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩}
  let lowV : Set GaussianInt := {⟨-1, -2⟩, ⟨0, -2⟩, ⟨1, -2⟩,
    ⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩}
  unfold TouchingTriple
  refine ⟨Or.inl ⟨hDn, hBn, hDBdis, pDB⟩,
    Or.inr (Or.inr ⟨hCc, ?_⟩), Or.inr (Or.inl ⟨hCc, ?_⟩), ?_⟩
  · rw [hCa, hBv]
    change (⟨1, 0⟩ : GaussianInt) ∈ lowV
    decide +kernel
  · rw [hCa, hDv]
    change (⟨1, 0⟩ : GaussianInt) ∈ sqV
    decide +kernel
  · refine ⟨(⟨1, 0⟩ : GaussianInt), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hDv]
        change (⟨1, 0⟩ : GaussianInt) ∈ sqV
        decide +kernel
      · rw [hBv]
        change (⟨1, 0⟩ : GaussianInt) ∈ lowV
        decide +kernel
      · change (⟨1, 0⟩ : GaussianInt) ∈ BoundaryFootprintVertices C
        unfold BoundaryFootprintVertices
        rw [ite_eq_right hCne, hCa]
        simp
    · intro x hx
      have hxC := hx.2.2
      unfold BoundaryFootprintVertices at hxC
      rw [ite_eq_right hCne, hCa] at hxC
      simpa using hxC

private theorem left_contact :
    let D := DiamondTile 1
    let U := P5124T1ParentModel 1 1 true
    let V := P5124T1ParentModel 1 2 false
    (V.cells = ∅) → (V.anchor = ⟨-1, 0⟩) → (¬ V.cells.Nonempty) → (BoundaryFootprintVertices
        (DiamondTile (1 : ℕ)) = {⟨(-1 : ℤ), (0 : ℤ)⟩, ⟨(0 : ℤ), (0 :
        ℤ)⟩, ⟨(1 : ℤ), (0 : ℤ)⟩, ⟨(-1 : ℤ), (1 : ℤ)⟩, ⟨(1 :
        ℤ), (1 : ℤ)⟩, ⟨(-1 : ℤ), (2 : ℤ)⟩, ⟨(0 : ℤ), (2 : ℤ)⟩,
        ⟨(1 : ℤ), (2 : ℤ)⟩}) → (U.cells.Nonempty) → (BoundaryFootprintVertices
        (P5124T1ParentModel (1 : ℕ) (1 : Fin (3 : ℕ)) true) = {⟨(-2 : ℤ), (0 : ℤ)⟩, ⟨(-1 : ℤ),
            (0 : ℤ)⟩, ⟨(-2 : ℤ), (1 : ℤ)⟩, ⟨(-1 :
        ℤ), (1 : ℤ)⟩}) → (D.cells.Nonempty) → (Disjoint D.cells U.cells) → (SimpleGridPath
        (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices U) (BoundaryFootprintEdges D ∩
        BoundaryFootprintEdges U)) → TouchingTriple D U V := by
  classical
  intro D U V hVc hVa hVne hDv hUne hUv hDn hDUdis pDU
  let sqV : Set GaussianInt := {⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩,
    ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩}
  let unitV : Set GaussianInt := {⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, 1⟩, ⟨-1, 1⟩}
  unfold TouchingTriple
  refine ⟨Or.inl ⟨hDn, hUne, hDUdis, pDU⟩,
    Or.inr (Or.inr ⟨hVc, ?_⟩), Or.inr (Or.inl ⟨hVc, ?_⟩), ?_⟩
  · rw [hVa, hUv]
    change (⟨-1, 0⟩ : GaussianInt) ∈ unitV
    decide +kernel
  · rw [hVa, hDv]
    change (⟨-1, 0⟩ : GaussianInt) ∈ sqV
    decide +kernel
  · refine ⟨(⟨-1, 0⟩ : GaussianInt), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hDv]
        change (⟨-1, 0⟩ : GaussianInt) ∈ sqV
        decide +kernel
      · rw [hUv]
        change (⟨-1, 0⟩ : GaussianInt) ∈ unitV
        decide +kernel
      · change (⟨-1, 0⟩ : GaussianInt) ∈ BoundaryFootprintVertices V
        unfold BoundaryFootprintVertices
        rw [ite_eq_right hVne, hVa]
        simp
    · intro x hx
      have hxV := hx.2.2
      unfold BoundaryFootprintVertices at hxV
      rw [ite_eq_right hVne, hVa] at hxV
      simpa using hxV

private theorem right_contact :
    let D := DiamondTile 1
    let C := P5124T1ParentModel 1 2 true
    let W := P5124T1ParentModel 1 0 false
    (D.cells = {⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩}) → (C.cells = ∅) → (C.anchor = ⟨1, 0⟩) → (¬
        C.cells.Nonempty) → (W.cells = {⟨1, 0⟩}) → (BoundaryFootprintVertices (DiamondTile (1 :
        ℕ)) = {⟨(-1 : ℤ), (0 : ℤ)⟩, ⟨(0 : ℤ), (0 : ℤ)⟩, ⟨(1 :
        ℤ), (0 : ℤ)⟩, ⟨(-1 : ℤ), (1 : ℤ)⟩, ⟨(1 : ℤ), (1 : ℤ)⟩,
        ⟨(-1 : ℤ), (2 : ℤ)⟩, ⟨(0 : ℤ), (2 : ℤ)⟩, ⟨(1 : ℤ), (2 : ℤ)⟩}) →
            (BoundaryFootprintVertices (P5124T1ParentModel (1 : ℕ) (0 : Fin (3 :
        ℕ)) false) = {⟨(1 : ℤ), (0 : ℤ)⟩, ⟨(2 : ℤ), (0 : ℤ)⟩, ⟨(1 : ℤ), (1 : ℤ)⟩, ⟨(2 : ℤ), (1 :
            ℤ)⟩}) → (D.cells.Nonempty) →
        (W.cells.Nonempty) → (SimpleGridPath (BoundaryFootprintVertices D ∩
        BoundaryFootprintVertices W) (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges W)) →
        TouchingTriple D C W := by
  classical
  intro D C W hDc hCc hCa hCne hWc hDv hWv hDn hWn pDW
  let sqV : Set GaussianInt := {⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩,
    ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩}
  let rightV : Set GaussianInt := {⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩}
  unfold TouchingTriple
  refine ⟨Or.inr (Or.inr ⟨hCc, ?_⟩),
    Or.inr (Or.inl ⟨hCc, ?_⟩),
    Or.inl ⟨hWn, hDn, ?_, by simpa [Set.inter_comm] using pDW⟩, ?_⟩
  · rw [hCa, hDv]
    change (⟨1, 0⟩ : GaussianInt) ∈ sqV
    decide +kernel
  · rw [hCa, hWv]
    change (⟨1, 0⟩ : GaussianInt) ∈ rightV
    decide +kernel
  · rw [hDc, hWc]; decide +kernel
  · refine ⟨(⟨1, 0⟩ : GaussianInt), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hDv]
        change (⟨1, 0⟩ : GaussianInt) ∈ sqV
        decide +kernel
      · change (⟨1, 0⟩ : GaussianInt) ∈ BoundaryFootprintVertices C
        unfold BoundaryFootprintVertices
        rw [ite_eq_right hCne, hCa]
        simp
      · rw [hWv]
        change (⟨1, 0⟩ : GaussianInt) ∈ rightV
        decide +kernel
    · intro x hx
      have hxC := hx.2.1
      unfold BoundaryFootprintVertices at hxC
      rw [ite_eq_right hCne, hCa] at hxC
      simpa using hxC

end EmptyParentContacts

theorem P5124T1EmptyParents :
    TouchingTriple (DiamondTile 1)
      (TileTranslation (DiamondTile 1) ⟨0, -2⟩)
      (P5124T1ParentModel 1 2 true) ∧
    TouchingTriple (DiamondTile 1) (P5124T1ParentModel 1 1 true)
      (P5124T1ParentModel 1 2 false) ∧
    TouchingTriple (DiamondTile 1) (P5124T1ParentModel 1 2 true)
      (P5124T1ParentModel 1 0 false) := by
-- BODY
  have finalProof :
      TouchingTriple (DiamondTile 1)
        (TileTranslation (DiamondTile 1) ⟨0, -2⟩)
        (P5124T1ParentModel 1 2 true) ∧
      TouchingTriple (DiamondTile 1) (P5124T1ParentModel 1 1 true)
        (P5124T1ParentModel 1 2 false) ∧
      TouchingTriple (DiamondTile 1) (P5124T1ParentModel 1 2 true)
        (P5124T1ParentModel 1 0 false) := by
    classical
    let D := DiamondTile 1
    let B := TileTranslation D ⟨0, -2⟩
    let C := P5124T1ParentModel 1 2 true
    let U := P5124T1ParentModel 1 1 true
    let V := P5124T1ParentModel 1 2 false
    let W := P5124T1ParentModel 1 0 false
    have hDc : D.cells = {⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩} := by
      dsimp [D, DiamondTile, DiamondCellDomain]
      decide +kernel
    have hBc : B.cells = {⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩} := by
      dsimp [B, D, TileTranslation, DiamondTile, DiamondCellDomain, GaussianTranslation]
      decide +kernel
    have hCc : C.cells = ∅ := by dsimp [C, P5124T1ParentModel]; decide +kernel
    have hCa : C.anchor = ⟨1, 0⟩ := by dsimp [C, P5124T1ParentModel]; decide +kernel
    have hCne : ¬ C.cells.Nonempty := by rw [hCc]; simp
    have hUc : U.cells = {⟨-2, 0⟩} := by dsimp [U, P5124T1ParentModel]
    have hVc : V.cells = ∅ := by dsimp [V, P5124T1ParentModel]; decide +kernel
    have hVa : V.anchor = ⟨-1, 0⟩ := by dsimp [V, P5124T1ParentModel]; decide +kernel
    have hVne : ¬ V.cells.Nonempty := by rw [hVc]; simp
    have hWc : W.cells = {⟨1, 0⟩} := by dsimp [W, P5124T1ParentModel]
    let sqE : Set (Finset GaussianInt) := {e |
      e = {⟨-1, 0⟩, ⟨0, 0⟩} ∨ e = {⟨0, 0⟩, ⟨1, 0⟩} ∨
      e = {⟨-1, 2⟩, ⟨0, 2⟩} ∨ e = {⟨0, 2⟩, ⟨1, 2⟩} ∨
      e = {⟨-1, 0⟩, ⟨-1, 1⟩} ∨ e = {⟨1, 0⟩, ⟨1, 1⟩} ∨
      e = {⟨-1, 1⟩, ⟨-1, 2⟩} ∨ e = {⟨1, 1⟩, ⟨1, 2⟩}}
    let sqV : Set GaussianInt := {⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩,
      ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩}
    let r : Int → Int := fun b => min (b + 1) (2 * (1 : Int) - b)
    let H : Int → Int → Prop := fun a b =>
      ((b = 0 ∨ b = 2 * (1 : Int)) ∧ -1 ≤ a ∧ a < 1) ∨
      (1 ≤ b ∧ b < 1 ∧ (a = -b - 1 ∨ a = b)) ∨
      ((1 : Int) < b ∧ b < 2 * (1 : Int) ∧
        (a = b - 2 * (1 : Int) - 1 ∨ a = 2 * (1 : Int) - b))
    let E : Set (Finset GaussianInt) := {e | ∃ a b : Int,
      (H a b ∧ e = {⟨a, b⟩, ⟨a + 1, b⟩}) ∨
      (0 ≤ b ∧ b < 2 * (1 : Int) ∧ (a = -r b ∨ a = r b) ∧
        e = {⟨a, b⟩, ⟨a, b + 1⟩})}
    have hgeom := P5124T1BoundaryGeometry 1 (by decide)
    change BoundaryFootprintEdges D = E ∧
      BoundaryFootprintVertices D = {z | ∃ e ∈ E, z ∈ e} at hgeom
    have hDe := EmptyParentGeometry.hDe hgeom
    have hDv := EmptyParentGeometry.hDv hgeom hDe
    let lowE : Set (Finset GaussianInt) := {e |
      e = {⟨-1, -2⟩, ⟨0, -2⟩} ∨ e = {⟨0, -2⟩, ⟨1, -2⟩} ∨
      e = {⟨-1, 0⟩, ⟨0, 0⟩} ∨ e = {⟨0, 0⟩, ⟨1, 0⟩} ∨
      e = {⟨-1, -2⟩, ⟨-1, -1⟩} ∨ e = {⟨1, -2⟩, ⟨1, -1⟩} ∨
      e = {⟨-1, -1⟩, ⟨-1, 0⟩} ∨ e = {⟨1, -1⟩, ⟨1, 0⟩}}
    let lowV : Set GaussianInt := {⟨-1, -2⟩, ⟨0, -2⟩, ⟨1, -2⟩,
      ⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩}
    obtain ⟨_, _, _, _, _, _, _, hBV, hBE⟩ := TileTranslationFormulas D ⟨0, -2⟩
    have hBe : BoundaryFootprintEdges B = lowE := by
      change BoundaryFootprintEdges (TileTranslation D ⟨0, -2⟩) = lowE
      rw [hBE, hDe]
      ext e
      simp [lowE, GaussianTranslation, Finset.image_insert, eq_comm]
    have hBv := EmptyParentGeometry.hBv hDv hBV
    let capV : Set GaussianInt := {⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩}
    have hDBv : BoundaryFootprintVertices D ∩ BoundaryFootprintVertices B = capV := by
      rw [hDv, hBv]
      ext z
      simp only [Set.mem_inter_iff, capV, Set.mem_insert_iff,
        Set.mem_singleton_iff, Zsqrtd.ext_iff]
      omega
    let capE : Set (Finset GaussianInt) := {e |
      e = {⟨-1, 0⟩, ⟨0, 0⟩} ∨ e = {⟨0, 0⟩, ⟨1, 0⟩}}
    have pairEq {α : Type} [DecidableEq α] (a b c d : α) := EmptyParentGeometry.pairEq (α := α) a
        b c d
    have hDBe := EmptyParentGeometry.hDBe hDe hBe pairEq
    let unitE : Set (Finset GaussianInt) := {e |
      e = {⟨-2, 0⟩, ⟨-1, 0⟩} ∨ e = {⟨-2, 0⟩, ⟨-2, 1⟩} ∨
      e = {⟨-1, 0⟩, ⟨-1, 1⟩} ∨ e = {⟨-2, 1⟩, ⟨-1, 1⟩}}
    let unitV : Set GaussianInt := {⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, 1⟩, ⟨-1, 1⟩}
    have hUe := EmptyParentGeometry.hUe hUc
    have hUne : U.cells.Nonempty := by rw [hUc]; simp
    have hUv := EmptyParentGeometry.hUv hUe hUne
    have hWt : W = TileTranslation U ⟨3, 0⟩ := by
      simp only [W, U, P5124T1ParentModel, TileTranslation]
      constructor
    obtain ⟨_, _, _, _, _, _, _, hWtV, hWtE⟩ := TileTranslationFormulas U ⟨3, 0⟩
    let rightE : Set (Finset GaussianInt) := {e |
      e = {⟨1, 0⟩, ⟨2, 0⟩} ∨ e = {⟨1, 0⟩, ⟨1, 1⟩} ∨
      e = {⟨2, 0⟩, ⟨2, 1⟩} ∨ e = {⟨1, 1⟩, ⟨2, 1⟩}}
    let rightV : Set GaussianInt := {⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩}
    have gt20 : GaussianTranslation ⟨3, 0⟩ ⟨-2, 0⟩ = ⟨1, 0⟩ := by decide +kernel
    have gt10 : GaussianTranslation ⟨3, 0⟩ ⟨-1, 0⟩ = ⟨2, 0⟩ := by decide +kernel
    have gt21 : GaussianTranslation ⟨3, 0⟩ ⟨-2, 1⟩ = ⟨1, 1⟩ := by decide +kernel
    have gt11 : GaussianTranslation ⟨3, 0⟩ ⟨-1, 1⟩ = ⟨2, 1⟩ := by decide +kernel
    have imagePair (a b c d : GaussianInt)
        (ha : GaussianTranslation ⟨3, 0⟩ a = c)
        (hb : GaussianTranslation ⟨3, 0⟩ b = d) :
        ({a, b} : Finset GaussianInt).image
          (GaussianTranslation ⟨3, 0⟩) = {c, d} := by
      rw [Finset.image_insert, Finset.image_singleton, ha, hb]
    have hWe := EmptyParentGeometry.hWe hUe hWt hWtE gt20
        gt10 gt21 gt11 imagePair
    have hWv := EmptyParentGeometry.hWv hUv hWt hWtV gt20
        gt10 gt21 gt11
    let leftE : Set (Finset GaussianInt) := {e | e = {⟨-1, 0⟩, ⟨-1, 1⟩}}
    let leftV : Set GaussianInt := {⟨-1, 0⟩, ⟨-1, 1⟩}
    have hDUe := EmptyParentGeometry.hDUe hDe hUe
    have hDUv : BoundaryFootprintVertices D ∩ BoundaryFootprintVertices U = leftV := by
      rw [hDv, hUv]
      ext z
      simp only [Set.mem_inter_iff, leftV, Set.mem_insert_iff,
        Set.mem_singleton_iff, Zsqrtd.ext_iff]
      omega
    let rightTouchE : Set (Finset GaussianInt) := {e | e = {⟨1, 0⟩, ⟨1, 1⟩}}
    let rightTouchV : Set GaussianInt := {⟨1, 0⟩, ⟨1, 1⟩}
    have hDWe := EmptyParentGeometry.hDWe hDe hWe
    have hDWv : BoundaryFootprintVertices D ∩ BoundaryFootprintVertices W = rightTouchV := by
      rw [hDv, hWv]
      ext z
      simp only [Set.mem_inter_iff, rightTouchV, Set.mem_insert_iff,
        Set.mem_singleton_iff, Zsqrtd.ext_iff]
      omega
    have path2Decomp {x y a b : GaussianInt} {l₁ l₂ : List GaussianInt}
      (hp : [x, y] = l₁ ++ a :: b :: l₂) := EmptyParentGeometry.path2Decomp (x := x) (y := y) (a
          := a) (b := b) (l₁ := l₁) (l₂ := l₂) hp
    have path3Decomp {x y z a b : GaussianInt} {l₁ l₂ : List GaussianInt}
      (hp : [x, y, z] = l₁ ++ a :: b :: l₂) := EmptyParentGeometry.path3Decomp (x := x) (y := y)
          (z := z) (a := a) (b := b) (l₁ := l₁) (l₂ := l₂) hp
    have simplePath2 (x y : GaussianInt) (hnodup : [x, y].Nodup)
      (hstep : y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) :=
          EmptyParentGeometry.simplePath2 path2Decomp x y hnodup hstep
    have simplePath3 (x y z : GaussianInt) (hnodup : [x, y, z].Nodup)
      (hxy : y = x + 1) (hyz : z = y + 1) := EmptyParentGeometry.simplePath3
            path3Decomp x y z hnodup hxy hyz
    have hDn : D.cells.Nonempty := by rw [hDc]; simp
    have hBn : B.cells.Nonempty := by rw [hBc]; simp
    have hWn : W.cells.Nonempty := by rw [hWc]; simp
    have hDBdis : Disjoint D.cells B.cells := by rw [hDc, hBc]; decide +kernel
    have hDUdis : Disjoint D.cells U.cells := by rw [hDc, hUc]; decide +kernel
    have hDWdis : Disjoint D.cells W.cells := by rw [hDc, hWc]; decide +kernel
    have pDB : SimpleGridPath
        (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices B)
        (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges B) := by
      rw [hDBv, hDBe]
      change SimpleGridPath capV capE
      apply simplePath3 ⟨-1, 0⟩ ⟨0, 0⟩ ⟨1, 0⟩
      · decide +kernel
      · ext <;> simp
      · ext <;> simp
    have pDU : SimpleGridPath
        (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices U)
        (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges U) := by
      rw [hDUv, hDUe]
      change SimpleGridPath leftV leftE
      apply simplePath2 ⟨-1, 0⟩ ⟨-1, 1⟩
      · decide +kernel
      · right; right; left; ext <;> simp
    have pDW : SimpleGridPath
        (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices W)
        (BoundaryFootprintEdges D ∩ BoundaryFootprintEdges W) := by
      rw [hDWv, hDWe]
      change SimpleGridPath rightTouchV rightTouchE
      apply simplePath2 ⟨1, 0⟩ ⟨1, 1⟩
      · decide +kernel
      · right; right; left; ext <;> simp
    have lower_contact : TouchingTriple D B C := EmptyParentContacts.lower_contact hCc hCa hCne
        hDv hBv hDn hBn hDBdis pDB
    have left_contact : TouchingTriple D U V := EmptyParentContacts.left_contact hVc hVa hVne hDv
        hUne hUv hDn hDUdis pDU
    have right_contact : TouchingTriple D C W := EmptyParentContacts.right_contact hDc hCc hCa
        hCne hWc hDv hWv hDn hWn pDW
    exact ⟨lower_contact, left_contact, right_contact⟩
  exact finalProof

end ApollonianSuperharmonic

end
