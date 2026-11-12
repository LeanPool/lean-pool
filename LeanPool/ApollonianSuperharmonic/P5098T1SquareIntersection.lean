/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4062T1CanonicalSupport
public import LeanPool.ApollonianSuperharmonic.P4456T2SquareEdges

-- [TABLET NODE: P5098T1SquareIntersection]

/-!
# P5098T1SquareIntersection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5098T1SquareIntersection (p q : Nat) (hp : 0 < p) (hq : 0 < q)
    (a b : GaussianInt) :
    let A := TileTranslation (FordTile p) a
    let B := TileTranslation (FordTile q) b
    ((FootprintEdges A ∩ FootprintEdges B).Nonempty ↔
      ((-(q : Int) < (b - a).re ∧ (b - a).re < p) ∧
        (-(q : Int) ≤ (b - a).im ∧ (b - a).im ≤ p)) ∨
      ((-(q : Int) ≤ (b - a).re ∧ (b - a).re ≤ p) ∧
        (-(q : Int) < (b - a).im ∧ (b - a).im < p))) ∧
    (¬ (FootprintEdges A ∩ FootprintEdges B).Nonempty →
      (FootprintVertices A ∩ FootprintVertices B).Subsingleton) := by
-- BODY
  classical
  dsimp only
  have box (n : Nat) (hn : 0 < n) (c z : GaussianInt) :
      z ∈ FootprintVertices (TileTranslation (FordTile n) c) ↔
        c.re ≤ z.re ∧ z.re ≤ c.re + n ∧
        c.im ≤ z.im ∧ z.im ≤ c.im + n := by
    rw [(TileTranslationFormulas _ _).2.2.2.2.2.1,
      (P4062T1CanonicalSupport n hn).1]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [FordVertexDomain, Set.mem_ofPred_eq] at hw
      simp only [GaussianTranslation, Zsqrtd.re_add, Zsqrtd.im_add]
      omega
    · intro hz
      refine ⟨z - c, ?_, by simp [GaussianTranslation]⟩
      simp only [FordVertexDomain, Set.mem_ofPred_eq, Zsqrtd.re_sub, Zsqrtd.im_sub]
      omega
  have ends (T : ProtoTile) (e : Finset GaussianInt) (he : e ∈ FootprintEdges T) :
      (∀ z ∈ e, z ∈ FootprintVertices T) ∧
        ∃ x y, x ∈ e ∧ y ∈ e ∧ (y = x + 1 ∨ y = x + ⟨0, 1⟩) := by
    rcases he with ⟨c, hc, rfl | rfl | rfl | rfl⟩
    all_goals
      have hn : T.cells.Nonempty := ⟨c, hc⟩
      constructor
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        simp only [FootprintVertices, ite_eq_left hn, Set.mem_ofPred_eq]
        rcases hz with hz | hz
        all_goals exact ⟨c, hc, by rw [hz]; simp⟩
    · exact ⟨c, c + 1, by simp, by simp, Or.inl rfl⟩
    · exact ⟨c, c + ⟨0, 1⟩, by simp, by simp, Or.inr rfl⟩
    · exact ⟨c + 1, c + 1 + ⟨0, 1⟩, by simp, by simp, Or.inr rfl⟩
    · refine ⟨c + ⟨0, 1⟩, c + 1 + ⟨0, 1⟩, by simp, by simp, Or.inl ?_⟩
      abel
  have supported (x y : GaussianInt)
      (hx : x ∈ FootprintVertices (TileTranslation (FordTile p) a) ∩
        FootprintVertices (TileTranslation (FordTile q) b))
      (hy : y ∈ FootprintVertices (TileTranslation (FordTile p) a) ∩
        FootprintVertices (TileTranslation (FordTile q) b))
      (hxy : FourNeighborAdjacent x y) :
      (FootprintEdges (TileTranslation (FordTile p) a) ∩
        FootprintEdges (TileTranslation (FordTile q) b)).Nonempty := by
    exact ⟨{x, y}, (P4456T2SquareEdges p hp a _ rfl).2 x hx.1 y hy.1 hxy,
      (P4456T2SquareEdges q hq b _ rfl).2 x hx.2 y hy.2 hxy⟩
  have segment (x y : GaussianInt)
      (hx : x ∈ FootprintVertices (TileTranslation (FordTile p) a) ∩
        FootprintVertices (TileTranslation (FordTile q) b))
      (hy : y ∈ FootprintVertices (TileTranslation (FordTile p) a) ∩
        FootprintVertices (TileTranslation (FordTile q) b)) (hne : x ≠ y) :
      (FootprintEdges (TileTranslation (FordTile p) a) ∩
        FootprintEdges (TileTranslation (FordTile q) b)).Nonempty := by
    have hxA := (box p hp a x).mp hx.1
    have hxB := (box q hq b x).mp hx.2
    have hyA := (box p hp a y).mp hy.1
    have hyB := (box q hq b y).mp hy.2
    have in_box (z : GaussianInt)
        (hz : min x.re y.re ≤ z.re ∧ z.re ≤ max x.re y.re ∧
          min x.im y.im ≤ z.im ∧ z.im ≤ max x.im y.im) :
        z ∈ FootprintVertices (TileTranslation (FordTile p) a) ∩
          FootprintVertices (TileTranslation (FordTile q) b) := by
      constructor
      · apply (box p hp a z).mpr
        constructor <;> try constructor
        all_goals omega
      · apply (box q hq b z).mpr
        constructor <;> try constructor
        all_goals omega
    by_cases hr : x.re = y.re
    · have hi : x.im ≠ y.im := by
        intro hi
        exact hne (Zsqrtd.ext hr hi)
      let z : GaussianInt := ⟨x.re, min x.im y.im⟩
      apply supported z (z + ⟨0, 1⟩)
      · apply in_box
        dsimp [z]
        omega
      · apply in_box
        simp only [Zsqrtd.re_add, Zsqrtd.im_add]
        dsimp [z]
        omega
      · exact Or.inr (Or.inr (Or.inl rfl))
    · let z : GaussianInt := ⟨min x.re y.re, x.im⟩
      apply supported z (z + 1)
      · apply in_box
        dsimp [z]
        omega
      · apply in_box
        simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one]
        dsimp [z]
        omega
      · exact Or.inl rfl
  constructor
  · constructor
    · rintro ⟨e, heA, heB⟩
      obtain ⟨allA, x, y, hx, hy, hstep⟩ := ends _ e heA
      have allB := (ends _ e heB).1
      have hxA := (box p hp a x).mp (allA x hx)
      have hxB := (box q hq b x).mp (allB x hx)
      have hyA := (box p hp a y).mp (allA y hy)
      have hyB := (box q hq b y).mp (allB y hy)
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
      rcases hstep with rfl | rfl
      · left
        simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one] at hyA hyB
        omega
      · right
        simp only [Zsqrtd.re_add, Zsqrtd.im_add] at hyA hyB
        norm_num at hyA hyB
        omega
    · intro h
      let z : GaussianInt := ⟨max a.re b.re, max a.im b.im⟩
      have hz : z ∈ FootprintVertices (TileTranslation (FordTile p) a) ∩
          FootprintVertices (TileTranslation (FordTile q) b) := by
        constructor <;> apply (box _ (by assumption) _ _).mpr
        all_goals dsimp [z]; simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at h; omega
      rcases h with h | h
      · apply supported z (z + 1) hz
        · constructor <;> apply (box _ (by assumption) _ _).mpr
          all_goals simp [z] at *; omega
        · exact Or.inl rfl
      · apply supported z (z + ⟨0, 1⟩) hz
        · constructor <;> apply (box _ (by assumption) _ _).mpr
          all_goals simp [z] at *; omega
        · exact Or.inr (Or.inr (Or.inl rfl))
  · intro he x hx y hy
    by_contra hn
    exact he (segment x y hx hy hn)

end ApollonianSuperharmonic

end
