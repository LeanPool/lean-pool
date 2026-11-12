/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AcyclicIndegreeOrientation

-- [TABLET NODE: P4062T1OrientationTransport]

/-!
# P4062T1OrientationTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4062T1OrientationTransport
    (D E : Finset GaussianInt) (σ τ : GaussianInt → Int)
    (u : GaussianInt) (hE : E = D.image (fun x => x + u))
    (hσ : ∀ x ∈ E, τ x = σ (x - u))
    (o : AcyclicIndegreeOrientation D σ) :
    ∃ t : AcyclicIndegreeOrientation E τ,
      (∀ x y, t.edge x y ↔ o.edge (x-u) (y-u)) ∧
      ∀ x, t.rank x = o.rank (x-u) := by
-- BODY
  classical
  have hm (x : GaussianInt) : x ∈ E ↔ x-u ∈ D := by
    rw [hE]
    constructor
    · rintro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      simpa using hy
    · intro hx
      exact Finset.mem_image.mpr ⟨x-u, hx, by simp⟩
  have ha (x y : GaussianInt) :
      FourNeighborAdjacent (x-u) (y-u) ↔ FourNeighborAdjacent x y := by
    have cancel (a b v : GaussianInt) (h : a-u = b-u+v) : a=b+v := by
      have he := congrArg (fun z => z+u) h
      convert he using 1 <;> abel
    unfold FourNeighborAdjacent
    constructor <;> intro h
    · rcases h with h | h | h | h
      · left; exact cancel y x 1 h
      · right; left
        have he := cancel y x (-1) (by simpa only [sub_eq_add_neg] using h)
        simpa only [sub_eq_add_neg] using he
      · right; right; left; exact cancel y x ⟨0, 1⟩ h
      · right; right; right
        have he := cancel y x (-⟨0, 1⟩) (by simpa only [sub_eq_add_neg] using h)
        simpa only [sub_eq_add_neg] using he
    · rcases h with h | h | h | h
      · left; rw [h]; abel
      · right; left; rw [h]; abel
      · right; right; left; rw [h]; abel
      · right; right; right; rw [h]; abel
  let t : AcyclicIndegreeOrientation E τ := {
    edge := fun x y => o.edge (x-u) (y-u)
    edge_decidable := fun x y => o.edge_decidable (x-u) (y-u)
    rank := fun x => o.rank (x-u)
    supported := by
      intro x y he
      obtain ⟨hx, hy, hxy⟩ := o.supported _ _ he
      exact ⟨(hm x).mpr hx, (hm y).mpr hy, (ha x y).mp hxy⟩
    oriented := by
      intro x hx y hy hxy
      exact o.oriented _ ((hm x).mp hx) _ ((hm y).mp hy) ((ha x y).mpr hxy)
    increasing := by intro x y he; exact o.increasing _ _ he
    indegree := by
      intro x hx
      have hc : (E.filter (fun y => @decide (o.edge (y-u) (x-u))
          (o.edge_decidable (y-u) (x-u)))).card =
          (D.filter (fun y => @decide (o.edge y (x-u))
            (o.edge_decidable y (x-u)))).card := by
        apply Finset.card_bij (fun y _ => y-u)
        · intro y hy
          simp only [Finset.mem_filter, decide_eq_true_eq] at hy ⊢
          exact ⟨(hm y).mp hy.1, hy.2⟩
        · intro y hy z hz he
          have he' := congrArg (fun w => w+u) he
          simpa using he'
        · intro z hz
          simp only [Finset.mem_filter, decide_eq_true_eq] at hz
          refine ⟨z+u, Finset.mem_filter.mpr ⟨(hm _).mpr (by simpa using hz.1),
            by simpa using hz.2⟩, by simp⟩
      rw [hc, hσ x hx]
      exact o.indegree (x-u) ((hm x).mp hx) }
  exact ⟨t, fun _ _ => Iff.rfl, fun _ => rfl⟩

end ApollonianSuperharmonic

end
