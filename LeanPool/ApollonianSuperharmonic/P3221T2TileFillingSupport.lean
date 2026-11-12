/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.LatticeTileComplementGridConnected
public import Mathlib.Data.Finsupp.Basic

-- [TABLET NODE: P3221T2TileFillingSupport]

/-!
# P3221T2TileFillingSupport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3221T2TileFillingSupport (T : ProtoTile) (hT : LatticeTile T)
    (c : GaussianInt →₀ ℤ)
    (hH : ∀ x, ({x, x + 1} : Finset GaussianInt) ∉ FootprintEdges T →
      c x - c (x - ⟨0, 1⟩) = 0)
    (hV : ∀ x, ({x, x + ⟨0, 1⟩} : Finset GaussianInt) ∉ FootprintEdges T →
      c (x - 1) - c x = 0) :
    ∀ x, x ∉ T.cells → c x = 0 := by
-- BODY
  classical
  have horizontal_unique (a b : GaussianInt)
      (h : ({a, a + 1} : Finset GaussianInt) = {b, b + 1}) : a = b := by
    have ha : a = b ∨ a = b + 1 := by
      have : a ∈ ({b, b + 1} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    have ha1 : a + 1 = b ∨ a + 1 = b + 1 := by
      have : a + 1 ∈ ({b, b + 1} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    rcases ha with hab | hab
    · exact hab
    · have hr := congrArg Zsqrtd.re hab
      rcases ha1 with ha1 | ha1
      all_goals
        have hr1 := congrArg Zsqrtd.re ha1
        simp at hr hr1
        exfalso
        omega
  have vertical_unique (a b : GaussianInt)
      (h : ({a, a + ⟨0, 1⟩} : Finset GaussianInt) = {b, b + ⟨0, 1⟩}) : a = b := by
    have ha : a = b ∨ a = b + ⟨0, 1⟩ := by
      have : a ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    have hai : a + ⟨0, 1⟩ = b ∨ a + ⟨0, 1⟩ = b + ⟨0, 1⟩ := by
      have : a + ⟨0, 1⟩ ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by
        rw [← h]; simp
      simpa using this
    rcases ha with hab | hab
    · exact hab
    · have hi := congrArg Zsqrtd.im hab
      rcases hai with hai | hai
      all_goals
        have hi1 := congrArg Zsqrtd.im hai
        simp at hi hi1
        exfalso
        omega
  have horizontal_vertical_ne (a b : GaussianInt) :
      ({a, a + 1} : Finset GaussianInt) ≠ {b, b + ⟨0, 1⟩} := by
    intro h
    have ha : a = b ∨ a = b + ⟨0, 1⟩ := by
      have : a ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    have ha1 : a + 1 = b ∨ a + 1 = b + ⟨0, 1⟩ := by
      have : a + 1 ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    rcases ha with ha | ha <;> rcases ha1 with ha1 | ha1
    all_goals
      have hr := congrArg Zsqrtd.re ha
      have hr1 := congrArg Zsqrtd.re ha1
      simp at hr hr1
      omega
  have horizontal_missing (z : GaussianInt)
      (hz : z ∉ T.cells) (hzi : z - ⟨0, 1⟩ ∉ T.cells) :
      ({z, z + 1} : Finset GaussianInt) ∉ FootprintEdges T := by
    rintro ⟨w, hw, he | he | he | he⟩
    · exact hz (horizontal_unique z w he ▸ hw)
    · exact horizontal_vertical_ne z w he
    · exact horizontal_vertical_ne z (w + 1) he
    · have he' : ({z, z + 1} : Finset GaussianInt) = {w + ⟨0, 1⟩, w + ⟨0, 1⟩ + 1} := by
        simpa [add_assoc, add_comm, add_left_comm] using he
      have hzw := horizontal_unique z (w + ⟨0, 1⟩) he'
      apply hzi
      simpa [hzw] using hw
  have vertical_missing (z : GaussianInt)
      (hz : z ∉ T.cells) (hz1 : z - 1 ∉ T.cells) :
      ({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∉ FootprintEdges T := by
    rintro ⟨w, hw, he | he | he | he⟩
    · exact horizontal_vertical_ne w z he.symm
    · exact hz (vertical_unique z w he ▸ hw)
    · have hzw := vertical_unique z (w + 1) he
      apply hz1
      simpa [hzw] using hw
    · have he' : ({w + ⟨0, 1⟩, w + ⟨0, 1⟩ + 1} : Finset GaussianInt) = {z, z + ⟨0, 1⟩} := by
        simpa [add_assoc, add_comm, add_left_comm] using he.symm
      exact horizontal_vertical_ne (w + ⟨0, 1⟩) z he'
  have adjacent_equal (a b : GaussianInt) (ha : a ∉ T.cells)
      (hb : b ∉ T.cells) (hab : FourNeighborAdjacent a b) : c a = c b := by
    rcases hab with rfl | rfl | rfl | rfl
    · have hh := hV (a + 1)
        (vertical_missing (a + 1) hb (by simpa using ha))
      have hh' : c a - c (a + 1) = 0 := by simpa using hh
      omega
    · have hh := hV a (vertical_missing a ha hb)
      omega
    · have hh := hH (a + ⟨0, 1⟩)
        (horizontal_missing (a + ⟨0, 1⟩) hb (by simpa using ha))
      have hh' : c (a + ⟨0, 1⟩) - c a = 0 := by simpa using hh
      omega
    · have hh := hH a (horizontal_missing a ha hb)
      omega
  let s : Finset GaussianInt := insert 0 (T.cells ∪ c.support)
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s (fun z => z.re)
    (by simp [s])
  let b : GaussianInt := a + 1
  have hb : b ∉ s := by
    intro hb
    have hm := hmax b hb
    simp [b] at hm
  have hbT : b ∉ T.cells := by
    intro h
    apply hb
    simp [s, h]
  have hbc : c b = 0 := by
    by_contra h
    have hmem : b ∈ c.support := Finsupp.mem_support_iff.mpr h
    apply hb
    simp [s, hmem]
  have chain_const : ∀ (a : GaussianInt) (l : List GaussianInt),
      (∀ z ∈ a :: l, z ∉ T.cells) → List.IsChain FourNeighborAdjacent (a :: l) →
      ∀ z ∈ a :: l, c z = c a := by
    intro a l
    induction l generalizing a with
    | nil =>
        intro hout hchain z hz
        rcases List.mem_singleton.mp hz with rfl
        rfl
    | cons d l ih =>
        intro hout hchain z hz
        have had : FourNeighborAdjacent a d :=
          (List.isChain_cons.mp hchain).1 d (by simp)
        have heq := adjacent_equal a d (hout a (by simp)) (hout d (by simp)) had
        rcases List.mem_cons.mp hz with rfl | hz
        · rfl
        · exact (ih d (fun z hz => hout z (by simp [hz]))
            (List.isChain_cons.mp hchain).2 z hz).trans heq.symm
  intro x hx
  obtain ⟨p, hhead, hlast, hout, hadj⟩ :=
    (LatticeTileComplementGridConnected T hT).2 x hx b hbT
  have hchain : List.IsChain FourNeighborAdjacent p :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mpr hadj
  cases p with
  | nil => simp at hhead
  | cons a l =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst a
      have heq := chain_const x l hout hchain b
        (List.mem_of_mem_getLast? (by simp [hlast]))
      exact heq.symm.trans hbc

end ApollonianSuperharmonic

end
