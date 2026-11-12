/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure

-- [TABLET NODE: P4366T1AttachedRemainderIndexZero]

/-!
# P4366T1AttachedRemainderIndexZero

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4366T1AttachedRemainderIndexZero
    (T : ProtoTile) (F : Fin 3 → Bool → ProtoTile)
    (hF : ∀ i s, LatticeTile (F i s))
    (hinside : ∀ i s, (F i s).cells ⊆ T.cells)
    (hattach : ∀ i s, ∃ e : Finset GaussianInt,
      e ∈ BoundaryFootprintEdges (F i s) ∧ e ∈ BoundaryFootprintEdges T)
    (p : List GaussianInt) (x y : GaussianInt)
    (hhead : p.head? = some x) (hlast : p.getLast? = some y)
    (hnodup : p.Nodup) (hlen : 3 ≤ p.length)
    (hadj : ∀ a b, (a, b) ∈ p.zip p.tail → FourNeighborAdjacent a b)
    (hclose : FourNeighborAdjacent y x)
    (havoid : ∀ z ∈ p, z ∉ BoundaryFootprintVertices T)
    (hnoncross : let edges := (p.zip p.tail) ++ [(y, x)]
      ∀ i s z,
        ((z ∈ (F i s).cells ∧ z + 1 ∈ (F i s).cells) →
          (z + 1, z + 1 + ⟨0, 1⟩) ∉ edges ∧
            (z + 1 + ⟨0, 1⟩, z + 1) ∉ edges) ∧
        ((z ∈ (F i s).cells ∧ z + ⟨0, 1⟩ ∈ (F i s).cells) →
          (z + 1 + ⟨0, 1⟩, z + ⟨0, 1⟩) ∉ edges ∧
            (z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩) ∉ edges))
    (houtside : ∀ z : GaussianInt, z ∉ T.cells → GridRayCrossingIndex z p = 0) :
    ∀ i s z, z ∈ (F i s).cells → GridRayCrossingIndex z p = 0 := by
-- BODY
  classical
  let edges := (p.zip p.tail) ++ [(y, x)]
  let I := fun z => GridRayCrossingIndex z p
  have hchange := GridRayCrossingIndexAdjacentCell p x y hhead hlast hnodup hlen
    hadj hclose
  have hTne : T.cells.Nonempty := by
    obtain ⟨c, hc⟩ := (LatticeTileGridStructure (F 0 true) (hF 0 true)).1.1
    exact ⟨c, hinside 0 true hc⟩
  have cyclic_first (u v : GaussianInt) (huv : (u, v) ∈ edges) : u ∈ p := by
    simp only [edges, List.mem_append, List.mem_singleton] at huv
    rcases huv with huv | huv
    · exact (List.of_mem_zip huv).1
    · have hu : u = y := congrArg Prod.fst huv
      rw [hu]
      exact List.mem_of_getLast? hlast
  have boundary_absent (u v : GaussianInt)
      (he : ({u, v} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) :
      (u, v) ∉ edges ∧ (v, u) ∉ edges := by
    have hu : u ∈ BoundaryFootprintVertices T := by
      rw [BoundaryFootprintVertices, ite_eq_left hTne]
      exact ⟨{u, v}, he, by simp⟩
    have hv : v ∈ BoundaryFootprintVertices T := by
      rw [BoundaryFootprintVertices, ite_eq_left hTne]
      exact ⟨{u, v}, he, by simp⟩
    exact ⟨fun hm => havoid u (cyclic_first u v hm) hu,
      fun hm => havoid v (cyclic_first v u hm) hv⟩
  have horizontal_unique (a b : GaussianInt)
      (h : {a, a + 1} = ({b, b + 1} : Finset GaussianInt)) : a = b := by
    have ha : a ∈ ({b, b + 1} : Finset GaussianInt) := by rw [← h]; simp
    have ha1 : a + 1 ∈ ({b, b + 1} : Finset GaussianInt) := by rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ha1
    rcases ha with hab | hab <;> rcases ha1 with ha1b | ha1b
    · exact hab
    · exact hab
    · have h₁ := congrArg Zsqrtd.re hab
      have h₂ := congrArg Zsqrtd.re ha1b
      simp at h₁ h₂
      omega
    · have h₁ := congrArg Zsqrtd.re hab
      have h₂ := congrArg Zsqrtd.re ha1b
      simp at h₁ h₂
      omega
  have vertical_unique (a b : GaussianInt)
      (h : {a, a + ⟨0, 1⟩} = ({b, b + ⟨0, 1⟩} : Finset GaussianInt)) : a = b := by
    have ha : a ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← h]; simp
    have ha1 : a + ⟨0, 1⟩ ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ha1
    rcases ha with hab | hab <;> rcases ha1 with ha1b | ha1b
    · exact hab
    · exact hab
    · have h₁ := congrArg Zsqrtd.im hab
      have h₂ := congrArg Zsqrtd.im ha1b
      simp at h₁ h₂
      omega
    · have h₁ := congrArg Zsqrtd.im hab
      have h₂ := congrArg Zsqrtd.im ha1b
      simp at h₁ h₂
      omega
  have horizontal_vertical_ne (a b : GaussianInt) :
      ({a, a + 1} : Finset GaussianInt) ≠ {b, b + ⟨0, 1⟩} := by
    intro h
    have ha : a ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← h]; simp
    have ha1 : a + 1 ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ha1
    rcases ha with hab | hab <;> rcases ha1 with ha1b | ha1b
    all_goals
      have h₁ := congrArg Zsqrtd.re hab
      have h₂ := congrArg Zsqrtd.re ha1b
      simp at h₁ h₂
      omega
  have horizontal_boundary (z : GaussianInt)
      (he : ({z, z + 1} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) :
      (z ∈ T.cells ∧ z - ⟨0, 1⟩ ∉ T.cells) ∨
        (z ∉ T.cells ∧ z - ⟨0, 1⟩ ∈ T.cells) := by
    rcases he with ⟨a, ⟨heq, hocc⟩ | ⟨heq, hocc⟩⟩
    · simpa [horizontal_unique a z heq.symm] using hocc
    · exact (horizontal_vertical_ne z a heq).elim
  have vertical_boundary (z : GaussianInt)
      (he : ({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) :
      (z ∈ T.cells ∧ z - 1 ∉ T.cells) ∨
        (z ∉ T.cells ∧ z - 1 ∈ T.cells) := by
    rcases he with ⟨a, ⟨heq, hocc⟩ | ⟨heq, hocc⟩⟩
    · exact (horizontal_vertical_ne a z heq.symm).elim
    · simpa [vertical_unique a z heq.symm] using hocc
  have adjacent_equal (i : Fin 3) (s : Bool) (a b : GaussianInt)
      (ha : a ∈ (F i s).cells) (hb : b ∈ (F i s).cells)
      (hab : FourNeighborAdjacent a b) : I a = I b := by
    rcases hab with rfl | rfl | rfl | rfl
    · exact ((hchange a).1 ((hnoncross i s a).1 ⟨ha, hb⟩)).symm
    · have he : a - 1 + 1 = a := sub_add_cancel a 1
      have ha' : a - 1 + 1 ∈ (F i s).cells := by simpa only [he] using ha
      simpa only [I, he] using
        (hchange (a - 1)).1 ((hnoncross i s (a - 1)).1 ⟨hb, ha'⟩)
    · exact ((hchange a).2.2.1 ((hnoncross i s a).2 ⟨ha, hb⟩)).symm
    · have he : a - ⟨0, 1⟩ + ⟨0, 1⟩ = a := sub_add_cancel a _
      have ha' : a - ⟨0, 1⟩ + ⟨0, 1⟩ ∈ (F i s).cells := by
        simpa only [he] using ha
      simpa only [I, he] using
        (hchange (a - ⟨0, 1⟩)).2.2.1
          ((hnoncross i s (a - ⟨0, 1⟩)).2 ⟨hb, ha'⟩)
  intro i s c hc
  have hconst (a b : GaussianInt) (ha : a ∈ (F i s).cells)
      (hb : b ∈ (F i s).cells) : I a = I b := by
    obtain ⟨l, hlhead, hllast, hlmem, hlstep⟩ :=
      (LatticeTileGridStructure (F i s) (hF i s)).1.2 a ha b hb
    have along : ∀ (l : List GaussianInt) (a b : GaussianInt),
        l.head? = some a → l.getLast? = some b →
        (∀ z ∈ l, z ∈ (F i s).cells) →
        (∀ u v l₁ l₂, l = l₁ ++ u :: v :: l₂ → FourNeighborAdjacent u v) →
        I a = I b := by
      intro l
      induction l with
      | nil => intro a b hh; simp at hh
      | cons u l ih =>
          intro a b hh ht hm hs
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst a
          cases l with
          | nil => simpa using congrArg I (Option.some.inj ht)
          | cons v l =>
              have heq := adjacent_equal i s u v (hm u (by simp))
                (hm v (by simp)) (hs u v [] l rfl)
              apply heq.trans
              apply ih v b rfl (by simpa using ht)
              · intro z hz
                exact hm z (List.mem_cons_of_mem u hz)
              · intro r t l₁ l₂ he
                exact hs r t (u :: l₁) l₂ (by simpa using congrArg (u :: ·) he)
    exact along l a b hlhead hllast hlmem hlstep
  obtain ⟨e, heF, heT⟩ := hattach i s
  rcases heF with ⟨z, ⟨rfl, hocc⟩ | ⟨rfl, hocc⟩⟩
  · have hTocc := horizontal_boundary z heT
    have hfree := boundary_absent z (z + 1) heT
    have hindex : I z = I (z - ⟨0, 1⟩) := by
      have he₁ : z - ⟨0, 1⟩ + 1 + ⟨0, 1⟩ = z + 1 := by abel
      have he₂ : z - ⟨0, 1⟩ + ⟨0, 1⟩ = z := sub_add_cancel z _
      have hj := (hchange (z - ⟨0, 1⟩)).2.2.1
      simp only [he₁, he₂] at hj
      exact hj hfree.symm
    rcases hocc with ⟨hz, _⟩ | ⟨_, hz⟩
    · have hout : z - ⟨0, 1⟩ ∉ T.cells := by
        rcases hTocc with h | h
        · exact h.2
        · exact (h.1 (hinside i s hz)).elim
      exact (hconst c z hc hz).trans (hindex.trans (houtside _ hout))
    · have hout : z ∉ T.cells := by
        rcases hTocc with h | h
        · exact (h.2 (hinside i s hz)).elim
        · exact h.1
      exact (hconst c (z - ⟨0, 1⟩) hc hz).trans (hindex.symm.trans (houtside _ hout))
  · have hTocc := vertical_boundary z heT
    have hfree := boundary_absent z (z + ⟨0, 1⟩) heT
    have hindex : I z = I (z - 1) := by
      have he : z - 1 + 1 = z := sub_add_cancel z 1
      have hj := (hchange (z - 1)).1
      simp only [he] at hj
      exact hj hfree
    rcases hocc with ⟨hz, _⟩ | ⟨_, hz⟩
    · have hout : z - 1 ∉ T.cells := by
        rcases hTocc with h | h
        · exact h.2
        · exact (h.1 (hinside i s hz)).elim
      exact (hconst c z hc hz).trans (hindex.trans (houtside _ hout))
    · have hout : z ∉ T.cells := by
        rcases hTocc with h | h
        · exact (h.2 (hinside i s hz)).elim
        · exact h.1
      exact (hconst c (z - 1) hc hz).trans (hindex.symm.trans (houtside _ hout))

end ApollonianSuperharmonic

end
