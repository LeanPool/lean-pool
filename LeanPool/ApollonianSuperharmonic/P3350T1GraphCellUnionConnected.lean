/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.P3102T2CommonEdgeSectorTransition

-- [TABLET NODE: P3350T1GraphCellUnionConnected]

/-!
# P3350T1GraphCellUnionConnected

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3350T1GraphCellUnionConnected {ι : Type*}
    (adjacent : ι → ι → Prop) (hirrefl : ∀ a, ¬ adjacent a a)
    (tile : ι → ProtoTile) (S : Set ι) (hnonempty : S.Nonempty)
    (htile : ∀ a ∈ S, FourNeighborConnected ((tile a).cells : Set LatticeCell))
    (hdisjoint : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      Disjoint (tile a).cells (tile b).cells)
    (hedge : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → adjacent a b →
      (FootprintEdges (tile a) ∩ FootprintEdges (tile b)).Nonempty)
    (hconnected : ∀ a ∈ S, ∀ b ∈ S,
      ∃ p : List ι, p.head? = some a ∧ p.getLast? = some b ∧
        (∀ c ∈ p, c ∈ S) ∧
        ∀ c d : ι, ∀ l₁ l₂ : List ι,
          p = l₁ ++ c :: d :: l₂ → adjacent c d) :
    FourNeighborConnected {x : LatticeCell | ∃ a ∈ S, x ∈ (tile a).cells} := by
-- BODY
  classical
  let U : Set LatticeCell := {x | ∃ a ∈ S, x ∈ (tile a).cells}
  have edgeStep : ∀ a ∈ S, ∀ b ∈ S, adjacent a b →
      ∃ u ∈ (tile a).cells, ∃ v ∈ (tile b).cells, FourNeighborAdjacent u v := by
    intro a ha b hb hab
    have hne : a ≠ b := by
      intro heq
      subst b
      exact hirrefl a hab
    obtain ⟨e, hU, hV⟩ := hedge a ha b hb hne hab
    have hene : e.Nonempty := by
      obtain ⟨u, hu, h | h | h | h⟩ := hU
      all_goals rw [h]; simp
    obtain ⟨x, hx⟩ := hene
    obtain ⟨j, _, hsector⟩ := P3102T2CommonEdgeSectorTransition
      (tile a) (tile b) x e (hdisjoint a ha b hb hne) hx ⟨hU, hV⟩
    have hstep : ∀ j : Fin 4,
        FourNeighborAdjacent (LatticeVertexIncidentCell x j)
          (LatticeVertexIncidentCell x (j + 1)) := by
      intro j
      fin_cases j <;>
        simp [FourNeighborAdjacent, LatticeVertexIncidentCell, Zsqrtd.ext_iff]
    have hsymm : ∀ u v : LatticeCell,
        FourNeighborAdjacent u v → FourNeighborAdjacent v u := by
      intro u v h
      rcases h with h | h | h | h
      all_goals subst v
      all_goals simp [FourNeighborAdjacent, Zsqrtd.ext_iff]
    rcases hsector with hsector | hsector
    · exact ⟨_, hsector.1, _, hsector.2, hstep j⟩
    · exact ⟨_, hsector.2, _, hsector.1, hsymm _ _ (hstep j)⟩
  have walkJoin : ∀ (x y z : LatticeCell) (p q : List LatticeCell),
      p.head? = some x → p.getLast? = some y →
      q.head? = some y → q.getLast? = some z →
      (∀ w ∈ p, w ∈ U) → (∀ w ∈ q, w ∈ U) →
      (∀ a b : LatticeCell, ∀ l₁ l₂ : List LatticeCell,
        p = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b) →
      (∀ a b : LatticeCell, ∀ l₁ l₂ : List LatticeCell,
        q = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b) →
      ∃ r : List LatticeCell,
        r.head? = some x ∧ r.getLast? = some z ∧
        (∀ w ∈ r, w ∈ U) ∧
        (∀ a b : LatticeCell, ∀ l₁ l₂ : List LatticeCell,
          r = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b) := by
    intro x y z p q hp hy hq hz hps hqs hpp hqq
    have hcp : List.IsChain FourNeighborAdjacent p :=
      (List.isChain_iff_forall_rel_of_append_cons_cons).2 hpp
    have hcq : List.IsChain FourNeighborAdjacent q :=
      (List.isChain_iff_forall_rel_of_append_cons_cons).2 hqq
    have hcross : ∀ u ∈ p.getLast?, ∀ v ∈ q.tail.head?,
        FourNeighborAdjacent u v := by
      intro u hu v hv
      have hu' : u = y := by simpa [hy] using hu.symm
      cases q with
      | nil => simp at hq
      | cons qhead qrest =>
        cases qrest with
        | nil => simp at hv
        | cons qnext qmore =>
          have hv' := hcq.rel_head? hv
          have hqhead : qhead = y := by simpa using hq
          rw [hqhead] at hv'
          rw [hu']
          exact hv'
    refine ⟨p ++ q.tail, ?_, ?_, ?_, ?_⟩
    · have hpne : p ≠ [] := by
        intro h
        subst p
        simp at hp
      simpa [List.head?_append_of_ne_nil _ hpne] using hp
    · have hlast : (p ++ q.tail).getLast? = q.getLast? := by
        cases q with
        | nil => simp at hq
        | cons qhead qrest =>
          have hqhead : qhead = y := by simpa using hq
          cases qrest with
          | nil => simpa [hqhead] using hy
          | cons qtail qmore =>
            rw [List.getLast?_append_of_ne_nil _ (by simp)]
            exact (List.getLast?_append_of_ne_nil [qhead] (by simp)).symm
      exact hlast.trans hz
    · intro w hw
      simp only [List.mem_append] at hw
      rcases hw with hw | hw
      · exact hps w hw
      · exact hqs w (List.mem_of_mem_tail hw)
    · exact (List.isChain_iff_forall_rel_of_append_cons_cons).1
        (hcp.append hcq.tail hcross)
  have tileWalk : ∀ a ∈ S, ∀ x ∈ (tile a).cells, ∀ y ∈ (tile a).cells,
      ∃ p : List LatticeCell,
        p.head? = some x ∧ p.getLast? = some y ∧
        (∀ z ∈ p, z ∈ U) ∧
        (∀ u v : LatticeCell, ∀ l₁ l₂ : List LatticeCell,
          p = l₁ ++ u :: v :: l₂ → FourNeighborAdjacent u v) := by
    intro a ha x hx y hy
    obtain ⟨p, hp, hlast, hmem, hchain⟩ := (htile a ha).2 x hx y hy
    exact ⟨p, hp, hlast, fun z hz => ⟨a, ha, hmem z hz⟩, hchain⟩
  have assemble : ∀ (c d : ι) (r : List ι),
      r.head? = some c → r.getLast? = some d →
      (∀ a ∈ r, a ∈ S) →
      (∀ a b : ι, ∀ l₁ l₂ : List ι,
        r = l₁ ++ a :: b :: l₂ → adjacent a b) →
      ∀ x ∈ (tile c).cells, ∀ y ∈ (tile d).cells,
      ∃ p : List LatticeCell,
        p.head? = some x ∧ p.getLast? = some y ∧
        (∀ z ∈ p, z ∈ U) ∧
        (∀ u v : LatticeCell, ∀ l₁ l₂ : List LatticeCell,
          p = l₁ ++ u :: v :: l₂ → FourNeighborAdjacent u v) := by
    intro c d r
    induction r generalizing c d with
    | nil => simp
    | cons e r ih =>
      cases r with
      | nil =>
        intro hhead hlast hmem hchain x hx y hy
        have hec : e = c := by simpa using hhead
        have hed : e = d := by simpa using hlast
        subst c
        subst d
        exact tileWalk e (hmem e (by simp)) x hx y hy
      | cons f r =>
        intro hhead hlast hmem hchain x hx y hy
        have hec : e = c := by simpa using hhead
        have hfirst : adjacent e f := by
          apply hchain e f [] r
          simp
        have heS : e ∈ S := hmem e (by simp)
        have hfS : f ∈ S := hmem f (by simp)
        obtain ⟨u, hu, v, hv, huv⟩ := edgeStep e heS f hfS hfirst
        subst c
        obtain ⟨q₁, hq₁, hq₂, hq₃, hq₄⟩ := tileWalk e heS x hx u hu
        have huvU : ∀ w ∈ [u, v], w ∈ U := by
          intro w hw
          have hw' : w = u ∨ w = v := by simpa using hw
          rcases hw' with rfl | rfl
          · exact ⟨e, heS, hu⟩
          · exact ⟨f, hfS, hv⟩
        have huvEdges : ∀ (a b : LatticeCell) (l₁ l₂ : List LatticeCell),
            [u, v] = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b := by
          exact (List.isChain_iff_forall_rel_of_append_cons_cons).1
            ((List.isChain_pair).2 huv)
        have hmemRest : ∀ w ∈ f :: r, w ∈ S := by
          intro w hw
          exact hmem w (by simp [hw])
        have hchainRest : ∀ a b : ι, ∀ l₁ l₂ : List ι,
            f :: r = l₁ ++ a :: b :: l₂ → adjacent a b := by
          intro a b l₁ l₂ h
          apply hchain a b (e :: l₁) l₂
          simpa [List.cons_append, List.append_assoc] using h
        obtain ⟨q₂, hq₂₁, hq₂₂, hq₂₃, hq₂₄⟩ :=
          ih (c := f) (d := d) (by simp) hlast hmemRest hchainRest v hv y hy
        obtain ⟨qmid, hmid₁, hmid₂, hmid₃, hmid₄⟩ :=
          walkJoin x u v q₁ [u, v]
            hq₁ hq₂ (by simp) (by simp) hq₃ huvU hq₄ huvEdges
        exact walkJoin x v y qmid q₂
          hmid₁ hmid₂ hq₂₁ hq₂₂ hmid₃ hq₂₃ hmid₄ hq₂₄
  constructor
  · obtain ⟨a, ha⟩ := hnonempty
    obtain ⟨x, hx⟩ := (htile a ha).1
    exact ⟨x, a, ha, hx⟩
  · intro x hx y hy
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    obtain ⟨p, hphead, hplast, hpS, hpchain⟩ := hconnected a ha b hb
    exact assemble a b p hphead hplast hpS hpchain x hxa y hyb

end ApollonianSuperharmonic

end
