/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyStoredColorsCardinality

/-!
# Good Hierarchy Initial Pairs Non PE

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem GoodHierarchyInitialPairsNonPE {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (_ : ett.series.data.kind (Fin.last ett.rounds) ≠
      some TashkinovExtensionKind.PE)
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card) :
    ∃ gamma : Fin k → Finset (Fin k),
      (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt H 0 →
        (gamma eta).card = 2 ∧
          gamma eta ⊆ TreeMissingColors phi
            (ett.series.data.tree (Fin.last ett.rounds).castSucc)) ∧
      ∀ eta theta : Fin k,
        eta ∈ HierarchyStoredColorsAt H 0 →
        theta ∈ HierarchyStoredColorsAt H 0 → eta ≠ theta →
        Disjoint (gamma eta) (gamma theta) := by
  classical
  have pairing : ∀ (D M : Finset (Fin k)), 2 * D.card ≤ M.card →
      ∃ gamma : Fin k → Finset (Fin k),
        (∀ eta, eta ∈ D → (gamma eta).card = 2 ∧ gamma eta ⊆ M) ∧
        ∀ eta theta, eta ∈ D → theta ∈ D → eta ≠ theta →
          Disjoint (gamma eta) (gamma theta) := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
        intro M h
        refine ⟨fun _ => ∅, ?_, ?_⟩
        · simp
        · simp
    | @insert a D ha ih =>
        intro M h
        have hcard : (insert a D).card = D.card + 1 := by simp [ha]
        have hbig : 2 ≤ M.card := by
          rw [hcard] at h
          omega
        have hM : M.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨x, hx⟩ := hM
        have hrest : 1 ≤ (M.erase x).card := by
          rw [Finset.card_erase_of_mem hx]
          omega
        obtain ⟨y, hy⟩ := Finset.card_pos.mp hrest
        have hxy : x ≠ y := by
          intro hxy
          have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
          exact hyx hxy.symm
        have hrec : 2 * D.card ≤ ((M.erase x).erase y).card := by
          rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hx]
          omega
        obtain ⟨g, hg, hd⟩ := ih ((M.erase x).erase y) hrec
        refine ⟨fun z => if z = a then {x, y} else g z, ?_, ?_⟩
        · intro eta heta
          by_cases he : eta = a
          · subst eta
            constructor
            · simp [hxy]
            · have hpair : {x, y} ⊆ M := by
                intro z hz
                rcases Finset.mem_insert.mp hz with rfl | hz
                · exact hx
                · exact (Finset.mem_singleton.mp hz).symm ▸ Finset.mem_of_mem_erase hy
              simpa using hpair
          · have heta' : eta ∈ D := Finset.mem_insert.mp heta |>.resolve_left he
            have hz := hg eta heta'
            constructor
            · simpa [he] using hz.1
            · simpa [he] using hz.2.trans (by
                intro z hz'
                exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz'))
        · intro eta theta heta htheta hne
          by_cases he : eta = a
          · subst eta
            have ht : theta ∈ D := Finset.mem_insert.mp htheta |>.resolve_left (Ne.symm hne)
            have hsub := hg theta ht |>.2
            have htheta_ne : theta ≠ a := Ne.symm hne
            have hpair : Disjoint {x, y} (g theta) := by
              apply Finset.disjoint_left.2
              intro z hz hzg
              have hzg' := hsub (by simpa [htheta_ne] using hzg)
              rcases Finset.mem_insert.mp hz with rfl | hz
              · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hzg').2).1 rfl
              · exact (Finset.mem_erase.mp hzg').1 (Finset.mem_singleton.mp hz)
            simpa [htheta_ne] using hpair
          · by_cases ht : theta = a
            · subst theta
              have he' : eta ∈ D := Finset.mem_insert.mp heta |>.resolve_left he
              have hsub := hg eta he' |>.2
              have hpair : Disjoint (g eta) {x, y} := by
                apply Finset.disjoint_left.2
                intro z hzg hz
                have hzg' := hsub (by simpa [he] using hzg)
                rcases Finset.mem_insert.mp hz with rfl | hz
                · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hzg').2).1 rfl
                · exact (Finset.mem_erase.mp hzg').1 (Finset.mem_singleton.mp hz)
              simpa [he] using hpair
            · have he' : eta ∈ D := Finset.mem_insert.mp heta |>.resolve_left he
              have ht' : theta ∈ D := Finset.mem_insert.mp htheta |>.resolve_left ht
              simpa [he, ht] using hd eta theta he' ht' hne
  have hstored : 2 * (HierarchyStoredColorsAt H 0).card ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card := by
    have hc := HierarchyStoredColorsCardinality H 0
    omega
  obtain ⟨gamma, hgamma, hdisj⟩ :=
    pairing (HierarchyStoredColorsAt H 0)
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) hstored
  exact ⟨gamma, hgamma, hdisj⟩

end GoldbergSeymour

end
