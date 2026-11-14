/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyStoredColorsCardinality

public import LeanPool.GoldbergSeymour.TreeColorSetMinusClosed

/-!
# Good Hierarchy Initial Pairs PE

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem GoodHierarchyInitialPairsPE_hreserve_82.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
          E k}
      {T : TreeSequence G e0} {phi : PartialEdgeColoring E k} {ett : ExtendedTashkinovTree G k e0
          input T phi}
      {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base),
      let M := TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc);
      let C := M ∩ TreeMissingColors phi base.closure;
      (HierarchyStoredColorsAt H 0).card ≤ ett.rounds →
        2 * ett.rounds + 11 ≤ M.card →
          4 ≤ C.card → ∀ alpha ∉ C, ∀ (d : ℕ), 2 * d ≤ M.card - 11 → ∃ R ⊆ M.erase alpha, R.card
              = 2 * d ∧ 4 ≤ (C \ R).card := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H M C hD hM hC alpha halphaC d hd
  have hsubC0 : C ⊆ M := Finset.inter_subset_left
  have hsubC : C ⊆ M.erase alpha := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨by
      intro he
      exact halphaC (he ▸ hx), hsubC0 hx⟩
  have hA : 2 * d + 10 ≤ (M.erase alpha).card := by
    by_cases ham : alpha ∈ M
    · rw [Finset.card_erase_of_mem ham]
      omega
    · simp [ham]
      omega
  by_cases houtside : 2 * d ≤ (M.erase alpha \ C).card
  · obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq houtside
    refine ⟨R, ?_, hRcard, ?_⟩
    · intro x hx
      have hxA := (Finset.mem_sdiff.mp (hRsub hx)).1
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hxA).1,
        (Finset.mem_erase.mp hxA).2⟩
    have hdis : Disjoint C R := Finset.disjoint_left.mpr (by
      intro x hxC hxR
      exact (Finset.mem_sdiff.mp (hRsub hxR)).2 hxC)
    have heq : C \ R = C := by
      apply Finset.ext
      intro x
      constructor
      · exact fun hx => (Finset.mem_sdiff.mp hx).1
      · intro hx
        exact Finset.mem_sdiff.mpr ⟨hx, by
          intro hxr
          exact (Finset.mem_sdiff.mp (hRsub hxr)).2 hx⟩
    rw [heq]
    exact hC
  · have hlt : (M.erase alpha \ C).card < 2 * d := Nat.lt_of_not_ge houtside
    have hdiff : (M.erase alpha \ C).card + C.card = (M.erase alpha).card := by
      have hu := Finset.union_sdiff_of_subset hsubC
      have hc := congrArg Finset.card hu
      rw [Finset.card_union_of_disjoint Finset.disjoint_sdiff] at hc
      omega
    have hq : 2 * d - (M.erase alpha \ C).card ≤ C.card := by omega
    obtain ⟨Q, hQsub, hQcard⟩ := Finset.exists_subset_card_eq hq
    let R := (M.erase alpha \ C) ∪ Q
    have hRsub : R ⊆ M.erase alpha := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_sdiff.mp hx |>.1
      · exact hsubC (hQsub hx)
    have hRcard : R.card = 2 * d := by
      dsimp [R]
      rw [Finset.card_union_of_disjoint (by
        apply Finset.disjoint_left.mpr
        intro x hxO hxQ
        exact (Finset.mem_sdiff.mp hxO).2 (hQsub hxQ))]
      omega
    have hRQ : C \ R = C \ Q := by
      dsimp [R]
      apply Finset.ext
      intro x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxC, hxnot⟩
        refine ⟨hxC, ?_⟩
        intro hxQ
        exact hxnot (Or.inr hxQ)
      · rintro ⟨hxC, hxnot⟩
        refine ⟨hxC, ?_⟩
        intro hxR
        rcases hxR with hxO | hxQ
        · exact hxO.2 hxC
        · exact hxnot hxQ
    refine ⟨R, hRsub, hRcard, ?_⟩
    rw [hRQ, Finset.card_sdiff_of_subset hQsub]
    omega

private theorem GoodHierarchyInitialPairsPE_pairing_163.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] {G
    : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k} {T :
    TreeSequence G e0} {phi : PartialEdgeColoring E k} {ett : ExtendedTashkinovTree G k e0
    input T phi} {base : HierarchyBase ett phi} (_ : TashkinovHierarchy ett base) (_ D X :
    Finset (Fin k)), 2 * D.card ≤ X.card → ∃ (gamma : Fin k → Finset (Fin k)), (∀ eta ∈ D,
    (gamma eta).card = 2 ∧ gamma eta ⊆ X) ∧ ∀ (eta theta : Fin k), eta ∈ D → theta ∈ D → eta ≠
    theta → Disjoint (gamma eta) (gamma theta) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H R D
  induction D using Finset.induction_on with
  | empty =>
      intro X hx
      exact ⟨fun _ => ∅, by simp, by simp⟩
  | @insert a D ha ih =>
      intro X hx
      have htwo : 2 ≤ X.card := by
        have hc : (insert a D).card = D.card + 1 := by simp [ha]
        rw [hc] at hx
        omega
      obtain ⟨x, hxX⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
      have hrest : 1 ≤ (X.erase x).card := by
        rw [Finset.card_erase_of_mem hxX]
        omega
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hrest
      have hxy : x ≠ y := by
        intro e
        exact (Finset.mem_erase.mp hy).1 e.symm
      have hrec : 2 * D.card ≤ ((X.erase x).erase y).card := by
        have hxcard : 2 * (D.card + 1) ≤ X.card := by
          simpa [ha] using hx
        rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hxX]
        omega
      obtain ⟨g, hg, hgd⟩ := ih ((X.erase x).erase y) hrec
      refine ⟨fun z => if z = a then {x, y} else g z, ?_, ?_⟩
      · intro eta heta
        by_cases he : eta = a
        · subst eta
          refine ⟨by simp [hxy], ?_⟩
          simp only []
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hxX
          · have hz' : z = y := Finset.mem_singleton.mp hz
            subst z
            exact Finset.mem_of_mem_erase hy
        · have heD : eta ∈ D := Finset.mem_insert.mp heta |>.resolve_left he
          simp only [ite_eq_right he]
          exact ⟨(hg eta heD).1, ((hg eta heD).2.trans
            (Finset.erase_subset _ _)).trans (Finset.erase_subset _ _)⟩
      · intro eta theta heta htheta hne
        by_cases he : eta = a
        · subst eta
          have ht : theta ∈ D := Finset.mem_insert.mp htheta |>.resolve_left (Ne.symm hne)
          have hs := (hg theta ht).2
          simp only [ite_eq_right (Ne.symm hne)]
          apply Finset.disjoint_left.mpr
          intro z hz hzG
          have hz' := hs (by simpa [Ne.symm hne] using hzG)
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hz').2).1 rfl
          · exact (Finset.mem_erase.mp hz').1 (Finset.mem_singleton.mp hz)
        · by_cases ht : theta = a
          · subst theta
            have heD : eta ∈ D := Finset.mem_insert.mp heta |>.resolve_left he
            have hs := (hg eta heD).2
            simp only [ite_eq_right he]
            apply Finset.disjoint_left.mpr
            intro z hzG hz
            have hz' := hs hzG
            rcases Finset.mem_insert.mp hz with rfl | hz
            · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hz').2).1 rfl
            · exact (Finset.mem_erase.mp hz').1 (Finset.mem_singleton.mp hz)
          · simpa [he, ht] using hgd eta theta
              (Finset.mem_insert.mp heta |>.resolve_left he)
              (Finset.mem_insert.mp htheta |>.resolve_left ht) hne

theorem GoodHierarchyInitialPairsPE {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (_ : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (hnotClosed : ∃ alpha : Fin k,
      alpha ∈ TreeMissingColors phi base.core ∧
        ¬ TreeColorSetClosed G phi base.core {alpha})
    (hcommonClosed : TreeColorSetClosed G phi base.core
      (TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
        TreeMissingColors phi base.closure))
    (hcommonFour : 4 ≤
      (TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
        TreeMissingColors phi base.closure).card) :
    ∃ gamma : Fin k → Finset (Fin k),
      (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt H 0 →
        (gamma eta).card = 2 ∧
          gamma eta ⊆ TreeMissingColors phi
            (ett.series.data.tree (Fin.last ett.rounds).castSucc)) ∧
      (∀ eta theta : Fin k,
        eta ∈ HierarchyStoredColorsAt H 0 →
        theta ∈ HierarchyStoredColorsAt H 0 → eta ≠ theta →
        Disjoint (gamma eta) (gamma theta)) ∧
      ¬ TreeColorSetMinusClosed G phi base.core
        ((HierarchyStoredColorsAt H 0).biUnion gamma) ∧
      4 ≤ ((TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
        TreeMissingColors phi base.closure) \
          (HierarchyStoredColorsAt H 0).biUnion gamma).card := by
  classical
  let M := TreeMissingColors phi
    (ett.series.data.tree (Fin.last ett.rounds).castSucc)
  let C := M ∩ TreeMissingColors phi base.closure
  have hD : (HierarchyStoredColorsAt H 0).card ≤ ett.rounds :=
    HierarchyStoredColorsCardinality H 0
  have hM : 2 * ett.rounds + 11 ≤ M.card := by simpa [M] using hlarge
  have hC : 4 ≤ C.card := by simpa [C] using hcommonFour
  obtain ⟨alpha, halpha, hna⟩ := hnotClosed
  have halphaC : alpha ∉ C := by
    intro hac
    have hh := hcommonClosed alpha (by simpa [C] using hac)
    exact hna (by
      unfold TreeColorSetClosed
      intro beta hbeta
      have : beta = alpha := Finset.mem_singleton.mp hbeta
      subst beta
      exact hh)
  have hreserve : ∀ (d : ℕ), 2 * d ≤ M.card - 11 →
      ∃ R : Finset (Fin k), R ⊆ M.erase alpha ∧ R.card = 2 * d ∧
        4 ≤ (C \ R).card := by
    exact @GoodHierarchyInitialPairsPE_hreserve_82 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 input T phi ett base H hD hM hC alpha halphaC
  have hdM : 2 * (HierarchyStoredColorsAt H 0).card ≤ M.card - 11 := by
    omega
  obtain ⟨R, hRsub, hRcard, hCR⟩ := hreserve
    (HierarchyStoredColorsAt H 0).card hdM
  have pairing : ∀ (D X : Finset (Fin k)), 2 * D.card ≤ X.card →
      ∃ gamma : Fin k → Finset (Fin k),
        (∀ eta, eta ∈ D → (gamma eta).card = 2 ∧ gamma eta ⊆ X) ∧
        ∀ eta theta, eta ∈ D → theta ∈ D → eta ≠ theta →
          Disjoint (gamma eta) (gamma theta) := by
    exact @GoodHierarchyInitialPairsPE_pairing_163 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 input T phi ett base H R
  obtain ⟨gamma, hg, hgd⟩ := pairing (HierarchyStoredColorsAt H 0) R
    (by simp [hRcard])
  refine ⟨gamma, ?_, hgd, ?_, ?_⟩
  · intro eta heta
    exact ⟨(hg eta heta).1, (hg eta heta).2.trans
      (hRsub.trans (Finset.erase_subset _ _))⟩
  · intro hclosed
    apply hna
    unfold TreeColorSetClosed
    unfold TreeColorSetMinusClosed at hclosed
    intro beta hbeta
    have hba : beta = alpha := Finset.mem_singleton.mp hbeta
    subst beta
    exact hclosed alpha (by
      apply Finset.mem_sdiff.mpr
      refine ⟨halpha, ?_⟩
      intro haU
      simp only [Finset.mem_biUnion] at haU
      obtain ⟨eta, heta, hame⟩ := haU
      have := (hg eta heta).2 hame
      exact (Finset.mem_erase.mp (hRsub this)).1 rfl)
  · have hU : (HierarchyStoredColorsAt H 0).biUnion gamma ⊆ R := by
      intro x hx
      obtain ⟨eta, heta, hxe⟩ := Finset.mem_biUnion.mp hx
      exact (hg eta heta).2 hxe
    have hsub : C \ R ⊆ C \ (HierarchyStoredColorsAt H 0).biUnion gamma :=
      Finset.sdiff_subset_sdiff_right C hU
    exact hCR.trans (Finset.card_le_card hsub)

end GoldbergSeymour

end
